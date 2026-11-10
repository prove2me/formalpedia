-- Prove2me | Definitions.Def_GeoLipLearn_Agnostic_Learner
-- name    : GeoLipLearn_Agnostic_Learner
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:52:50.078661+00:00
-- url     : https://prove2.me/theorems/4f9f29b5-5476-4b88-8878-0dba29009031
-- title:
--   Uniform learner and finite correction contracts with all resource bounds
-- statement:
--   Training runs on the labelled and Gaussian streams, starting from the fixed input layout. Evaluation receives only a real representation block and a query $x$: the representation starts at address zero, $x_i$ occupies address $-1-i$, pointer 0 contains $d$ and pointer 1 the representation length. Its output register defines the returned hypothesis. The observation horizon is the ceiling of the real resource budget; this ceiling is a mathematical observer, not a machine instruction.
--
--   The formula budget demands, for every stream, halting training with work, example count and representation length at most the budget, nonnegative output length, and halting evaluation on every query within the same work budget. For learning the budget is
--   $$(d+1)^{C(V/\varepsilon)^C}(\log(2/\delta))^3.$$
--   The training inputs are $[\varepsilon,\delta,V]$. The measurable success event requires global 1-Lipschitzness and risk at most $\operatorname{opt}_1+\varepsilon$. In the bounded-label version every returned function also has range in $[-V,V]$ on every stream.
--
--   For correction, inputs are $[B,\tau,\xi]$ followed by the polynomial coefficients, with $k$ in pointer 3; its budget is $(d+1)^{C((k+1)/\tau)^C}\,CB^C(\log(2/\xi))^3$. Every output has range $[-B,B]$, and on a measurable Gaussian-stream event it is globally 1-Lipschitz and within $\tau$ of $C_B(p)$ in Gaussian $L^1$.
--
--   For polynomial learning, inputs are $[B,\eta,\alpha,\zeta]$ with the loss exponent in pointer 3. The output is the full monomial coefficient block for degree bound $k$ from (25) at half accuracy and defect parameters. Samples and work are bounded on every stream by $C(1+B+\eta^{-1}+\alpha^{-1}+k+D+9^k)^C(\log(2/\zeta))^2$, where $D=\binom{d+k}{k}$. On one measurable success event the decoded polynomial has the required risk, defect and norm bounds. The definitions impose no implementation as a premise: existence of admissible programs is asserted by the theorem items.
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), p.16, Proposition 4.3; p.41, Proposition A.6; pp.34–36, Proposition 9.2; pp.48–49, Theorems C.1–C.2

import Definitions.Def_GeoLipLearn_Agnostic_Machine
import Definitions.Def_GeoLipLearn_Agnostic_Hermite

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

/-- The ceiling is only the observer's finite run horizon, never an instruction. -/
noncomputable def train (P : Program) (d discrete : ℕ) (input : List ℝ)
    (R : ℝ) (ω : Streams d) : State := run P d ω (initial d discrete input) ⌈R⌉₊
/-- Evaluation sees only the representation and the query: x occupies negative memory,
representation starts at 0, pointer 1 contains its length. -/
noncomputable def evaluationInitial {d : ℕ} (a : List ℝ) (x : Space d) : State :=
  { initial d 0 a with cfg :=
    { (initial d 0 a).cfg with
      ptrs := fun j => if j=0 then (d : ℤ) else if j=1 then (a.length : ℤ) else 0,
      mem := fun j => if h : j < 0 ∧ -j-1 < (d : ℤ) then
        x ⟨(-j-1).toNat, by omega⟩ else if 0 ≤ j then a[j.toNat]! else 0 } }
noncomputable def evaluate {d : ℕ} (E : Program) (R : ℝ) (a : List ℝ) (x : Space d) : State :=
  run E d (fun _ => (0,0), fun _ => 0) (evaluationInitial a x) ⌈R⌉₊
noncomputable def hypothesis {d : ℕ} (E : Program) (R : ℝ) (a : List ℝ) : Space d → ℝ :=
  fun x => (evaluate E R a x).output
noncomputable def TrainingBudget (S : State) (R : ℝ) : Prop :=
  S.halted = true ∧ (S.work : ℝ) ≤ R ∧ (S.examples : ℝ) ≤ R ∧
    0 ≤ S.cfg.ptrs 1 ∧ ((representation S).length : ℝ) ≤ R
noncomputable def FormulaBudget (E : Program) (d discrete : ℕ) (input : List ℝ)
    (P : Program) (R : ℝ) : Prop :=
  ∀ ω : Streams d,
    let S := train P d discrete input R ω
    TrainingBudget S R ∧ ∀ x : Space d,
      (evaluate E R (representation S) x).halted = true ∧
      ((evaluate E R (representation S) x).work : ℝ) ≤ R
noncomputable def learningBound (C d : ℕ) (V ε δ : ℝ) : ℝ :=
  (d+1 : ℝ) ^ ((C : ℝ) * (V/ε)^C) * (Real.log (2/δ))^3
noncomputable def Learns (P E : Program) (C d : ℕ) (V ε δ : ℝ)
    (D : Measure (Space d × ℝ)) (bounded : Bool) : Prop :=
  let R := learningBound C d V ε δ
  FormulaBudget E d 0 [ε,δ,V] P R ∧
  (bounded = true → ∀ ω : Streams d,
    InRange V (hypothesis (d := d) E R (representation (train P d 0 [ε,δ,V] R ω)))) ∧
  HighProbability (streamLaw D) δ (fun ω =>
    let H := hypothesis (d := d) E R (representation (train P d 0 [ε,δ,V] R ω))
    LipschitzWith 1 H ∧ err 1 D H ≤ opt 1 D + ENNReal.ofReal ε)
noncomputable def correctionBound (C d k : ℕ) (B τ ξ : ℝ) : ℝ :=
  (d+1 : ℝ)^((C : ℝ)*((k+1 : ℝ)/τ)^C) * ((C : ℝ)*B^C) * (Real.log (2/ξ))^3
noncomputable def Corrects (P E : Program) (C d k : ℕ) (B τ ξ : ℝ) (p : Poly d) : Prop :=
  let R := correctionBound C d k B τ ξ
  let input := [B,τ,ξ] ++ coefficients k p
  FormulaBudget E d k input P R ∧
  (∀ ω : Streams d, InRange B (hypothesis (d := d) E R (representation (train P d k input R ω)))) ∧
  HighProbability gaussianStreamLaw ξ (fun ω =>
    let H := hypothesis (d := d) E R (representation (train P d k input R (fun _ => (0,0), ω)))
    LipschitzWith 1 H ∧ normG 1 (fun x => H x - clip B (evalPoly p x)) ≤ ENNReal.ofReal τ)
noncomputable def polynomialBound (C d k : ℕ) (B η α ζ : ℝ) : ℝ :=
  (C : ℝ) * (1+B+η⁻¹+α⁻¹+(k : ℝ)+(Nat.choose (d+k) k : ℝ)+(9 : ℝ)^k)^C *
    (Real.log (2/ζ))^2
noncomputable def PolynomialLearns (P : Program) (C d ell : ℕ) (B η α ζ : ℝ)
    (D : Measure (Space d × ℝ)) : Prop :=
  let k := degree25 B (η/2) (α/2)
  let R := polynomialBound C d k B η α ζ
  (∀ ω : Streams d,
    let S := train P d ell [B,η,α,ζ] R ω
    S.halted = true ∧ (S.work : ℝ) ≤ R ∧ (S.examples : ℝ) ≤ R ∧
      S.cfg.ptrs 1 = ((exponents d k).length : ℤ)) ∧
  HighProbability (streamLaw D) ζ (fun ω =>
    let p := coefficientFunction d k (representation (train P d ell [B,η,α,ζ] R ω))
    err ell D p ≤ opt ell D + ENNReal.ofReal η ∧
    defect p ≤ α^2 ∧ normG 2 p ≤ ENNReal.ofReal B)

end GeoLipLearn.Agnostic


