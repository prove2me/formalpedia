-- Prove2me | Definitions.Def_OnlineUBSR_Supplement_Model
-- name    : OnlineUBSR_Supplement_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:35:36.960419+00:00
-- url     : https://prove2.me/theorems/4090d2fa-2826-42ed-a507-986c1247220b
-- title:
--   Parameterized UBSR samples, derivative estimator, and SGD recursions
-- statement:
--   This module defines the parameterized family $\xi(\theta)=-X(\theta)$ used in Section 5, the objective $h(\theta)=SR_\lambda(X(\theta))$, the independent-double-sampling derivative estimator $h'_m=A_m/B_m$ of (12), and the unprojected and projected stochastic-gradient recursions (10) and (18). It also records the paper's assumptions and the explicit constants $K_1,C_4,C_5,B_1,L_4$, plus the phase schedule (19).
--
--   The data are total in $\theta$, while assumptions are imposed on the printed parameter interval. Positive sample indices are used and index zero is unread. This module reuses the base mission's definitions of UBSR, projection, the projected estimator, its noise, and its iterate filtration.
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Algorithm 1 and (10)–(14), pp.8–10; (18)–(20), p.12

import Mathlib
import Definitions.Def_OnlineUBSR_gFun
import Definitions.Def_OnlineUBSR_ubsr
import Definitions.Def_OnlineUBSR_proj
import Definitions.Def_OnlineUBSR_iterate
import Definitions.Def_OnlineUBSR_noise
import Definitions.Def_OnlineUBSR_iterSigma

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped Topology

namespace OnlineUBSR.Supplement

/-- Corrected Assumption 4 for an arbitrary step sequence in the base projected estimator.
It includes index zero, uses the fresh sample `ξ_{n+1}`, and conditions on the sigma-field of
the iterates. -/
def EstimationNoiseBound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ℓ : ℝ → ℝ) (lam tl tu t₀ σ : ℝ) (X : Ω → ℝ) (a : ℕ → ℝ)
    (ξ : ℕ → Ω → ℝ) : Prop :=
  ∀ n : ℕ,
    μ[fun ω => OnlineUBSR.noise μ ℓ lam X (OnlineUBSR.iterate ℓ lam tl tu t₀ a ξ) ξ n ω ^ 2 |
      OnlineUBSR.iterSigma (OnlineUBSR.iterate ℓ lam tl tu t₀ a ξ) n] ≤ᵐ[μ] fun _ => σ ^ 2

/-- The parameterized loss family used in Section 5 of Hegde--Menon--Prashanth--Jagannathan,
arXiv:2111.08805v3, pp.7--12.  `F θ u` is the paper's sample `ξ(θ)=-X(θ)` when
`u` has law `ν`.  The remaining fields are exactly the constants occurring in Assumptions
1--9 and in (13), together with the initial value and `c/k` step size of the inner UBSR
estimator.

**Formalization Note.** Conditions on this data are kept in the predicates below so that the
same model can be used under Assumption 10 or Assumption 11.  The map is total on `ℝ`, while
all hypotheses are imposed only on `[θl, θu]`, as in the paper. -/
structure Model (E : Type*) [MeasurableSpace E] where
  ν : Measure E
  ℓ : ℝ → ℝ
  lam : ℝ
  tl : ℝ
  tu : ℝ
  t₀ : ℝ
  c : ℝ
  M₀ : ℝ
  μ₁ : ℝ
  L₁ : ℝ
  σ : ℝ
  θl : ℝ
  θu : ℝ
  η : ℝ
  L₂ : ℝ
  zeta : ℝ
  zetaTilde : ℝ
  M₂ : ℝ
  β₁ : ℝ
  F : ℝ → E → ℝ

/-- The shortfall-risk objective `h(θ)=SR_λ(X(θ))`, with `X(θ)=-F(θ,·)` (p.7, (9)). -/
noncomputable def objective {E : Type*} [MeasurableSpace E] (M : Model E) (θ : ℝ) : ℝ :=
  OnlineUBSR.ubsr M.ν M.ℓ M.lam (fun u => -M.F θ u)

/-- The `m`-step inner UBSR estimate formed from the independent tilde batch (Algorithm 1,
pp.8--9). Samples and step sizes are indexed from one; index zero is unread. -/
noncomputable def innerEstimate {Ω E : Type*} [MeasurableSpace E] (M : Model E)
    (S : Bool → ℕ → ℕ → Ω → E) (outer m : ℕ) (θ : ℝ) : Ω → ℝ :=
  OnlineUBSR.iterate M.ℓ M.lam M.tl M.tu M.t₀ (fun k : ℕ => M.c / (k : ℝ))
    (fun i ω => M.F θ (S true outer i ω)) m

/-- The double-sample derivative estimator `h'_m=A_m/B_m` of (12), pp.8--9.  `false`
selects the batch used in `A_m,B_m`; `true` selects the independent batch used for the inner
estimate. Lean's total division is used literally, so the value is zero when `B_m=0`. -/
noncomputable def derivativeEstimator {Ω E : Type*} [MeasurableSpace E] (M : Model E)
    (S : Bool → ℕ → ℕ → Ω → E) (outer m : ℕ) (θ : ℝ) (ω : Ω) : ℝ :=
  let tm := innerEstimate M S outer m θ ω
  let A := (1 / (m : ℝ)) * ∑ i ∈ range m,
    deriv M.ℓ (M.F θ (S false outer (i + 1) ω) - tm) *
      deriv (fun q => M.F q (S false outer (i + 1) ω)) θ
  let B := (1 / (m : ℝ)) * ∑ i ∈ range m,
    deriv M.ℓ (M.F θ (S false outer (i + 1) ω) - tm)
  A / B

/-- The unprojected recursion used in the proof of Theorem 5: `θ_k=θ_{k-1}-(b/k)h'_m(θ_{k-1})`,
starting from `θ₀`.  This follows the proof's indexing on p.27; `b/0` is never read. -/
noncomputable def unprojectedSGD {Ω E : Type*} [MeasurableSpace E] (M : Model E)
    (S : Bool → ℕ → ℕ → Ω → E) (θ₀ b : ℝ) (m : ℕ) : ℕ → Ω → ℝ
  | 0 => fun _ => θ₀
  | k + 1 => fun ω =>
      unprojectedSGD M S θ₀ b m k ω - b / (k + 1 : ℝ) *
        derivativeEstimator M S (k + 1) m (unprojectedSGD M S θ₀ b m k ω) ω

/-- The projected recursion (18), indexed as in Theorem 6: `θ₁` is initial and the update with
index `k≥1` produces `θ_{k+1}`.  The value at index zero is an unread copy of `θ₁`. -/
noncomputable def projectedSGD {Ω E : Type*} [MeasurableSpace E] (M : Model E)
    (S : Bool → ℕ → ℕ → Ω → E) (θ₁ : ℝ) (b : ℕ → ℝ) (m : ℕ → ℕ) : ℕ → Ω → ℝ
  | 0 => fun _ => θ₁
  | 1 => fun _ => θ₁
  | k + 2 => fun ω => OnlineUBSR.proj M.θl M.θu
      (projectedSGD M S θ₁ b m (k + 1) ω - b (k + 1) *
        derivativeEstimator M S (k + 1) (m (k + 1))
          (projectedSGD M S θ₁ b m (k + 1) ω) ω)

/-- All samples in all outer batches are mutually independent and have the model law `ν`.
Only positive sample indices occur, matching Algorithm 1. -/
def IsSampleBank {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (M : Model E) (S : Bool → ℕ → ℕ → Ω → E) : Prop :=
  (∀ side outer i, Measurable (S side outer (i + 1))) ∧
  iIndepFun (fun q : Bool × ℕ × ℕ => S q.1 q.2.1 (q.2.2 + 1)) μ ∧
  (∀ side outer i, IdentDistrib (S side outer (i + 1)) id μ M.ν)

/-- Corrected Assumptions 1--3, uniformly in the parameter.  The derivative bound is on `g'`,
the quantity used by the proofs, rather than the paper's erroneous `-ℓ'(-t)`. -/
def Assumptions1To3 {E : Type*} [MeasurableSpace E] (M : Model E) : Prop :=
  0 < M.θl ∧ M.θl < M.θu ∧ M.tl < M.tu ∧
  ConvexOn ℝ Set.univ M.ℓ ∧ Differentiable ℝ M.ℓ ∧
  0 < M.M₀ ∧ 0 < M.μ₁ ∧ 0 < M.L₁ ∧
  ∀ θ ∈ Set.Icc M.θl M.θu,
    Measurable (M.F θ) ∧
    (∀ᵐ u ∂M.ν, |M.F θ u| ≤ M.M₀) ∧
    0 < OnlineUBSR.gFun M.ν M.ℓ M.lam (fun u => -M.F θ u) M.tl ∧
    OnlineUBSR.gFun M.ν M.ℓ M.lam (fun u => -M.F θ u) M.tu < 0 ∧
    (∀ t ∈ Set.Icc M.tl M.tu,
      -M.L₁ ≤ deriv (OnlineUBSR.gFun M.ν M.ℓ M.lam (fun u => -M.F θ u)) t ∧
      deriv (OnlineUBSR.gFun M.ν M.ℓ M.lam (fun u => -M.F θ u)) t ≤ -M.μ₁)

/-- Assumption 4 for the inner estimator at parameter `θ` and outer batch `outer`, corrected to
include noise index zero. -/
def InnerNoiseBound {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (M : Model E) (S : Bool → ℕ → ℕ → Ω → E) (outer : ℕ) (θ : ℝ) : Prop :=
  0 < M.σ ∧ M.t₀ ∈ Set.Icc M.tl M.tu ∧ 1 / 2 < M.μ₁ * M.c ∧
  ∀ n : ℕ,
    μ[fun ω : Ω => (M.ℓ (M.F θ (S true outer (n + 1) ω) -
          OnlineUBSR.iterate M.ℓ M.lam M.tl M.tu M.t₀ (fun k : ℕ => M.c / (k : ℝ))
            (fun i ω => M.F θ (S true outer i ω)) n ω) - M.lam -
        OnlineUBSR.gFun M.ν M.ℓ M.lam (fun u => -M.F θ u)
          (OnlineUBSR.iterate M.ℓ M.lam M.tl M.tu M.t₀ (fun k : ℕ => M.c / (k : ℝ))
            (fun i ω => M.F θ (S true outer i ω)) n ω)) ^ 2 |
      OnlineUBSR.iterSigma
        (OnlineUBSR.iterate M.ℓ M.lam M.tl M.tu M.t₀ (fun k : ℕ => M.c / (k : ℝ))
          (fun i ω => M.F θ (S true outer i ω))) n] ≤ᵐ[μ] fun _ => M.σ ^ 2

/-- Assumptions 5--9 and (13), with their printed quantifiers (pp.8--9): `ς, ς̃ > 0` as in
Assumption 8, and Assumptions 7 and 9 hold almost surely simultaneously for every parameter
(and every `t ∈ [tl, tu]`).  The pathwise derivatives of `F` are Mathlib's two-sided
derivatives. -/
def Assumptions5To9 {E : Type*} [MeasurableSpace E] (M : Model E) : Prop :=
  0 < M.η ∧ 0 < M.L₂ ∧ 0 < M.zeta ∧ 0 < M.zetaTilde ∧ 0 < M.M₂ ∧ 0 < M.β₁ ∧
  (∀ x, DifferentiableAt ℝ M.ℓ x ∧ DifferentiableAt ℝ (deriv M.ℓ) x) ∧
  -- Assumption 7, with its printed quantifier order: w.p. 1, for all `(θ, t)` in the rectangle.
  (∀ᵐ u ∂M.ν, ∀ θ ∈ Set.Icc M.θl M.θu, ∀ t ∈ Set.Icc M.tl M.tu,
    |deriv (deriv M.ℓ) (M.F θ u - t)| ≤ M.L₂) ∧
  -- Assumption 9: `sup_{θ ∈ [θl, θu]} |ξ'(θ)| ≤ M₂`, pathwise (almost surely).
  (∀ᵐ u ∂M.ν, ∀ θ ∈ Set.Icc M.θl M.θu, |deriv (fun q => M.F q u) θ| ≤ M.M₂) ∧
  (∀ θ ∈ Set.Icc M.θl M.θu,
    (∀ᵐ u ∂M.ν, M.η < deriv M.ℓ (M.F θ u - objective M θ)) ∧
    (∀ t ∈ Set.Icc M.tl M.tu,
      ∀ᵐ u ∂M.ν,
        DifferentiableAt ℝ (fun q => M.ℓ (M.F q u - t)) θ ∧
        DifferentiableAt ℝ (fun s => M.ℓ (M.F θ u - s)) t) ∧
    (∫ u, (deriv M.ℓ (M.F θ u - objective M θ) -
          ∫ v, deriv M.ℓ (M.F θ v - objective M θ) ∂M.ν) ^ 2 ∂M.ν ≤ M.zeta ^ 2) ∧
    (∫ u, (deriv M.ℓ (M.F θ u - objective M θ) * deriv (fun q => M.F q u) θ -
          ∫ v, deriv M.ℓ (M.F θ v - objective M θ) * deriv (fun q => M.F q v) θ ∂M.ν) ^ 2
        ∂M.ν ≤ M.zetaTilde ^ 2) ∧
    (∫ u, (deriv M.ℓ (M.F θ u - objective M θ)) ^ 2 ∂M.ν ≤ M.β₁))

/-- The smoothness that the paper explicitly says Assumptions 7 and 9 ensure (p.9).  It rules
out Mathlib's junk value `deriv f x = 0` at nondifferentiability points while adding no new
mathematical regime intended by the source. -/
def SmoothObjective {E : Type*} [MeasurableSpace E] (M : Model E) : Prop :=
  DifferentiableOn ℝ (objective M) (Set.Icc M.θl M.θu) ∧
  DifferentiableOn ℝ (deriv (objective M)) (Set.Icc M.θl M.θu)

/-- The paper's uniform reading of the initial inner-estimator error. -/
noncomputable def initialError {E : Type*} [MeasurableSpace E] (M : Model E) : ℝ :=
  sSup ((fun θ => |M.t₀ - objective M θ|) '' Set.Icc M.θl M.θu)

/-- `K₁(m)` in Lemma 1, at a fixed parameter. -/
noncomputable def K1 {E : Type*} [MeasurableSpace E] (M : Model E) (θ : ℝ) (m : ℕ) : ℝ :=
  Real.exp (M.L₁ ^ 2 * M.c ^ 2 * Real.pi ^ 2 / 12) *
    (|M.t₀ - objective M θ| / (m : ℝ) ^ (M.μ₁ * M.c - 1 / 2) +
      (2 : ℝ) ^ (M.μ₁ * M.c) * M.c * M.σ / (M.μ₁ * M.c - 1 / 2))

/-- The uniform `K₁(m)` used when the estimator is evaluated at random outer iterates. -/
noncomputable def K1Uniform {E : Type*} [MeasurableSpace E] (M : Model E) (m : ℕ) : ℝ :=
  Real.exp (M.L₁ ^ 2 * M.c ^ 2 * Real.pi ^ 2 / 12) *
    (initialError M / (m : ℝ) ^ (M.μ₁ * M.c - 1 / 2) +
      (2 : ℝ) ^ (M.μ₁ * M.c) * M.c * M.σ / (M.μ₁ * M.c - 1 / 2))

noncomputable def C4of {E : Type*} [MeasurableSpace E] (M : Model E) (K : ℝ) : ℝ :=
  (Real.sqrt M.β₁ * (K * M.M₂ * M.L₂ + M.zetaTilde) +
    Real.sqrt M.β₁ * M.M₂ * (K * M.L₂ + M.zeta)) / M.η ^ 2

noncomputable def C5of {E : Type*} [MeasurableSpace E] (M : Model E) (K : ℝ) : ℝ :=
  (2 * M.β₁ * (2 * M.L₂ ^ 2 * K ^ 2 + M.zeta ^ 2) +
    2 * M.β₁ * M.M₂ ^ 2 * (2 * M.L₂ ^ 2 * M.M₂ ^ 2 * K ^ 2 + M.zetaTilde ^ 2)) /
      M.η ^ 4

noncomputable def C4 {E : Type*} [MeasurableSpace E] (M : Model E) (θ : ℝ) (m : ℕ) : ℝ :=
  C4of M (K1 M θ m)

noncomputable def C5 {E : Type*} [MeasurableSpace E] (M : Model E) (θ : ℝ) (m : ℕ) : ℝ :=
  C5of M (K1 M θ m)

noncomputable def C4Uniform {E : Type*} [MeasurableSpace E] (M : Model E) (m : ℕ) : ℝ :=
  C4of M (K1Uniform M m)

noncomputable def C5Uniform {E : Type*} [MeasurableSpace E] (M : Model E) (m : ℕ) : ℝ :=
  C5of M (K1Uniform M m)

/-- `B₁=L₁M₂/η` from Lemma 2 and Theorem 6. -/
noncomputable def B1 {E : Type*} [MeasurableSpace E] (M : Model E) : ℝ := M.L₁ * M.M₂ / M.η

/-- `L₄` from Lemma 2, with the missing `L₃` interpreted as a bound on `|ξ''(θ)|`, exactly as
the proof on p.27 uses it. -/
noncomputable def L4 {E : Type*} [MeasurableSpace E] (M : Model E) (L₃ : ℝ) : ℝ :=
  (2 * M.L₁ * M.L₂ * M.M₂ ^ 2 + 2 * M.L₁ * M.L₂ * B1 M * M.M₂ + M.L₁ ^ 2 * L₃) /
    M.η ^ 2

/-- `n_i=n-⌈2^{-i}n⌉` in (19), with natural-number subtraction. -/
noncomputable def phaseStart (n i : ℕ) : ℕ :=
  n - ⌈(2 : ℝ) ^ (-(i : ℝ)) * n⌉₊

/-- The assertion that `p=inf{i:2^{-i}n≤1}` in (19), expressed without choosing a default
value for an empty infimum. -/
def IsPhaseCount (n p : ℕ) : Prop :=
  (2 : ℝ) ^ (-(p : ℝ)) * n ≤ 1 ∧ ∀ i < p, 1 < (2 : ℝ) ^ (-(i : ℝ)) * n

end OnlineUBSR.Supplement


