-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18
-- name    : QAlgorithms_Papers_Independent_Dependency50_P18
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T13:53:20.236913+00:00
-- url     : https://prove2.me/theorems/8e073f9e-a60f-426e-836d-5678e2d67f4c
-- title:
--   Definitions for Upper Bounds on the Distillable Randomness of Bipartite Quantum States
-- statement:
--   The objects the formalized statements of *Upper Bounds on the Distillable Randomness of Bipartite Quantum States* (arXiv:2212.09073) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `swap`: Proposition 1, p.2: actual matrix subsystem exchange.
--   - `GammaFeasible`: Section III, p.2, (2): Hermitian witnesses and both signs of both constraints.
--   - `correlationGauge`: Section III, p.2, (2): trace infimum, without any attainment assumption.
--   - `logBits`: Extended binary logarithm, with log(0)=-infinity and log(+infinity)=+infinity. Only nonnegative arguments occur in the source's correlation measures (p.2).
--   - `cGamma`: Section III, p.2, (3), including C_gamma(0)=-infinity.
--   - `Divergence`: Dimension-compatible divergence; the second argument need not be normalized.
--   - `IsGeneralizedDivergence`: Section II, p.2: exactly the three printed divergence laws. The source leaves the zero-comparison boundary open; Proposition 4 states its necessary boundary condition explicitly, rather than restricting every generic divergence result. Faithfulness and continuity are imposed only where explicitly needed.
--   - `capitalGamma`: Section III, p.2, (4): extended infimum over PSD gamma-feasible comparisons.
--   - `normalizedComparison`: Section III, p.2, (5): the comparison is computed from rho, not a free variable. For a state gamma is finite and at least one, by Appendices C–D.
--   - `IsProductState`: Proposition 4, p.3: both product factors are states.
--   - `DivergenceFaithful`: Proposition 4, p.3: ordinary faithfulness on normalized states only.
--   - `DivergenceLowerSemicontinuous`: Appendix C, pp.8–9: lower semicontinuity in the PSD second argument, including the subnormalized sequence whose trace tends to one in (94).
--   - `cqLeft`: Proposition 7, p.3, (17): cq input in the AX:B ordering.
--   - `cqRight`: Proposition 7, p.3: the same cq operator in the A:BX ordering.
--   - `bipartiteTensor`: Proposition 8, p.3: product input regrouped as A1A2:B1B2.
--   - `DivergenceSubadditive`: Additional divergence premise only for (21), p.3.
--   - `classicalTarget`: Section II, p.2, (1): diagonal separable maximally classically correlated target.
--   - `supportIncluded`: Positive-matrix support inclusion, used at singular comparison operators.
--   - `umegaki`: Section III, p.3, (24): support-aware Umegaki divergence in bits. Supernormalized comparisons may give negative values.
--   - `sandwiched`: Section III, p.3, (23), for alpha>1: trace-power sandwiched Renyi divergence. Negative spectral powers use the pseudoinverse; support violations give +infinity.
--   - `errorPenalty`: Proposition 10, p.3: epsilon=1 has infinite penalty, not a real-log junk value.
--   - `betaA`: Section VI, p.5, (52): fix Alice's reference; infeasibility gives +infinity.
--   - `betaB`: Section VI, p.5, (54): fix Bob's reference, retaining both signs.
--   - `upsilonA`: Section VI, p.5, (53): target marginal fixed before optimizing sigma.
--   - `upsilonB`: Section VI, p.5, (54): Bob's target marginal is fixed before optimization.
--   - `staticBeta`: Appendix I, p.11, (181): this marginal belongs to sigma, unlike Section VI.
--   - `staticUpsilon`: Appendix I, p.11, (183): a distinct static Upsilon infimum.
--   - `ClassicalOutput`: Section IV, pp.3–4: a classical output channel has diagonal output on every input.
--   - `ClassicalMessage`: Section IV, p.4: only the transmitted register is classical; the local memory may remain quantum and correlated with that register.
--   - `RandomnessProtocol`: Section IV, pp.3–4, (27)–(34): an arbitrary finite protocol, with local workspaces of any finite nonzero dimension. A message is moved to the receiver, never copied as a quantum register. Validity is imposed separately. There is no initial auxiliary shared seed; the only initial joint input is the supplied rho. Consecutive sends by one party can be combined into a single alphabet; trivial one-symbol sends put any protocol into the source's alternating order.
--   - `RandomnessProtocol.Valid`: Local operations must be CPTP, transmitted messages classical, and both final registers classical, as required in Section IV, pp.3–4.
--   - `RandomnessProtocol.OneWay`: Section IV, (29): Alice-to-Bob only. Combining consecutive Alice messages and commuting her final local measurement gives exactly the E,D form on p.3.
--   - `RandomnessProtocol.run`: Execution, including subsystem transfer, of the protocol (Section IV, (32)).
--   - `RandomnessProtocol.communication`: Sum of binary logarithms of full message-alphabet sizes, (29), (34), p.4. No expected-length convention or discount for unused symbols is used.
--   - `oneShot`: One-shot distillable randomness, (29), (34), p.4: `twoWay=true` admits every finite protocol, and `false` restricts to Alice-to-Bob communication.
--   - `randomnessBlockRate`: Rate per input copy at block length n+1, avoiding division by zero (p.4).
--   - `ordinaryRate`: Ordinary distillable randomness: inf over eps in (0,1] of the liminf, (30), (35), p.4. The positive block lengths run through n+1.
--   - `strongConverseRate`: Strong-converse rate: sup over eps in [0,1) of the limsup, (31), (36), p.4. The asymmetric error interval is intentional.
-- source:
--   Upper Bounds on the Distillable Randomness of Bipartite Quantum States, arXiv:2212.09073v1, https://arxiv.org/abs/2212.09073v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-! Statements from Lami–Regula–Wang–Wilde, arXiv:2212.09073v1.
Pages are PDF pages. New definitions belong exclusively to this paper; exact primitives are imported from
the pinned accepted library. Correlation gamma is `correlationGauge`, distinct from
the accepted partial transpose called `gamma`.
All optimization values are extended real numbers. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

/-- Proposition 1, p.2: actual matrix subsystem exchange. -/
def swap {A B : Type} (s : Matrix (A × B) (A × B) ℂ) :
    Matrix (B × A) (B × A) ℂ := fun i j => s (i.2, i.1) (j.2, j.1)

/-- Section III, p.2, (2): Hermitian witnesses and both signs of both constraints. -/
def GammaFeasible {A B : Type} [Fintype A] [Fintype B]
    (s : Matrix (A × B) (A × B) ℂ) (k : Matrix A A ℂ) (l : Matrix B B ℂ)
    (v : Matrix (A × B) (A × B) ℂ) : Prop :=
  k.IsHermitian ∧ l.IsHermitian ∧ v.IsHermitian ∧
    (QAlgorithms.Papers.Independent.Information100.P04.gamma (v + s)).PosSemidef ∧
    (QAlgorithms.Papers.Independent.Information100.P04.gamma (v - s)).PosSemidef ∧
    (Matrix.kronecker k l + v).PosSemidef ∧ (Matrix.kronecker k l - v).PosSemidef

/-- Section III, p.2, (2): trace infimum, without any attainment assumption. -/
def correlationGauge {A B : Type} [Fintype A] [Fintype B]
    (s : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {r | ∃ k l v, GammaFeasible s k l v ∧ r = ((Matrix.kronecker k l).trace.re : EReal)}

/-- Extended binary logarithm, with log(0)=-infinity and log(+infinity)=+infinity.
Only nonnegative arguments occur in the source's correlation measures (p.2). -/
def logBits (x : EReal) : EReal :=
  if x = 0 then ⊥ else if x = ⊤ then ⊤ else if x = ⊥ then ⊥
  else (Real.logb 2 x.toReal : EReal)

/-- Section III, p.2, (3), including C_gamma(0)=-infinity. -/
def cGamma {A B : Type} [Fintype A] [Fintype B]
    (s : Matrix (A × B) (A × B) ℂ) : EReal := logBits (correlationGauge s)

/-- Dimension-compatible divergence; the second argument need not be normalized. -/
abbrev Divergence := ∀ {I : Type} [Fintype I] [DecidableEq I],
  Matrix I I ℂ → Matrix I I ℂ → EReal

/-- Section II, p.2: exactly the three printed divergence laws. The source leaves
the zero-comparison boundary open; Proposition 4 states its necessary boundary
condition explicitly, rather than restricting every generic divergence result.
Faithfulness and continuity are imposed only where explicitly needed. -/
structure IsGeneralizedDivergence (D : Divergence) : Prop where
  dataProcessing : ∀ {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho sigma : Matrix I I ℂ) (N : QAlgorithms.Superop I J),
    QAlgorithms.IsDensityMatrix rho → sigma.PosSemidef → QAlgorithms.IsChannel N →
    D (N rho) (N sigma) ≤ D rho sigma
  scaling : ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (c : ℝ), QAlgorithms.IsDensityMatrix rho →
    sigma.PosSemidef → 0 < c →
    D rho ((c : ℂ) • sigma) = D rho sigma - (Real.logb 2 c : EReal)
  zeroValue : ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : Matrix I I ℂ), QAlgorithms.IsDensityMatrix rho → D rho rho = 0

/-- Section III, p.2, (4): extended infimum over PSD gamma-feasible comparisons. -/
def capitalGamma (D : Divergence) {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {r | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    sigma.PosSemidef ∧ correlationGauge sigma ≤ 1 ∧ r = D rho sigma}

/-- Section III, p.2, (5): the comparison is computed from rho, not a free variable.
For a state gamma is finite and at least one, by Appendices C–D. -/
def normalizedComparison {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  (((correlationGauge rho).toReal)⁻¹ : ℂ) • rho

/-- Proposition 4, p.3: both product factors are states. -/
def IsProductState {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ s : Matrix A A ℂ, ∃ t : Matrix B B ℂ,
    QAlgorithms.IsDensityMatrix s ∧ QAlgorithms.IsDensityMatrix t ∧ rho = Matrix.kronecker s t

/-- Proposition 4, p.3: ordinary faithfulness on normalized states only. -/
def DivergenceFaithful (D : Divergence) : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ), QAlgorithms.IsDensityMatrix rho →
    QAlgorithms.IsDensityMatrix sigma → (D rho sigma = 0 ↔ rho = sigma)

/-- Appendix C, pp.8–9: lower semicontinuity in the PSD second argument,
including the subnormalized sequence whose trace tends to one in (94). -/
def DivergenceLowerSemicontinuous (D : Divergence) : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : Matrix I I ℂ), QAlgorithms.IsDensityMatrix rho →
    LowerSemicontinuous (fun s : {s : Matrix I I ℂ // s.PosSemidef} => D rho s.1)

/-- Proposition 7, p.3, (17): cq input in the AX:B ordering. -/
def cqLeft {A B X : Type} [DecidableEq X]
    (p : X → ℝ) (rho : X → Matrix (A × B) (A × B) ℂ) :
    Matrix ((A × X) × B) ((A × X) × B) ℂ :=
  fun i j => if i.1.2 = j.1.2 then
    (p i.1.2 : ℂ) * rho i.1.2 (i.1.1, i.2) (j.1.1, j.2) else 0

/-- Proposition 7, p.3: the same cq operator in the A:BX ordering. -/
def cqRight {A B X : Type} [DecidableEq X]
    (p : X → ℝ) (rho : X → Matrix (A × B) (A × B) ℂ) :
    Matrix (A × (B × X)) (A × (B × X)) ℂ :=
  fun i j => if i.2.2 = j.2.2 then
    (p i.2.2 : ℂ) * rho i.2.2 (i.1, i.2.1) (j.1, j.2.1) else 0

/-- Proposition 8, p.3: product input regrouped as A1A2:B1B2. -/
def bipartiteTensor {A B C E : Type}
    (s : Matrix (A × B) (A × B) ℂ) (t : Matrix (C × E) (C × E) ℂ) :
    Matrix ((A × C) × (B × E)) ((A × C) × (B × E)) ℂ :=
  fun i j => s (i.1.1, i.2.1) (j.1.1, j.2.1) * t (i.1.2, i.2.2) (j.1.2, j.2.2)

/-- Additional divergence premise only for (21), p.3. -/
def DivergenceSubadditive (D : Divergence) : Prop :=
  ∀ {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] (r s : Matrix I I ℂ) (t u : Matrix J J ℂ),
    QAlgorithms.IsDensityMatrix r → s.PosSemidef →
    QAlgorithms.IsDensityMatrix t → u.PosSemidef →
    D (Matrix.kronecker r t) (Matrix.kronecker s u) ≤ D r s + D t u

/-- Section II, p.2, (1): diagonal separable maximally classically correlated target. -/
def classicalTarget (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun i j => if i = j ∧ i.1 = i.2 then (d : ℂ)⁻¹ else 0

/-- Positive-matrix support inclusion, used at singular comparison operators. -/
def supportIncluded {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : Prop :=
  LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin

/-- Section III, p.3, (24): support-aware Umegaki divergence in bits.
Supernormalized comparisons may give negative values. -/
def umegaki : Divergence := fun rho sigma =>
  if supportIncluded rho sigma then
    (((cfc (fun x : ℝ => x * Real.log x) rho - rho * cfc Real.log sigma).trace.re /
      Real.log 2 : ℝ) : EReal)
  else ⊤

/-- Section III, p.3, (23), for alpha>1: trace-power sandwiched Renyi divergence.
Negative spectral powers use the pseudoinverse; support violations give +infinity. -/
def sandwiched (alpha : ℝ) : Divergence := fun rho sigma =>
  if supportIncluded rho sigma then
    let h := cfc (fun x : ℝ => x ^ ((1 - alpha) / (2 * alpha))) sigma
    let q := (cfc (fun x : ℝ => x ^ alpha) (h * rho * h)).trace.re
    logBits (q : EReal) * (((alpha - 1)⁻¹ : ℝ) : EReal)
  else ⊤

/-- Proposition 10, p.3: epsilon=1 has infinite penalty, not a real-log junk value. -/
def errorPenalty (alpha eps : ℝ) : EReal :=
  if eps = 1 then ⊤ else
    ((alpha / (alpha - 1) * Real.logb 2 (1 / (1 - eps)) : ℝ) : EReal)

/-- Section VI, p.5, (52): fix Alice's reference; infeasibility gives +infinity. -/
def betaA {A B : Type} [Fintype A] [Fintype B]
    (sigma : Matrix (A × B) (A × B) ℂ) (a : Matrix A A ℂ) : EReal :=
  sInf {r | ∃ l v, GammaFeasible sigma a l v ∧ r = ((Matrix.kronecker a l).trace.re : EReal)}

/-- Section VI, p.5, (54): fix Bob's reference, retaining both signs. -/
def betaB {A B : Type} [Fintype A] [Fintype B]
    (sigma : Matrix (A × B) (A × B) ℂ) (b : Matrix B B ℂ) : EReal :=
  sInf {r | ∃ k v, GammaFeasible sigma k b v ∧ r = ((Matrix.kronecker k b).trace.re : EReal)}

/-- Section VI, p.5, (53): target marginal fixed before optimizing sigma. -/
def upsilonA (D : Divergence) {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {r | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    sigma.PosSemidef ∧ betaA sigma (QAlgorithms.traceRight rho) ≤ 1 ∧ r = D rho sigma}

/-- Section VI, p.5, (54): Bob's target marginal is fixed before optimization. -/
def upsilonB (D : Divergence) {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {r | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    sigma.PosSemidef ∧ betaB sigma (QAlgorithms.traceLeft rho) ≤ 1 ∧ r = D rho sigma}

/-- Appendix I, p.11, (181): this marginal belongs to sigma, unlike Section VI. -/
def staticBeta {A B : Type} [Fintype A] [Fintype B]
    (sigma : Matrix (A × B) (A × B) ℂ) : EReal := betaA sigma (QAlgorithms.traceRight sigma)

/-- Appendix I, p.11, (183): a distinct static Upsilon infimum. -/
def staticUpsilon (D : Divergence) {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {r | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    sigma.PosSemidef ∧ staticBeta sigma ≤ 1 ∧ r = D rho sigma}

example {A B : Type} (s : Matrix (A × B) (A × B) ℂ) :
    QAlgorithms.Papers.Independent.Information100.P04.gamma (QAlgorithms.Papers.Independent.Information100.P04.gamma s) = s := rfl

example {A B : Type} (s : Matrix (A × B) (A × B) ℂ) : swap (swap s) = s := rfl

example : logBits 0 = ⊥ := by simp [logBits]

example (alpha : ℝ) : errorPenalty alpha 1 = ⊤ := by simp [errorPenalty]

example : classicalTarget 2 (0, 0) (1, 1) = 0 := by simp [classicalTarget]

example {A B : Type} [Fintype A] [Fintype B]
    (s : Matrix (A × B) (A × B) ℂ) :
    staticBeta s = betaA s (QAlgorithms.traceRight s) := rfl

/-- Section IV, pp.3–4: a classical output channel has diagonal output on every input. -/
def ClassicalOutput {I J : Type} (N : QAlgorithms.Superop I J) : Prop :=
  ∀ s i j, i ≠ j → N s i j = 0

/-- Section IV, p.4: only the transmitted register is classical; the local memory
may remain quantum and correlated with that register. -/
def ClassicalMessage {I C : Type} {l : ℕ} (N : QAlgorithms.Superop I (C × Fin l)) : Prop :=
  ∀ s i j, i.2 ≠ j.2 → N s i j = 0

/-- Section IV, pp.3–4, (27)–(34): an arbitrary finite protocol, with local
workspaces of any finite nonzero dimension. A message is moved to the receiver,
never copied as a quantum register. Validity is imposed separately. There is no
initial auxiliary shared seed; the only initial joint input is the supplied rho.
Consecutive sends by one party can be combined into a single alphabet; trivial
one-symbol sends put any protocol into the source's alternating order. -/
inductive RandomnessProtocol : Type → Type → ℕ → Type 1 where
  | finish {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      [Nonempty A] [Nonempty B] (d : ℕ)
      (N : QAlgorithms.Superop A (Fin d)) (M : QAlgorithms.Superop B (Fin d)) :
      RandomnessProtocol A B d
  | alice {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
      [DecidableEq A] [DecidableEq B] [DecidableEq C]
      [Nonempty A] [Nonempty B] [Nonempty C] {d : ℕ}
      (l : ℕ) (hl : 0 < l) (N : QAlgorithms.Superop A (C × Fin l))
      (rest : RandomnessProtocol C (B × Fin l) d) : RandomnessProtocol A B d
  | bob {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
      [DecidableEq A] [DecidableEq B] [DecidableEq C]
      [Nonempty A] [Nonempty B] [Nonempty C] {d : ℕ}
      (l : ℕ) (hl : 0 < l) (M : QAlgorithms.Superop B (C × Fin l))
      (rest : RandomnessProtocol (A × Fin l) C d) : RandomnessProtocol A B d

/-- Local operations must be CPTP, transmitted messages classical, and both final
registers classical, as required in Section IV, pp.3–4. -/
def RandomnessProtocol.Valid {A B : Type} {d : ℕ} : RandomnessProtocol A B d → Prop
  | @RandomnessProtocol.finish _ _ fA fB eA eB _ _ _ N M =>
      letI := fA
      letI := fB
      letI := eA
      letI := eB
      QAlgorithms.IsChannel N ∧ QAlgorithms.IsChannel M ∧
        ClassicalOutput N ∧ ClassicalOutput M
  | @RandomnessProtocol.alice _ _ _ fA _ fC eA _ _ _ _ _ _ _ _ N rest =>
      letI := fA
      letI := fC
      letI := eA
      QAlgorithms.IsChannel N ∧ ClassicalMessage N ∧ rest.Valid
  | @RandomnessProtocol.bob _ _ _ _ fB fC _ eB _ _ _ _ _ _ _ M rest =>
      letI := fB
      letI := fC
      letI := eB
      QAlgorithms.IsChannel M ∧ ClassicalMessage M ∧ rest.Valid

/-- Section IV, (29): Alice-to-Bob only. Combining consecutive Alice messages
and commuting her final local measurement gives exactly the E,D form on p.3. -/
def RandomnessProtocol.OneWay {A B : Type} {d : ℕ} : RandomnessProtocol A B d → Prop
  | @RandomnessProtocol.finish _ _ _ _ _ _ _ _ _ _ _ => True
  | @RandomnessProtocol.alice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest => rest.OneWay
  | @RandomnessProtocol.bob _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => False

/-- Execution, including subsystem transfer, of the protocol (Section IV, (32)). -/
def RandomnessProtocol.run {A B : Type} {d : ℕ} (P : RandomnessProtocol A B d)
    (rho : Matrix (A × B) (A × B) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  match P with
  | @RandomnessProtocol.finish _ _ fA fB eA eB _ _ _ N M =>
      letI := fA
      letI := fB
      letI := eA
      letI := eB
      QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M rho
  | @RandomnessProtocol.alice _ _ _ fA fB _ eA eB _ _ _ _ _ _ _ N rest =>
      letI := fA
      letI := fB
      letI := eA
      letI := eB
      let s := QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N (fun t => t) rho
      rest.run (fun i j => s ((i.1, i.2.2), i.2.1) ((j.1, j.2.2), j.2.1))
  | @RandomnessProtocol.bob _ _ _ fA fB _ eA eB _ _ _ _ _ _ _ M rest =>
      letI := fA
      letI := fB
      letI := eA
      letI := eB
      let s := QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (fun t => t) M rho
      rest.run (fun i j => s (i.1.1, (i.2, i.1.2)) (j.1.1, (j.2, j.1.2)))

/-- Sum of binary logarithms of full message-alphabet sizes, (29), (34), p.4.
No expected-length convention or discount for unused symbols is used. -/
def RandomnessProtocol.communication {A B : Type} {d : ℕ} :
    RandomnessProtocol A B d → ℝ
  | @RandomnessProtocol.finish _ _ _ _ _ _ _ _ _ _ _ => 0
  | @RandomnessProtocol.alice _ _ _ _ _ _ _ _ _ _ _ _ _ l _ _ rest =>
      Real.logb 2 l + rest.communication
  | @RandomnessProtocol.bob _ _ _ _ _ _ _ _ _ _ _ _ _ l _ _ rest =>
      Real.logb 2 l + rest.communication

/-- One-shot distillable randomness, (29), (34), p.4: `twoWay=true` admits every
finite protocol, and `false` restricts to Alice-to-Bob communication. -/
def oneShot {A B : Type} (twoWay : Bool) (eps : ℝ)
    (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sSup {r | ∃ d : ℕ, 0 < d ∧ ∃ P : RandomnessProtocol A B d,
    P.Valid ∧ (twoWay = true ∨ P.OneWay) ∧
    1 - eps ≤ QAlgorithms.Papers.Independent.Information100.P67.squaredFidelity (classicalTarget d) (P.run rho) ∧
    r = ((Real.logb 2 d - P.communication : ℝ) : EReal)}

/-- Rate per input copy at block length n+1, avoiding division by zero (p.4). -/
def randomnessBlockRate {A B : Type} (twoWay : Bool) (eps : ℝ)
    (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) : EReal :=
  (((n + 1 : ℕ) : ℝ)⁻¹ : EReal) *
    oneShot twoWay eps (QAlgorithms.Papers.Independent.Information100.P04.copies rho (n + 1))

/-- Ordinary distillable randomness: inf over eps in (0,1] of the liminf,
(30), (35), p.4. The positive block lengths run through n+1. -/
def ordinaryRate {A B : Type} (twoWay : Bool)
    (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {r | ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
    r = Filter.liminf (randomnessBlockRate twoWay eps rho) Filter.atTop}

/-- Strong-converse rate: sup over eps in [0,1) of the limsup,
(31), (36), p.4. The asymmetric error interval is intentional. -/
def strongConverseRate {A B : Type} (twoWay : Bool)
    (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sSup {r | ∃ eps : ℝ, 0 ≤ eps ∧ eps < 1 ∧
    r = Filter.limsup (randomnessBlockRate twoWay eps rho) Filter.atTop}

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (d : ℕ)
    (N : QAlgorithms.Superop A (Fin d)) (M : QAlgorithms.Superop B (Fin d)) :
    (RandomnessProtocol.finish d N M).communication = 0 := rfl

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (d : ℕ)
    (N : QAlgorithms.Superop A (Fin d)) (M : QAlgorithms.Superop B (Fin d))
    (rho : Matrix (A × B) (A × B) ℂ) :
    (RandomnessProtocol.finish d N M).run rho = QAlgorithms.Papers.Independent.Information100.P62.tensorChannel N M rho := rfl

example {A B : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (i j : (Fin 0 → A) × (Fin 0 → B)) : QAlgorithms.Papers.Independent.Information100.P04.copies rho 0 i j = 1 := by
  simp [QAlgorithms.Papers.Independent.Information100.P04.copies]

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

end QAlgorithms.Papers.Independent.Dependency50.P18


