-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P20
-- name    : QAlgorithms_Papers_Independent_Bridge50_P20
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T14:57:14.82256+00:00
-- url     : https://prove2.me/theorems/2c5741f6-bb99-456c-9f59-72a7068f7b13
-- title:
--   Definitions for Versatile relative entropy bounds for quantum networks
-- statement:
--   The objects the formalized statements of *Versatile relative entropy bounds for quantum networks* (arXiv:1707.05543) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `stateEMax`: PDF p.4, (10): optimize over all separable normalized comparison states.
--   - `channelEMax`: PDF pp.2,17, (1),(50): the original optimization over all normalized mixed inputs and all positive finite reference dimensions, before the pure-input reduction. Writing r+1 includes every positive reference dimension, independently of the input.
--   - `comparisonFeasible`: PDF p.17, (51): false selects all separable states; true adds the fixed reference marginal, retaining the normalization of the full comparison state.
--   - `comparisonMinimum`: PDF p.17, (51): extended optimal value; attainment is not built into the definition.
--   - `IsComparisonOptimizer`: PDF p.28, Lemma 1: an actual attaining optimizer in its specified feasible set.
--   - `privateDensity`: PDF p.5, (14)-(15): private state on (keyA,shieldA):(keyB,shieldB). The twisting blocks may act jointly on both shields. This is the entry formula for U(psi_d tensor shield)U-adjoint after regrouping the local registers.
--   - `IsPrivateTarget`: PDF p.5, (14)-(15): actual private targets, with arbitrary positive finite shield dimensions in the theorem binders. One-dimensional shields include maximally entangled targets; no shield dimension is bounded by d.
--   - `amplitudeDampingKraus`: PDF p.18, (54)-(55): excited-state damping probability lambda.
--   - `amplitudeChoiLower`: PDF p.18, (57): the unconstrained Choi minimum. The branch containing 1/(2 lambda) is never selected at zero on the theorem's physical domain.
--   - `amplitudeValue`: PDF p.18, (57)-(58): the constrained Choi optimum and exact channel value.
--   - `phaseUnitary`: PDF p.27, (B2): opposite signs and half angles on the two parties. The frozen zRotation a is exp(-i a sigma_z/2); arguments -theta,theta therefore give exactly exp(+i theta sigma_z/2) tensor exp(-i theta sigma_z/2).
--   - `phaseConjugate`: PDF pp.27-28, (B2)-(B4): conjugation by the source's product unitary.
--   - `phaseTwirl`: PDF p.28, (B3)-(B4): normalized angular average, on every matrix entry. The integrands are continuous on a compact interval, so the Bochner integrals are genuine integrals rather than nonintegrability defaults.
--   - `IsPhaseCovariant`: PDF pp.27-28, (B1): covariance is required for every normalized input and every real angle. The frozen zRotation (-2*theta) is exp(+i theta sigma_z), so the source's sign and angle in (B1) are retained.
--   - `IsPhaseInvariant`: PDF p.28, (B3): invariance under every angle in a complete period.
--   - `PhaseParameters`: PDF p.28, (B6): parameters in the source's order alpha,beta,gamma,delta,xi,phi.
--   - `PhaseParameters.Valid`: PDF p.28, (B6): positivity, trace one, phase range, and the two PPT/PSD coherence bounds, specialized to two qubits.
--   - `invariantSeparableMatrix`: PDF p.28, (B6): basis order 00,01,10,11. Upper-right coherence has +i phi.
--   - `PhaseParameters.FixedMarginal`: PDF p.28, (B6): extra marginal equations for the upper Choi bound.
--   - `relativeAdvantage`: PDF p.16, (49): a is the finite squashed cut cost, b the finite versatile cut cost. This compares cost terms in the vanishing-error regime.
--   - `dephasingSquashedBound`: PDF p.21, (63): the cited dephasing squashed-entanglement upper bound. The +1/2 is outside the radical. Binary entropy uses the frozen convention.
--   - `dampingSquashedBound`: PDF p.21, (64): the cited amplitude-damping squashed-entanglement upper bound.
--   - `dephasingRelativeValue`: PDF p.21: the cited exact dephasing REE value, phase-flip probability x/2.
--   - `exampleAdvantage`: PDF pp.20-21, (49),(62): substituted cost ratio before cancelling the common expected channel use count m. No claim to compute exact E_sq is made.
-- source:
--   Versatile relative entropy bounds for quantum networks, arXiv:1707.05543v2, https://arxiv.org/abs/1707.05543v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

/-!
arXiv:1707.05543v2, finite-dimensional state/channel results.
The reported duplicate definitions are imported from the pinned accepted library.
Its zRotation is used with the source's signs and angle scaling; the distinct
(B6) state family is named invariantSeparableMatrix to distinguish phase gates.
All entropies are in bits. Optimizations use EReal so infeasible sets and
support failures retain infinity. The original channel optimization includes
mixed inputs and every positive finite reference dimension.
Operational LOCC/network results are deferred in the unit's HARD.md; they
are not represented by assumed scalar recurrences. Compilation is pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P20

open QAlgorithms QAlgorithms.Entanglement

-- Reuse pinned accepted definitions; source-specific conventions are audited below.
open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)
open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)
open QAlgorithms.Papers.Independent.Information100.P53 (amplitudeDamping)
open QAlgorithms.Papers.Independent.Information100.P75 (mixedIdentity)
open QAlgorithms.Papers.Independent.Next46.P29 (zRotation)
open QAlgorithms.Papers.Independent.Support50.P11 (choiState)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (10): optimize over all separable normalized comparison states. -/
def stateEMax {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {v : EReal | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    IsSeparableDensity sigma ∧ v = maxRelative rho sigma}

/-- PDF pp.2,17, (1),(50): the original optimization over all normalized mixed
inputs and all positive finite reference dimensions, before the pure-input reduction.
Writing r+1 includes every positive reference dimension, independently of the input. -/
def channelEMax {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (N : Superop I O) : EReal :=
  sSup {v : EReal | ∃ r : ℕ,
    ∃ rho : Matrix (Fin (r + 1) × I) (Fin (r + 1) × I) ℂ,
      IsDensityMatrix rho ∧ v = stateEMax (idTensorSuperop N rho)}

/-- PDF p.17, (51): false selects all separable states; true adds the fixed
reference marginal, retaining the normalization of the full comparison state. -/
def comparisonFeasible {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (fixed : Bool) (sigma : Matrix (A × B) (A × B) ℂ) : Prop :=
  IsSeparableDensity sigma ∧ (fixed = true → traceRight sigma = mixedIdentity A)

/-- PDF p.17, (51): extended optimal value; attainment is not built into the definition. -/
def comparisonMinimum {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (fixed : Bool) : EReal :=
  sInf {v : EReal | ∃ sigma : Matrix (A × B) (A × B) ℂ,
    comparisonFeasible fixed sigma ∧ v = maxRelative rho sigma}

/-- PDF p.28, Lemma 1: an actual attaining optimizer in its specified feasible set. -/
def IsComparisonOptimizer (rho sigma : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (fixed : Bool) : Prop :=
  comparisonFeasible fixed sigma ∧
    ∀ tau, comparisonFeasible fixed tau → maxRelative rho sigma ≤ maxRelative rho tau

/-- PDF p.5, (14)-(15): private state on (keyA,shieldA):(keyB,shieldB).
The twisting blocks may act jointly on both shields. This is the entry formula
for U(psi_d tensor shield)U-adjoint after regrouping the local registers. -/
def privateDensity {d s t : ℕ}
    (shield : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ)
    (U : Fin d → Fin d → Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ) :
    Matrix ((Fin d × Fin s) × (Fin d × Fin t))
      ((Fin d × Fin s) × (Fin d × Fin t)) ℂ :=
  fun x y => if x.1.1 = x.2.1 ∧ y.1.1 = y.2.1 then
    (d : ℂ)⁻¹ * (U x.1.1 x.2.1 * shield * (U y.1.1 y.2.1)ᴴ)
      (x.1.2, x.2.2) (y.1.2, y.2.2)
  else 0

/-- PDF p.5, (14)-(15): actual private targets, with arbitrary positive finite
shield dimensions in the theorem binders. One-dimensional shields include
maximally entangled targets; no shield dimension is bounded by d. -/
def IsPrivateTarget {d s t : ℕ}
    (phi : Matrix ((Fin d × Fin s) × (Fin d × Fin t))
      ((Fin d × Fin s) × (Fin d × Fin t)) ℂ) : Prop :=
  ∃ shield : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ,
    IsDensityMatrix shield ∧
    ∃ U : Fin d → Fin d → Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ,
      (∀ i j, (U i j)ᴴ * U i j = 1 ∧ U i j * (U i j)ᴴ = 1) ∧
      phi = privateDensity shield U

/-- PDF p.18, (54)-(55): excited-state damping probability lambda. -/
def amplitudeDampingKraus (lambda : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, (Real.sqrt (1 - lambda) : ℂ)],
    !![0, (Real.sqrt lambda : ℂ); 0, 0]]

/-- PDF p.18, (57): the unconstrained Choi minimum. The branch containing
1/(2 lambda) is never selected at zero on the theorem's physical domain. -/
def amplitudeChoiLower (lambda : ℝ) : ℝ :=
  if lambda ≤ (Real.sqrt 5 - 1) / 2 then
    Real.logb 2 ((1 / 2 : ℝ) * (1 + Real.sqrt (1 - lambda)) ^ 2)
  else Real.logb 2 ((1 + lambda) / (2 * lambda))

/-- PDF p.18, (57)-(58): the constrained Choi optimum and exact channel value. -/
def amplitudeValue (lambda : ℝ) : ℝ := Real.logb 2 (2 - lambda)

/-- PDF p.27, (B2): opposite signs and half angles on the two parties.
The frozen zRotation a is exp(-i a sigma_z/2); arguments -theta,theta
therefore give exactly exp(+i theta sigma_z/2) tensor exp(-i theta sigma_z/2). -/
def phaseUnitary (theta : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (zRotation (-theta)) (zRotation theta)

/-- PDF pp.27-28, (B2)-(B4): conjugation by the source's product unitary. -/
def phaseConjugate (theta : ℝ)
    (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  phaseUnitary theta * rho * (phaseUnitary theta)ᴴ

/-- PDF p.28, (B3)-(B4): normalized angular average, on every matrix entry.
The integrands are continuous on a compact interval, so the Bochner integrals
are genuine integrals rather than nonintegrability defaults. -/
def phaseTwirl (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ theta in (0 : ℝ)..(2 * Real.pi), phaseConjugate theta rho x y

/-- PDF pp.27-28, (B1): covariance is required for every normalized input
and every real angle. The frozen zRotation (-2*theta) is exp(+i theta sigma_z),
so the source's sign and angle in (B1) are retained. -/
def IsPhaseCovariant (N : Superop (Fin 2) (Fin 2)) : Prop :=
  ∀ theta : ℝ, ∀ rho : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix rho →
    N (zRotation (-2 * theta) * rho * (zRotation (-2 * theta))ᴴ) =
      zRotation (-2 * theta) * N rho * (zRotation (-2 * theta))ᴴ

/-- PDF p.28, (B3): invariance under every angle in a complete period. -/
def IsPhaseInvariant (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  ∀ theta ∈ Set.Icc (0 : ℝ) (2 * Real.pi), phaseConjugate theta rho = rho

/-- PDF p.28, (B6): parameters in the source's order alpha,beta,gamma,delta,xi,phi. -/
structure PhaseParameters where
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  delta : ℝ
  xi : ℝ
  phi : ℝ

/-- PDF p.28, (B6): positivity, trace one, phase range, and the two PPT/PSD
coherence bounds, specialized to two qubits. -/
def PhaseParameters.Valid (p : PhaseParameters) : Prop :=
  0 ≤ p.alpha ∧ 0 ≤ p.beta ∧ 0 ≤ p.gamma ∧ 0 ≤ p.delta ∧ 0 ≤ p.xi ∧
  p.alpha + p.beta + p.gamma + p.delta = 2 ∧
  p.phi ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
  p.xi ≤ min (Real.sqrt (p.alpha * p.beta)) (Real.sqrt (p.gamma * p.delta))

/-- PDF p.28, (B6): basis order 00,01,10,11. Upper-right coherence has +i phi. -/
def invariantSeparableMatrix (p : PhaseParameters) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => (1 / 2 : ℂ) *
    (if x = (0, 0) ∧ y = (0, 0) then (p.alpha : ℂ)
    else if x = (0, 1) ∧ y = (0, 1) then (p.gamma : ℂ)
    else if x = (1, 0) ∧ y = (1, 0) then (p.delta : ℂ)
    else if x = (1, 1) ∧ y = (1, 1) then (p.beta : ℂ)
    else if x = (0, 0) ∧ y = (1, 1) then
      (p.xi : ℂ) * Complex.exp ((p.phi : ℂ) * Complex.I)
    else if x = (1, 1) ∧ y = (0, 0) then
      (p.xi : ℂ) * Complex.exp (-((p.phi : ℂ) * Complex.I))
    else 0)

/-- PDF p.28, (B6): extra marginal equations for the upper Choi bound. -/
def PhaseParameters.FixedMarginal (p : PhaseParameters) : Prop :=
  p.gamma = 1 - p.alpha ∧ p.delta = 1 - p.beta

/-- PDF p.16, (49): a is the finite squashed cut cost, b the finite versatile
cut cost. This compares cost terms in the vanishing-error regime. -/
def relativeAdvantage (a b : ℝ) : ℝ := (a - b) / (a + b)

/-- PDF p.21, (63): the cited dephasing squashed-entanglement upper bound.
The +1/2 is outside the radical. Binary entropy uses the frozen convention. -/
def dephasingSquashedBound (x : ℝ) : ℝ :=
  binEntropy2 (Real.sqrt ((x / 2) * (1 - x / 2)) + 1 / 2)

/-- PDF p.21, (64): the cited amplitude-damping squashed-entanglement upper bound. -/
def dampingSquashedBound (lambda : ℝ) : ℝ :=
  binEntropy2 (1 / 2 - lambda / 4) - binEntropy2 (1 - lambda / 4)

/-- PDF p.21: the cited exact dephasing REE value, phase-flip probability x/2. -/
def dephasingRelativeValue (x : ℝ) : ℝ := 1 - binEntropy2 (x / 2)

/-- PDF pp.20-21, (49),(62): substituted cost ratio before cancelling the
common expected channel use count m. No claim to compute exact E_sq is made. -/
def exampleAdvantage (k : ℕ) (x lambda m : ℝ) : ℝ :=
  relativeAdvantage
    (m * ((k : ℝ) * dephasingSquashedBound x + dampingSquashedBound lambda))
    (m * ((k : ℝ) * dephasingRelativeValue x + amplitudeValue lambda))

/-! Small sanity examples for the complete paper-local definition bodies. -/

example : bellProjector 1 (0, 0) (0, 0) = 1 := by
  norm_num [bellProjector]

example : choiState (fun X : Matrix (Fin 2) (Fin 2) ℂ => X) (0, 0) (1, 1) = 1 / 2 := by
  norm_num [choiState, QAlgorithms.Papers.Independent.Information100.P34.choi]

example : privateDensity (d := 1) (s := 1) (t := 1)
    (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) (fun _ _ => 1)
    ((0, 0), (0, 0)) ((0, 0), (0, 0)) = 1 := by
  norm_num [privateDensity]

example : phaseTwirl (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 0 := by
  ext x y
  simp [phaseTwirl, phaseConjugate]

example : amplitudeDampingKraus 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [amplitudeDampingKraus, Matrix.one_apply]

example : amplitudeDampingKraus 1 0 1 1 = 0 := by
  norm_num [amplitudeDampingKraus]

example : zRotation 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zRotation, Matrix.diagonal_apply, Matrix.one_apply]

example (p : PhaseParameters) : invariantSeparableMatrix p (0, 1) (0, 1) = (p.gamma : ℂ) / 2 := by
  simp [invariantSeparableMatrix, div_eq_mul_inv, mul_comm]

example (p : PhaseParameters) : invariantSeparableMatrix p (1, 0) (1, 0) = (p.delta : ℂ) / 2 := by
  simp [invariantSeparableMatrix, div_eq_mul_inv, mul_comm]

example : relativeAdvantage 1 0 = 1 := by norm_num [relativeAdvantage]

example : amplitudeValue 1 = 0 := by norm_num [amplitudeValue]

end QAlgorithms.Papers.Independent.Bridge50.P20


