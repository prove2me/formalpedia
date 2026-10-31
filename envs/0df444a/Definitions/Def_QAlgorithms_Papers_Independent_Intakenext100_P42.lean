-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P42
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:38:05.100994+00:00
-- url     : https://prove2.me/theorems/2e76acd7-4c2c-4eb6-9973-5fcc20414612
-- title:
--   Definitions for Entanglement Measures and Purification Procedures
-- statement:
--   The objects the formalized statements of *Entanglement Measures and Purification Procedures* (arXiv:quant-ph/9707035) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `relativeEntanglementNats`: PDF p.8, Eq.(7): the infimum is over the actual normalized separable states. In finite dimensions it is attained and finite; the certificates below retain attainment.
--   - `IsMinimizer`: PDF pp.12–15: a closest separable state, including feasibility.
--   - `DistanceFamily`: PDF pp.8–10: coherent distance family on finite registers of every dimension.
--   - `IsSubstate`: PDF p.8: the subnormalized PSD domain required by F4 and F5a, including zero.
--   - `UnitaryInvariantDistance`: PDF p.8, F2: unitary invariance on normalized density matrices.
--   - `F3`: PDF p.8, F3: normalized partial-trace monotonicity. The blocks flag selects the subnormalized PSD extension used in Theorem 2, PDF p.10, Eq.(18).
--   - `F5b`: PDF p.9, proof-used F5b: the ancillary projector is onto a UNIT vector.
--   - `CompleteProjectors`: PDF p.8: a complete orthogonal family of Hermitian projectors.
--   - `F5a`: PDF p.8, F5a: block additivity on the subnormalized domain.
--   - `ProductComplete`: PDF p.4, Eq.(1): the source's complete product-Kraus idealization. This predicate does not identify separable operations with physical LOCC.
--   - `rectangularKrausBranch`: PDF pp.4,6: unnormalized outcome state.
--   - `rectangularKrausProbability`: PDF p.6: branch probability.
--   - `normalizedBranch`: PDF p.6: positive-probability outcome normalization; never used at zero probability.
--   - `MeasureConditions`: PDF pp.6–7, E1–E3, for the source's explicit product-Kraus operations. Zero-probability outcomes are omitted before evaluating a normalized state.
--   - `FiniteSchmidtExpansion`: PDF pp.12–14: finite Schmidt data, permitting zero weights and unequal local dimensions.
--   - `finiteSchmidtVector`: PDF p.14, Eq.(33): the vector constructed from its Schmidt expansion.
--   - `schmidtDiagonal`: PDF p.13: the explicitly proposed Schmidt-diagonal comparison state.
--   - `finiteSchmidtEntropyNats`: PDF pp.12–14: Schmidt entropy in nats, with 0 log 0 = 0.
--   - `kernelG`: PDF p.13, Eqs.(27)–(30): continuous diagonal value and zero-weight boundary. The source's sentence g(p,p)=1 is read only for p>0.
--   - `formationNats`: PDF p.7, Eq.(6): the finite pure-ensemble convex roof (creation/formation), in nats.
--   - `buresGenerator`: PDF p.17: the actual Bures-generated quantity is 2 minus twice ROOT fidelity.
--   - `buresEntanglement`: PDF pp.8,17: Bures distance to the separable set, for the generator actually printed.
--   - `entanglementIndicator`: PDF p.19: the indicator of entanglement.
--   - `groupedStateProduct`: PDF p.11: product of possibly different-dimensional inputs, across the grouped cut.
--   - `qubitAngle`: PDF p.22, Eq.(49): a qubit ray parameterized by its polar angle and phase.
--   - `mixingAmplitude`: PDF p.21, Eq.(48): 16 amplitudes using 15 angles; the last product is empty.
--   - `angleState`: PDF pp.21–22, Eqs.(47)–(49): the complete 79-angle two-qubit parameterization. The first 15 entries are mixing angles; each term then uses 4 local ray angles.
--   - `HasPureProductDecomposition`: PDF p.20: bounded finite pure-product decomposition.
--   - `qubitMatrixUnit`: PDF pp.23–24: matrix units in the ordered two-qubit computational basis.
--   - `bellBasisVector`: PDF p.23, Eqs.(57)–(58): Phi+, Phi-, Psi+, Psi-, in that order.
--   - `exampleOneInput`: PDF p.23, Eq.(54).
--   - `exampleOneMinimum`: PDF p.23, Eq.(55): the actual constructed comparison matrix.
--   - `correlated`: PDF p.24, Eq.(63): complex maximally correlated two-qubit family.
--   - `correlatedMinimum`: PDF pp.23–24, Eqs.(60),(64): the diagonal comparison state.
--   - `exampleTwoInput`: PDF p.23, Eq.(59).
--   - `correlatedEigenvalue`: Corrected eigenvalues for PDF p.24, Eq.(66), determined by Eq.(63). Printed 1-4A(1-A)-|B|^2 is changed to (2A-1)^2+4|B|^2.
--   - `bellDiagonal`: PDF pp.16,33: Bell-diagonal density matrix with the specified four weights.
--   - `singletWernerState`: PDF p.25: Werner state with singlet weight F.
--   - `localBell`: PDF p.25: all maximally entangled two-qubit vectors via local unitaries.
--   - `twoQubitMaxEntangledFraction`: PDF p.25: optimized maximally-entangled overlap. On density inputs this real supremum ranges over a nonempty compact set and is attained.
--   - `wernerValue`: Corrected PDF p.25, Eq.(73): zero on the separable Werner regime.
--   - `bipartitionProductMatrix`: PDF p.34, Eq.(91): product across a specified nontrivial bipartition. The blocks may each have internal entanglement and arbitrary unequal dimensions.
--   - `IsMultipartiteBiseparable`: PDF pp.34–35, Eqs.(91)–(92): mixtures over ALL nontrivial bipartitions; this is biseparability, rather than full product separability (94).
--   - `partyKraus`: PDF p.35, Eq.(93): one product Kraus operator across all parties.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, https://arxiv.org/abs/quant-ph/9707035v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P49

/-!
Vedral–Plenio, quant-ph/9707035v2. Finite, nonempty local registers; natural logs.
Signed support-aware relative entropy, natural entropy, grouped binary products and
copies reuse the pinned accepted library. Remaining paper-local concepts have distinct
names where frozen short-name matches have different domains, units or meanings.
Source corrections and excluded claims are recorded in this unit's audit artifacts.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P04 (copies)
open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Eq.(7): the infimum is over the actual normalized separable states.
In finite dimensions it is attained and finite; the certificates below retain attainment. -/
def relativeEntanglementNats {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (sigma : Matrix (I × J) (I × J) ℂ) : EReal :=
  sInf {v | ∃ rho : Matrix (I × J) (I × J) ℂ,
    IsSeparableDensity rho ∧ v = relativeEntropy sigma rho}

/-- PDF pp.12–15: a closest separable state, including feasibility. -/
def IsMinimizer {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (sigma rho : Matrix (I × J) (I × J) ℂ) : Prop :=
  IsSeparableDensity rho ∧ ∀ tau, IsSeparableDensity tau →
    relativeEntropy sigma rho ≤ relativeEntropy sigma tau

/-- PDF pp.8–10: coherent distance family on finite registers of every dimension. -/
abbrev DistanceFamily := {I : Type} → [Fintype I] → [DecidableEq I] →
  Matrix I I ℂ → Matrix I I ℂ → EReal

/-- PDF p.8: the subnormalized PSD domain required by F4 and F5a, including zero. -/
def IsSubstate {I : Type} [Fintype I] (rho : Matrix I I ℂ) : Prop :=
  rho.PosSemidef ∧ rho.trace.re ≤ 1

/-- PDF p.8, F2: unitary invariance on normalized density matrices. -/
def UnitaryInvariantDistance (D : DistanceFamily) : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (sigma rho : Matrix I I ℂ), IsDensityMatrix sigma → IsDensityMatrix rho →
    ∀ U : Matrix.unitaryGroup I ℂ,
      D ((U : Matrix I I ℂ) * sigma * (U : Matrix I I ℂ)ᴴ)
        ((U : Matrix I I ℂ) * rho * (U : Matrix I I ℂ)ᴴ) = D sigma rho

/-- PDF p.8, F3: normalized partial-trace monotonicity. The blocks flag selects
the subnormalized PSD extension used in Theorem 2, PDF p.10, Eq.(18). -/
def F3 (D : DistanceFamily) (blocks : Bool := false) : Prop :=
  ∀ {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] (sigma rho : Matrix (I × J) (I × J) ℂ),
    (if blocks then IsSubstate sigma else IsDensityMatrix sigma) →
    (if blocks then IsSubstate rho else IsDensityMatrix rho) →
      D (traceLeft sigma) (traceLeft rho) ≤ D sigma rho

/-- PDF p.9, proof-used F5b: the ancillary projector is onto a UNIT vector. -/
def F5b (D : DistanceFamily) : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (sigma rho : Matrix I I ℂ), IsDensityMatrix sigma → IsDensityMatrix rho →
    ∀ {K : Type} [Fintype K] [DecidableEq K] [Nonempty K]
      (alpha : EuclideanSpace ℂ K), ‖alpha‖ = 1 →
      D (Matrix.kronecker sigma (pureDensity alpha))
        (Matrix.kronecker rho (pureDensity alpha)) = D sigma rho

/-- PDF p.8: a complete orthogonal family of Hermitian projectors. -/
def CompleteProjectors {I K : Type} [Fintype I] [Fintype K]
    [DecidableEq I] (P : K → Matrix I I ℂ) : Prop :=
  (∀ k, (P k).IsHermitian ∧ P k * P k = P k) ∧
    (∀ k l, k ≠ l → P k * P l = 0) ∧ ∑ k, P k = 1

/-- PDF p.8, F5a: block additivity on the subnormalized domain. -/
def F5a (D : DistanceFamily) : Prop :=
  ∀ {I K : Type} [Fintype I] [Fintype K] [DecidableEq I] [Nonempty I]
    (P : K → Matrix I I ℂ), CompleteProjectors P →
    ∀ sigma rho, IsDensityMatrix sigma → IsDensityMatrix rho →
      D (∑ k, P k * sigma * P k) (∑ k, P k * rho * P k) =
        ∑ k, D (P k * sigma * P k) (P k * rho * P k)

/-- PDF p.4, Eq.(1): the source's complete product-Kraus idealization.
This predicate does not identify separable operations with physical LOCC. -/
def ProductComplete {I J A B K : Type} [Fintype I] [Fintype J]
    [Fintype A] [Fintype B] [Fintype K] [DecidableEq I] [DecidableEq J]
    (L : K → Matrix A I ℂ) (R : K → Matrix B J ℂ) : Prop :=
  IsKrausFamily (fun k => Matrix.kronecker (L k) (R k))

/-- PDF pp.4,6: unnormalized outcome state. -/
def rectangularKrausBranch {I J K : Type} [Fintype I] [Fintype J]
    (V : K → Matrix J I ℂ) (sigma : Matrix I I ℂ) (k : K) : Matrix J J ℂ :=
  V k * sigma * (V k)ᴴ

/-- PDF p.6: branch probability. -/
def rectangularKrausProbability {I J K : Type} [Fintype I] [Fintype J]
    (V : K → Matrix J I ℂ) (sigma : Matrix I I ℂ) (k : K) : ℝ :=
  (rectangularKrausBranch V sigma k).trace.re

/-- PDF p.6: positive-probability outcome normalization; never used at zero probability. -/
def normalizedBranch {I J K : Type} [Fintype I] [Fintype J]
    (V : K → Matrix J I ℂ) (sigma : Matrix I I ℂ) (k : K) : Matrix J J ℂ :=
  ((rectangularKrausProbability V sigma k)⁻¹ : ℂ) • rectangularKrausBranch V sigma k

/-- PDF pp.6–7, E1–E3, for the source's explicit product-Kraus operations.
Zero-probability outcomes are omitted before evaluating a normalized state. -/
def MeasureConditions {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (E : Matrix (I × J) (I × J) ℂ → EReal) : Prop :=
  (∀ sigma, IsDensityMatrix sigma → (E sigma = 0 ↔ IsSeparableDensity sigma)) ∧
  (∀ sigma, IsDensityMatrix sigma →
    ∀ U : Matrix.unitaryGroup I ℂ, ∀ V : Matrix.unitaryGroup J ℂ,
      E (conjSuperop (Matrix.kronecker (U : Matrix I I ℂ) (V : Matrix J J ℂ)) sigma) =
        E sigma) ∧
  (∀ {K : Type} [Fintype K] (L : K → Matrix I I ℂ) (R : K → Matrix J J ℂ),
    ProductComplete L R → ∀ sigma, IsDensityMatrix sigma →
      let V := fun k => Matrix.kronecker (L k) (R k)
      (∑ k, if 0 < rectangularKrausProbability V sigma k then
        (rectangularKrausProbability V sigma k : EReal) * E (normalizedBranch V sigma k) else 0) ≤
          E sigma)

/-- PDF pp.12–14: finite Schmidt data, permitting zero weights and unequal local dimensions. -/
structure FiniteSchmidtExpansion (I J K : Type) [Fintype I] [Fintype J] [Fintype K] where
  weight : K → ℝ
  nonnegative : ∀ k, 0 ≤ weight k
  total : ∑ k, weight k = 1
  left : K → EuclideanSpace ℂ I
  right : K → EuclideanSpace ℂ J
  left_orthonormal : Orthonormal ℂ left
  right_orthonormal : Orthonormal ℂ right

/-- PDF p.14, Eq.(33): the vector constructed from its Schmidt expansion. -/
def finiteSchmidtVector {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    (s : FiniteSchmidtExpansion I J K) : EuclideanSpace ℂ (I × J) :=
  WithLp.toLp 2 fun p => ∑ k, (Real.sqrt (s.weight k) : ℂ) * s.left k p.1 * s.right k p.2

/-- PDF p.13: the explicitly proposed Schmidt-diagonal comparison state. -/
def schmidtDiagonal {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    (s : FiniteSchmidtExpansion I J K) : Matrix (I × J) (I × J) ℂ :=
  ∑ k, (s.weight k : ℂ) • Matrix.kronecker (pureDensity (s.left k)) (pureDensity (s.right k))

/-- PDF pp.12–14: Schmidt entropy in nats, with 0 log 0 = 0. -/
def finiteSchmidtEntropyNats {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    (s : FiniteSchmidtExpansion I J K) : ℝ := -∑ k, s.weight k * Real.log (s.weight k)

/-- PDF p.13, Eqs.(27)–(30): continuous diagonal value and zero-weight boundary.
The source's sentence g(p,p)=1 is read only for p>0. -/
def kernelG (p q : ℝ) : ℝ :=
  if p = 0 ∨ q = 0 then 0 else
    if p = q then 1 else Real.sqrt (p * q) * Real.log (q / p) / (q - p)

/-- PDF p.7, Eq.(6): the finite pure-ensemble convex roof (creation/formation), in nats. -/
def formationNats {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (sigma : Matrix (I × J) (I × J) ℂ) : EReal :=
  sInf {v | ∃ m : ℕ, ∃ w : Fin m → ℝ, ∃ psi : Fin m → EuclideanSpace ℂ (I × J),
    (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧ (∀ k, ‖psi k‖ = 1) ∧
    sigma = ∑ k, (w k : ℂ) • pureDensity (psi k) ∧
    v = ((∑ k, w k * entropy (traceLeft (pureDensity (psi k))) : ℝ) : EReal)}

/-- PDF p.17: the actual Bures-generated quantity is 2 minus twice ROOT fidelity. -/
def buresGenerator {I : Type} [Fintype I] [DecidableEq I]
    (sigma rho : Matrix I I ℂ) : ℝ := 2 - 2 * rootFidelity sigma rho

/-- PDF pp.8,17: Bures distance to the separable set, for the generator actually printed. -/
def buresEntanglement {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (sigma : Matrix (I × J) (I × J) ℂ) : EReal :=
  sInf {v | ∃ rho : Matrix (I × J) (I × J) ℂ, IsSeparableDensity rho ∧
    v = (buresGenerator sigma rho : EReal)}

/-- PDF p.19: the indicator of entanglement. -/
def entanglementIndicator {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (sigma : Matrix (I × J) (I × J) ℂ) : EReal :=
  if IsSeparableDensity sigma then 0 else 1

/-- PDF p.11: product of possibly different-dimensional inputs, across the grouped cut. -/
def groupedStateProduct {T : Type} [Fintype T] {I J : T → Type}
    (sigma : ∀ t, Matrix (I t × J t) (I t × J t) ℂ) :
    Matrix ((∀ t, I t) × (∀ t, J t)) ((∀ t, I t) × (∀ t, J t)) ℂ :=
  fun p q => ∏ t, sigma t (p.1 t,p.2 t) (q.1 t,q.2 t)

/-- Sanity: zero weights do not receive the positive diagonal continuation. -/
example (q : ℝ) : kernelG 0 q = 0 := by simp [kernelG]

/-- Sanity: equal positive weights give the divided difference's continuation. -/
example : kernelG (1 / 2) (1 / 2) = 1 := by norm_num [kernelG]

/-- Sanity: the empty tensor product is the scalar unit, not a zero operator. -/
example {I J : Type} (sigma : Matrix (I × J) (I × J) ℂ)
    (p q : (Fin 0 → I) × (Fin 0 → J)) : copies sigma 0 p q = 1 := by
  simp [copies]

/-- Sanity: the zero positive operator has zero entropy and zero relative entropy to itself. -/
example {I : Type} [Fintype I] [DecidableEq I] :
    entropy (0 : Matrix I I ℂ) = 0 ∧ relativeEntropy (0 : Matrix I I ℂ) 0 = 0 := by
  simp [entropy, relativeEntropy,
    QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported, cfc_zero]

/-- PDF p.22, Eq.(49): a qubit ray parameterized by its polar angle and phase. -/
def qubitAngle (theta phase : ℝ) : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun b => if b then (Real.sin theta : ℂ) * Complex.exp ((phase : ℂ) * Complex.I)
    else (Real.cos theta : ℂ)

/-- PDF p.21, Eq.(48): 16 amplitudes using 15 angles; the last product is empty. -/
def mixingAmplitude (angle : Fin 15 → ℝ) (i : Fin 16) : ℝ :=
  Real.sin (if h : i.val = 0 then Real.pi / 2 else angle ⟨i.val - 1, by omega⟩) *
    ∏ j : Fin 15, if i.val ≤ j.val then Real.cos (angle j) else 1

/-- PDF pp.21–22, Eqs.(47)–(49): the complete 79-angle two-qubit parameterization.
The first 15 entries are mixing angles; each term then uses 4 local ray angles. -/
def angleState (a : Fin 79 → ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ∑ i : Fin 16, ((mixingAmplitude (fun j => a ⟨j.val, by omega⟩) i)^2 : ℂ) •
    Matrix.kronecker
      (pureDensity (qubitAngle (a ⟨15 + 4*i.val, by omega⟩) (a ⟨16 + 4*i.val, by omega⟩)))
      (pureDensity (qubitAngle (a ⟨17 + 4*i.val, by omega⟩) (a ⟨18 + 4*i.val, by omega⟩)))

/-- PDF p.20: bounded finite pure-product decomposition. -/
def HasPureProductDecomposition {I J : Type} [Fintype I] [Fintype J]
    (rho : Matrix (I × J) (I × J) ℂ) (bound : ℕ) : Prop :=
  ∃ m : ℕ, m ≤ bound ∧ ∃ w : Fin m → ℝ,
    ∃ a : Fin m → EuclideanSpace ℂ I, ∃ b : Fin m → EuclideanSpace ℂ J,
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, ‖a i‖ = 1 ∧ ‖b i‖ = 1) ∧
    rho = ∑ i, (w i : ℂ) • Matrix.kronecker (pureDensity (a i)) (pureDensity (b i))

/-- PDF pp.23–24: matrix units in the ordered two-qubit computational basis. -/
def qubitMatrixUnit (a b c d : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.single (a,b) (c,d) 1

/-- PDF p.23, Eqs.(57)–(58): Phi+, Phi-, Psi+, Psi-, in that order. -/
def bellBasisVector (i : Fin 4) : EuclideanSpace ℂ (Bool × Bool) :=
  let c : ℂ := (Real.sqrt 2)⁻¹
  ![c • (ket (false,false) + ket (true,true)),
    c • (ket (false,false) - ket (true,true)),
    c • (ket (false,true) + ket (true,false)),
    c • (ket (false,true) - ket (true,false))] i

/-- PDF p.23, Eq.(54). -/
def exampleOneInput (t : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (t : ℂ) • pureDensity (bellBasisVector 0) + ((1-t : ℝ) : ℂ) • qubitMatrixUnit false true false true

/-- PDF p.23, Eq.(55): the actual constructed comparison matrix. -/
def exampleOneMinimum (t : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ((t/2*(1-t/2) : ℝ) : ℂ) •
    (qubitMatrixUnit false false false false + qubitMatrixUnit false false true true +
      qubitMatrixUnit true true false false + qubitMatrixUnit true true true true) +
    (((1-t/2)^2 : ℝ) : ℂ) • qubitMatrixUnit false true false true +
    ((t^2/4 : ℝ) : ℂ) • qubitMatrixUnit true false true false

/-- PDF p.24, Eq.(63): complex maximally correlated two-qubit family. -/
def correlated (a : ℝ) (b : ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (a : ℂ) • qubitMatrixUnit false false false false +
    b • qubitMatrixUnit false false true true + conj b • qubitMatrixUnit true true false false +
    ((1-a : ℝ) : ℂ) • qubitMatrixUnit true true true true

/-- PDF pp.23–24, Eqs.(60),(64): the diagonal comparison state. -/
def correlatedMinimum (a : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (a : ℂ) • qubitMatrixUnit false false false false +
    ((1-a : ℝ) : ℂ) • qubitMatrixUnit true true true true

/-- PDF p.23, Eq.(59). -/
def exampleTwoInput (t : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (t : ℂ) • pureDensity (bellBasisVector 0) + ((1-t : ℝ) : ℂ) • qubitMatrixUnit false false false false

/-- Corrected eigenvalues for PDF p.24, Eq.(66), determined by Eq.(63).
Printed 1-4A(1-A)-|B|^2 is changed to (2A-1)^2+4|B|^2. -/
def correlatedEigenvalue (a : ℝ) (b : ℂ) (plus : Bool) : ℝ :=
  (1 + (if plus then 1 else -1) * Real.sqrt ((2*a-1)^2 + 4*Complex.normSq b)) / 2

/-- PDF pp.16,33: Bell-diagonal density matrix with the specified four weights. -/
def bellDiagonal (p : Fin 4 → ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ∑ i, (p i : ℂ) • pureDensity (bellBasisVector i)

/-- PDF p.25: Werner state with singlet weight F. -/
def singletWernerState (f : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (f : ℂ) • pureDensity (bellBasisVector 3) + (( (1-f)/3 : ℝ) : ℂ) • (1-pureDensity (bellBasisVector 3))

/-- PDF p.25: all maximally entangled two-qubit vectors via local unitaries. -/
def localBell (U V : Matrix.unitaryGroup Bool ℂ) : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 ((Matrix.kronecker (U : Matrix Bool Bool ℂ) (V : Matrix Bool Bool ℂ)).mulVec
    (WithLp.ofLp (bellBasisVector 0)))

/-- PDF p.25: optimized maximally-entangled overlap. On density inputs this real
supremum ranges over a nonempty compact set and is attained. -/
def twoQubitMaxEntangledFraction (sigma : Matrix (Bool × Bool) (Bool × Bool) ℂ) : ℝ :=
  sSup {v | ∃ U V : Matrix.unitaryGroup Bool ℂ,
    v = effectProb (pureDensity (localBell U V)) sigma}

/-- Corrected PDF p.25, Eq.(73): zero on the separable Werner regime. -/
def wernerValue (f : ℝ) : ℝ :=
  if f ≤ 1/2 then 0 else f * Real.log f + (1-f)*Real.log (1-f) + Real.log 2

/-- PDF p.34, Eq.(91): product across a specified nontrivial bipartition.
The blocks may each have internal entanglement and arbitrary unequal dimensions. -/
def bipartitionProductMatrix {N : ℕ} (d : Fin N → ℕ) (S : Finset (Fin N))
    (X : Matrix (∀ i : {i // i ∈ S}, Fin (d i.val))
      (∀ i : {i // i ∈ S}, Fin (d i.val)) ℂ)
    (Y : Matrix (∀ i : {i // i ∉ S}, Fin (d i.val))
      (∀ i : {i // i ∉ S}, Fin (d i.val)) ℂ) :
    Matrix (∀ i, Fin (d i)) (∀ i, Fin (d i)) ℂ :=
  fun p q => X (fun i => p i.val) (fun i => q i.val) *
    Y (fun i => p i.val) (fun i => q i.val)

/-- PDF pp.34–35, Eqs.(91)–(92): mixtures over ALL nontrivial bipartitions;
this is biseparability, rather than full product separability (94). -/
def IsMultipartiteBiseparable {N : ℕ} (d : Fin N → ℕ)
    (rho : Matrix (∀ i, Fin (d i)) (∀ i, Fin (d i)) ℂ) : Prop :=
  ∃ m : ℕ, ∃ w : Fin m → ℝ, ∃ S : Fin m → Finset (Fin N),
    ∃ X : ∀ k, Matrix (∀ i : {i // i ∈ S k}, Fin (d i.val))
      (∀ i : {i // i ∈ S k}, Fin (d i.val)) ℂ,
    ∃ Y : ∀ k, Matrix (∀ i : {i // i ∉ S k}, Fin (d i.val))
      (∀ i : {i // i ∉ S k}, Fin (d i.val)) ℂ,
    (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
    (∀ k, (S k).Nonempty ∧ S k ≠ Finset.univ) ∧
    (∀ k, IsDensityMatrix (X k) ∧ IsDensityMatrix (Y k)) ∧
    rho = ∑ k, (w k : ℂ) • bipartitionProductMatrix d (S k) (X k) (Y k)

/-- PDF p.35, Eq.(93): one product Kraus operator across all parties. -/
def partyKraus {N : ℕ} {d : Fin N → ℕ}
    (A : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    Matrix (∀ i, Fin (d i)) (∀ i, Fin (d i)) ℂ :=
  fun p q => ∏ i, A i (p i) (q i)

/-- Sanity: the zero-angle qubit is |0>. -/
example : qubitAngle 0 0 false = 1 ∧ qubitAngle 0 0 true = 0 := by
  simp [qubitAngle]

/-- Sanity: zero off-diagonal coherence leaves exactly the diagonal comparison matrix. -/
example (a : ℝ) : correlated a 0 = correlatedMinimum a := by
  simp [correlated, correlatedMinimum]

/-- Sanity: the corrected Werner value at its separable boundary is zero. -/
example : wernerValue (1/2) = 0 := by simp [wernerValue]

/-- Sanity: scalar relative entropy can be negative on unequal subnormalizations. -/
example : ((Real.log (1/2) : ℝ) : EReal) < 0 := by
  exact_mod_cast Real.log_neg (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)

end QAlgorithms.Papers.Independent.Intakenext100.P42


