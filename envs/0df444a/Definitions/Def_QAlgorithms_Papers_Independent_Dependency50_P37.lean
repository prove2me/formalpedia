-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37
-- name    : QAlgorithms_Papers_Independent_Dependency50_P37
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:06:44.543488+00:00
-- url     : https://prove2.me/theorems/cee429f0-0cd0-4c02-9bbd-2ed95a4570a9
-- title:
--   Definitions for Zero-error communication under discrete-time Markovian dynamics
-- statement:
--   The objects the formalized statements of *Zero-error communication under discrete-time Markovian dynamics* (arXiv:2402.18703) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Dynamics`
--   - `OrthogonalOutputs`: PDF p.12: orthogonality of positive operators is equivalent to tr(AB)=0.
--   - `firstTime`: PDF pp.2,19 (B.9): positive-time index; empty infimum in WithTop Nat is infinity.
--   - `quantumTime`
--   - `classicalTime`
--   - `assistedTime`
--   - `EventuallyQuantumScrambling`
--   - `EventuallyClassicalScrambling`
--   - `Mixing`: PDF pp.3,10: convergence on all operators, not just states.
--   - `Ergodic`: PDF p.10: channel ergodicity is uniqueness of its invariant density.
--   - `MixingWithFaithfulState`: PDF p.10: mixing with a faithful invariant density, including NONUNITAL channels. The accepted P26.Primitive means peripheral=scalar identity for unital maps; it cannot replace this general source definition.
--   - `EntanglementBreaking`: PDF pp.10–11: all finite reference systems. Accepted separable-positive means a finite positive product decomposition, normalized automatically on channel outputs.
--   - `AsymptoticallyEntanglementBreaking`: PDF pp.3,11: limits along unbounded times. Strict subsequences retain stationary and periodic limits; this is not the derived set of distinct channel powers.
--   - `channelMatrix`: PDF pp.3,9–10: matrix-unit representation of the linear channel on all operators. Entry ((i,j),(k,l)) is Phi(E_kl)_{ij}; on channels this representation has exactly Phi's linear action. This adapts the accepted matrix-superoperator interface.
--   - `peripheralEigenvalues`: PDF p.16: distinct peripheral eigenvalues, without multiplicity.
--   - `PeripheralDecomposition`: PDF pp.3,10,17 eqs.(3)–(6): actual orthogonal decomposition of chi(Phi). H0 is the orthogonal complement of these mutually orthogonal isometric blocks. All active factors are positive dimensional. The equality is to the computed peripheral space; this is not unrelated block data assumed to have capacity formulas.
--   - `peripheralBlockDimensionSum`: PDF pp.3–4: sum of LEFT block dimensions, not a direct-sum superoperator. The accepted P26.blockSum constructs a map and is a different source concept.
--   - `blockMaximum`: The finite family is nonempty and positive, so this Nat supremum is its actual maximum.
--   - `IsOperatorAlgebra`: PDF pp.11,26: multiplicative closure; channel systems already contain identity and adjoints.
--   - `multiplicativeDomain`: PDF p.11: both defining multiplicative-domain identities.
--   - `stableMultiplicativeDomain`
--   - `ColumnStochastic`: PDF pp.19,28: real nonnegative entries and unit column sums.
--   - `cduc`: PDF p.28 (C.14): the CDUC map.
--   - `duc`: PDF p.28 (C.15): the DUC map transposes off-diagonal input entries.
--   - `matrixPeripheral`: PDF p.28: classical peripheral vector span. Stochastic peripheral eigenvalues are semisimple, so its dimension counts their algebraic multiplicities.
--   - `MatrixStrictlyPositive`: PDF p.28 (C.16): entrywise strict positivity.
--   - `MatrixScrambling`: PDF p.28 (C.16): overlapping support for every pair of columns.
--   - `MatrixMixing`: PDF p.28 (C.16): convergence form of the simple-one/no-other-peripheral spectrum criterion, equivalent for stochastic matrices.
--   - `MatrixPrimitive`: PDF p.28 (C.16): mixing with a full-support invariant probability vector.
--   - `matrixClassicalTime`
--   - `matrixWielandtTime`
--   - `StrictlyPositive`: PDF pp.23–24: strict positivity applies to CP maps even without trace preservation.
--   - `wielandtTime`
--   - `sharpMatrix`: PDF pp.20,31 eq.(18): sharp family used at d>=2. Column 0 goes to the last row, column 1 splits between rows 0 and d-1, column j>=2 goes to row j-1.
--   - `scramblingBound`: PDF pp.3,21,31: ceil((d^2-2d+2)/2), with real arithmetic before the ceiling.
--   - `wielandtBound`: PDF p.31: (d-1)^2+1 = d^2-2d+2 for positive d.
--   - `normalizedPositivePart`: PDF p.16: normalized Jordan part; the encoding theorem asserts trace positivity.
--   - `InvariantSubspace`: PDF pp.21–22, C.1: invariance on all supported densities.
--   - `LeastInvariantSubspace`: PDF pp.21–23: corrected C.1 interpretation used in C.2/C.3's proof: the least NONZERO invariant subspace, itself invariant and nonzero. Inclusion in zero would make the printed definition globally unsatisfiable.
--   - `OrthogonalProjectorOnto`: PDF p.21: the unique orthogonal projector onto S, specified by defining properties.
--   - `krausWordSpace`: PDF p.21 (C.3): ordered length-n Kraus words.
--   - `leftMultiplySpace`: PDF pp.21–22: LEFT multiplication P S, not two-sided compression.
--   - `FullyIrreducible`: PDF p.24 (C.6): all nontrivial equivalent projections, and every positive scalar. For projections, equality of traces is equivalent to Murray–von Neumann equivalence.
--   - `adjoint`: PDF p.9: trace-dual formula, equal to the HS adjoint for channels.
--   - `exampleC8`: PDF p.25 (C.8): displayed four-dimensional channel.
--   - `exampleC13Kraus`: PDF p.27 (C.13), credited there to the example after [25, Theorem 3.9].
--   - `exampleC13`
--   - `krausDilation`: PDF p.32: canonical Stinespring isometry of a normalized Kraus family. The accepted complementaryChannel takes the partial trace of V X V*, so its (i,j) entry is Tr(K_j* K_i X). The printed reversed Kraus indices would instead transpose this CP complement. Kraus normalization makes this an isometry; no minimality assumption is needed for its capacity.
--   - `ContinuousQMS`: PDF p.4 (1.6): continuous finite-dimensional QMS, equivalently Lindbladian-generated. Only nonnegative times are constrained; time zero is the identity.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, https://arxiv.org/abs/2402.18703v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-! Singh–Rahaman–Datta, arXiv:2402.18703v3. Page numbers are PDF pages.
New definitions are paper-local; matching interfaces are imported from the pinned library. Capacities are one-shot and exactly zero error;
powers are compositions; logarithms are base two. Indices start at 1, with infinity
for an empty hitting set. Compilation and independent moderation are pending. -/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)
open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)
open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)
open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

abbrev Dynamics (d : ℕ) := Superop (Fin d) (Fin d)

/-- PDF p.12: orthogonality of positive operators is equivalent to tr(AB)=0. -/
def OrthogonalOutputs {I : Type*} [Fintype I]
    (A B : Matrix I I ℂ) : Prop := (A * B).trace = 0

/-- PDF pp.2,19 (B.9): positive-time index; empty infimum in WithTop Nat is infinity. -/
def firstTime (P : ℕ → Prop) : WithTop ℕ :=
  sInf ((fun n : ℕ => (n : WithTop ℕ)) '' {n | 0 < n ∧ P n})

def quantumTime {d : ℕ} (Phi : Dynamics d) : WithTop ℕ :=
  firstTime fun n => quantumCapacity (Nat.iterate Phi n) = 0

def classicalTime {d : ℕ} (Phi : Dynamics d) : WithTop ℕ :=
  firstTime fun n => classicalCapacity (Nat.iterate Phi n) = 0

def assistedTime {d : ℕ} (Phi : Dynamics d) : WithTop ℕ :=
  firstTime fun n => assistedCapacity (Nat.iterate Phi n) = 0

def EventuallyQuantumScrambling {d : ℕ} (Phi : Dynamics d) : Prop :=
  ∃ n : ℕ, 0 < n ∧ quantumCapacity (Nat.iterate Phi n) = 0

def EventuallyClassicalScrambling {d : ℕ} (Phi : Dynamics d) : Prop :=
  ∃ n : ℕ, 0 < n ∧ classicalCapacity (Nat.iterate Phi n) = 0

/-- PDF pp.3,10: convergence on all operators, not just states. -/
def Mixing {d : ℕ} (Phi : Dynamics d) : Prop :=
  ∃ rho : Operator d, IsDensityMatrix rho ∧
    ∀ X : Operator d, Tendsto (fun n : ℕ => Nat.iterate Phi n X) atTop (nhds (X.trace • rho))

/-- PDF p.10: channel ergodicity is uniqueness of its invariant density. -/
def Ergodic {d : ℕ} (Phi : Dynamics d) : Prop :=
  ∃! rho : Operator d, IsDensityMatrix rho ∧ Phi rho = rho

/-- PDF p.10: mixing with a faithful invariant density, including NONUNITAL channels.
The accepted P26.Primitive means peripheral=scalar identity for unital maps;
it cannot replace this general source definition. -/
def MixingWithFaithfulState {d : ℕ} (Phi : Dynamics d) : Prop :=
  Mixing Phi ∧ ∃ rho : Operator d, IsDensityMatrix rho ∧ rho.PosDef ∧ Phi rho = rho

/-- PDF pp.10–11: all finite reference systems. Accepted separable-positive
means a finite positive product decomposition, normalized automatically on channel outputs. -/
def EntanglementBreaking {d : ℕ} (Phi : Dynamics d) : Prop :=
  ∀ a : ℕ, 0 < a →
    ∀ rho : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ,
      IsDensityMatrix rho → Entanglement.IsSeparablePositive (idTensorSuperop Phi rho)

/-- PDF pp.3,11: limits along unbounded times. Strict subsequences retain stationary
and periodic limits; this is not the derived set of distinct channel powers. -/
def AsymptoticallyEntanglementBreaking {d : ℕ} (Phi : Dynamics d) : Prop :=
  ∀ Psi : Dynamics d,
    (∃ t : ℕ → ℕ, StrictMono t ∧ ∀ X,
      Tendsto (fun n => Nat.iterate Phi (t n) X) atTop (nhds (Psi X))) →
    EntanglementBreaking Psi

/-- PDF pp.3,9–10: matrix-unit representation of the linear channel on all operators.
Entry ((i,j),(k,l)) is Phi(E_kl)_{ij}; on channels this representation has exactly
Phi's linear action. This adapts the accepted matrix-superoperator interface. -/
def channelMatrix {d : ℕ} (Phi : Dynamics d) : Information100.P26.Map d :=
  fun ij kl => Phi (Matrix.single kl.1 kl.2 1) ij.1 ij.2

/-- PDF p.16: distinct peripheral eigenvalues, without multiplicity. -/
def peripheralEigenvalues {d : ℕ} (Phi : Dynamics d) : Set ℂ :=
  {z | ‖z‖ = 1 ∧ ∃ X : Operator d, X ≠ 0 ∧ Phi X = z • X}

/-- PDF pp.3,10,17 eqs.(3)–(6): actual orthogonal decomposition of chi(Phi).
H0 is the orthogonal complement of these mutually orthogonal isometric blocks.
All active factors are positive dimensional. The equality is to the computed
peripheral space; this is not unrelated block data assumed to have capacity formulas. -/
structure PeripheralDecomposition {d : ℕ} (Phi : Dynamics d) where
  K : ℕ
  nonempty : 0 < K
  left : Fin K → ℕ
  right : Fin K → ℕ
  leftPositive : ∀ k, 0 < left k
  rightPositive : ∀ k, 0 < right k
  rho : (k : Fin K) → Operator (right k)
  density : ∀ k, IsDensityMatrix (rho k)
  faithful : ∀ k, (rho k).PosDef
  V : (k : Fin K) → Matrix (Fin d) (Fin (left k) × Fin (right k)) ℂ
  isometry : ∀ k, (V k)ᴴ * V k = 1
  orthogonal : ∀ k l, k ≠ l → (V k)ᴴ * V l = 0
  space : ∀ A : Operator d, A ∈ Information100.P26.peripheral (channelMatrix Phi) ↔
    ∃ X : (k : Fin K) → Operator (left k),
      A = ∑ k, V k * Matrix.kronecker (X k) (rho k) * (V k)ᴴ

/-- PDF pp.3–4: sum of LEFT block dimensions, not a direct-sum superoperator.
The accepted P26.blockSum constructs a map and is a different source concept. -/
def peripheralBlockDimensionSum {d : ℕ} {Phi : Dynamics d} (D : PeripheralDecomposition Phi) : ℕ :=
  ∑ k, D.left k

/-- The finite family is nonempty and positive, so this Nat supremum is its actual maximum. -/
def blockMaximum {d : ℕ} {Phi : Dynamics d} (D : PeripheralDecomposition Phi) : ℕ :=
  Finset.univ.sup D.left

/-- PDF pp.11,26: multiplicative closure; channel systems already contain identity and adjoints. -/
def IsOperatorAlgebra {d : ℕ} (S : Submodule ℂ (Operator d)) : Prop :=
  (1 : Operator d) ∈ S ∧ ∀ A ∈ S, ∀ B ∈ S, A * B ∈ S

/-- PDF p.11: both defining multiplicative-domain identities. -/
def multiplicativeDomain {d : ℕ} (Phi : Dynamics d) : Set (Operator d) :=
  {A | ∀ X, Phi (A * X) = Phi A * Phi X ∧ Phi (X * A) = Phi X * Phi A}

def stableMultiplicativeDomain {d : ℕ} (Phi : Dynamics d) : Set (Operator d) :=
  {A | ∀ n : ℕ, 0 < n → A ∈ multiplicativeDomain (Nat.iterate Phi n)}

/-- PDF pp.19,28: real nonnegative entries and unit column sums. -/
def ColumnStochastic {d : ℕ} (A : Operator d) : Prop :=
  (∀ i j, (A i j).im = 0 ∧ 0 ≤ (A i j).re) ∧ ∀ j, ∑ i, A i j = 1

/-- PDF p.28 (C.14): the CDUC map. -/
def cduc {d : ℕ} (A B : Operator d) : Dynamics d :=
  fun X i j => if i = j then ∑ k, A i k * X k k else B i j * X i j

/-- PDF p.28 (C.15): the DUC map transposes off-diagonal input entries. -/
def duc {d : ℕ} (A C : Operator d) : Dynamics d :=
  fun X i j => if i = j then ∑ k, A i k * X k k else C i j * X j i

/-- PDF p.28: classical peripheral vector span. Stochastic peripheral eigenvalues
are semisimple, so its dimension counts their algebraic multiplicities. -/
def matrixPeripheral {d : ℕ} (A : Operator d) : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
  Submodule.span ℂ {v | ∃ z : ℂ, ‖z‖ = 1 ∧ Matrix.toEuclideanLin A v = z • v}

/-- PDF p.28 (C.16): entrywise strict positivity. -/
def MatrixStrictlyPositive {d : ℕ} (A : Operator d) : Prop :=
  ∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re

/-- PDF p.28 (C.16): overlapping support for every pair of columns. -/
def MatrixScrambling {d : ℕ} (A : Operator d) : Prop :=
  ∀ i j, ∃ k, 0 < (A k i).re * (A k j).re

/-- PDF p.28 (C.16): convergence form of the simple-one/no-other-peripheral spectrum
criterion, equivalent for stochastic matrices. -/
def MatrixMixing {d : ℕ} (A : Operator d) : Prop :=
  ∃ v : Fin d → ℂ, (∀ i, (v i).im = 0 ∧ 0 ≤ (v i).re) ∧ (∑ i, v i) = 1 ∧
    ∀ x : Fin d → ℂ, Tendsto (fun n : ℕ => Matrix.mulVec (A ^ n) x)
      atTop (nhds ((∑ i, x i) • v))

/-- PDF p.28 (C.16): mixing with a full-support invariant probability vector. -/
def MatrixPrimitive {d : ℕ} (A : Operator d) : Prop :=
  MatrixMixing A ∧ ∃ v : Fin d → ℂ,
    (∀ i, (v i).im = 0 ∧ 0 < (v i).re) ∧ (∑ i, v i) = 1 ∧ Matrix.mulVec A v = v

def matrixClassicalTime {d : ℕ} (A : Operator d) : WithTop ℕ :=
  firstTime fun n => MatrixScrambling (A ^ n)

def matrixWielandtTime {d : ℕ} (A : Operator d) : WithTop ℕ :=
  firstTime fun n => MatrixStrictlyPositive (A ^ n)

/-- PDF pp.23–24: strict positivity applies to CP maps even without trace preservation. -/
def StrictlyPositive {d : ℕ} (Phi : Dynamics d) : Prop :=
  ∀ A : Operator d, A.PosSemidef → A ≠ 0 → (Phi A).PosDef

def wielandtTime {d : ℕ} (Phi : Dynamics d) : WithTop ℕ :=
  firstTime fun n => StrictlyPositive (Nat.iterate Phi n)

/-- PDF pp.20,31 eq.(18): sharp family used at d>=2. Column 0 goes to the last
row, column 1 splits between rows 0 and d-1, column j>=2 goes to row j-1. -/
def sharpMatrix (d : ℕ) : Operator d :=
  fun i j => if j.val = 0 then (if i.val + 1 = d then 1 else 0)
    else if j.val = 1 then (if i.val = 0 ∨ i.val + 1 = d then 1 / 2 else 0)
    else if i.val + 1 = j.val then 1 else 0

/-- PDF pp.3,21,31: ceil((d^2-2d+2)/2), with real arithmetic before the ceiling. -/
def scramblingBound (d : ℕ) : ℕ :=
  Nat.ceil (((d : ℝ) ^ 2 - 2 * d + 2) / 2)

/-- PDF p.31: (d-1)^2+1 = d^2-2d+2 for positive d. -/
def wielandtBound (d : ℕ) : ℕ := (d - 1) ^ 2 + 1

/-- PDF p.16: normalized Jordan part; the encoding theorem asserts trace positivity. -/
def normalizedPositivePart {d : ℕ} (A : Operator d) : Operator d :=
  (positivePart A).trace⁻¹ • positivePart A

/-- PDF pp.21–22, C.1: invariance on all supported densities. -/
def InvariantSubspace {d : ℕ} (Phi : Dynamics d) (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) : Prop :=
  ∀ rho, IsDensityMatrix rho → operatorRange rho ≤ S → operatorRange (Phi rho) ≤ S

/-- PDF pp.21–23: corrected C.1 interpretation used in C.2/C.3's proof: the least
NONZERO invariant subspace, itself invariant and nonzero. Inclusion in zero would
make the printed definition globally unsatisfiable. -/
def LeastInvariantSubspace {d : ℕ} (Phi : Dynamics d)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) : Prop :=
  S ≠ ⊥ ∧ InvariantSubspace Phi S ∧
    ∀ T, T ≠ ⊥ → InvariantSubspace Phi T → S ≤ T

/-- PDF p.21: the unique orthogonal projector onto S, specified by defining properties. -/
def OrthogonalProjectorOnto {d : ℕ} (P : Operator d)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) : Prop :=
  Pᴴ = P ∧ P * P = P ∧ operatorRange P = S

/-- PDF p.21 (C.3): ordered length-n Kraus words. -/
def krausWordSpace {d p : ℕ} (K : Fin p → Operator d) (n : ℕ) :
    Submodule ℂ (Operator d) :=
  Submodule.span ℂ (Set.range fun w : Fin n → Fin p => (List.ofFn fun i => K (w i)).prod)

/-- PDF pp.21–22: LEFT multiplication P S, not two-sided compression. -/
def leftMultiplySpace {d : ℕ} (P : Operator d) (S : Submodule ℂ (Operator d)) :
    Submodule ℂ (Operator d) :=
  Submodule.span ℂ {A | ∃ B ∈ S, A = P * B}

/-- PDF p.24 (C.6): all nontrivial equivalent projections, and every positive scalar.
For projections, equality of traces is equivalent to Murray–von Neumann equivalence. -/
def FullyIrreducible {d : ℕ} (Phi : Dynamics d) : Prop :=
  ∀ P Q : Operator d,
    Pᴴ = P → P * P = P → P ≠ 0 → P ≠ 1 →
    Qᴴ = Q → Q * Q = Q → Q ≠ 0 → Q ≠ 1 → P.trace = Q.trace →
    ∀ t : ℝ, 0 < t → ¬ (((t : ℂ) • Q - Phi P).PosSemidef)

/-- PDF p.9: trace-dual formula, equal to the HS adjoint for channels. -/
def adjoint {d : ℕ} (Phi : Dynamics d) : Dynamics d :=
  fun X i j => (X * Phi (Matrix.single j i 1)).trace

/-- PDF p.25 (C.8): displayed four-dimensional channel. -/
def exampleC8 : Dynamics 4 :=
  fun X => Matrix.diagonal ![(X 0 0 + X 1 1) / 2, (X 1 1 + X 2 2) / 2,
    (X 2 2 + X 3 3) / 2, (X 3 3 + X 0 0) / 2]

/-- PDF p.27 (C.13), credited there to the example after [25, Theorem 3.9]. -/
def exampleC13Kraus : Fin 3 → Operator 3 :=
  ![((Real.sqrt 2 : ℂ)⁻¹) • !![0, 0, 1; 0, 0, 1; 0, 0, 0],
    ((Real.sqrt 2 : ℂ)⁻¹) • !![1, 0, 0; -1, 0, 0; 0, 0, 0],
    !![0, 0, 0; 0, 0, 0; 0, 1, 0]]

def exampleC13 : Dynamics 3 := krausApply exampleC13Kraus

/-- PDF p.32: canonical Stinespring isometry of a normalized Kraus family.
The accepted complementaryChannel takes the partial trace of V X V*, so its
(i,j) entry is Tr(K_j* K_i X). The printed reversed Kraus indices would instead
transpose this CP complement. Kraus normalization makes this an isometry;
no minimality assumption is needed for its capacity. -/
def krausDilation {d e p : ℕ} (K : Fin p → Matrix (Fin e) (Fin d) ℂ) :
    Matrix (Fin e × Fin p) (Fin d) ℂ := fun ij k => K ij.2 ij.1 k

/-- PDF p.4 (1.6): continuous finite-dimensional QMS, equivalently Lindbladian-generated.
Only nonnegative times are constrained; time zero is the identity. -/
structure ContinuousQMS (d : ℕ) where
  map : ℝ → Dynamics d
  channel : ∀ t, 0 ≤ t → IsChannel (map t)
  zero : map 0 = id
  add : ∀ s t, 0 ≤ s → 0 ≤ t → map (s + t) = map s ∘ map t
  continuous : ∀ X, ContinuousOn (fun t => map t X) (Set.Ici 0)

/-! Definition-level sanity examples. -/

example {d : ℕ} (Phi : Dynamics d) (X : Operator d) : Nat.iterate Phi 0 X = X := rfl

example {d : ℕ} (Phi : Dynamics d) (X : Operator d) : Nat.iterate Phi 1 X = Phi X := rfl

example : firstTime (fun _ => False) = ⊤ := by simp [firstTime]

example : sharpMatrix 2 = !![0, 1 / 2; 1, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sharpMatrix]

example {d : ℕ} : IsOperatorAlgebra (⊤ : Submodule ℂ (Operator d)) := by
  simp [IsOperatorAlgebra]

example {d : ℕ} (Phi : Dynamics d) (i j k l : Fin d) :
    channelMatrix Phi (i, j) (k, l) = Phi (Matrix.single k l 1) i j := rfl

example {d e p : ℕ} (K : Fin p → Matrix (Fin e) (Fin d) ℂ)
    (i : Fin e) (j : Fin p) (k : Fin d) : krausDilation K (i, j) k = K j i k := rfl

end QAlgorithms.Papers.Independent.Dependency50.P37


