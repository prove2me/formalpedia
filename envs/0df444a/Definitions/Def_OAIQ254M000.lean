-- Prove2me | Definitions.Def_OAIQ254M000
-- name    : OAIQ254M000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:46:39.983107+00:00
-- url     : https://prove2.me/theorems/91b21233-bb50-4235-a8e5-1050473abaf6
-- title:
--   Definitions bundle OAIQ254M000 of the split of OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 938 declarations of OpenAI's Lean: 551 definitions, 16 inductive types or structures, 15 instances and 356 theorems. The definitions and types are `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.canonicalSideMass`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.orderEntropyRate`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.orderNativeDegree`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveGibbs.physicalPotential`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveGibbs.splitCoordinateWeight`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveGibbs.splitLogNormalizer`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveGibbs.splitNormalizer`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveGibbs.splitPotential`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchProbability`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.orderCounts`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.orderLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.orderMass`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.add`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.exact`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.inv`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.lower`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.mul`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.neg`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.ofBounds`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.upper`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.LogWitness`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.contains`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.logCoefficients`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.logResult`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.logVariable`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.pad`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.traceHead`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.initial`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.replicate`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.restrict`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.toWitness` and 527 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixFields_Arithmetic_CommonDimensions`, `MatrixFields_Certificates_CertificatesReplay`, `MatrixFields_Certificates_Terminal1_1_6`, `MatrixFields_Construction_ActiveSums`, `MatrixFields_Construction_CompleteWordPair`, `MatrixFields_Construction_ComplexPolynomialWitnessProduct`, `MatrixFields_Construction_ComplexRectangularASI`, `MatrixFields_Construction_GroupAmbientDegree`, `MatrixFields_Construction_InitialFamily`, `MatrixFields_Construction_InitialHistories`, `MatrixFields_Construction_InitialState`, `MatrixFields_Construction_JointAPFree`, `MatrixFields_Construction_JointCoarseReorder`, `MatrixFields_Construction_JointCompatibilityIncidence`, `MatrixFields_Construction_JointLossCounts`, `MatrixFields_Construction_JointMaskedAssignment`, `MatrixFields_Construction_ShapeEncoding`, `MatrixFields_Entropy_GroupBranchLaws`, `MatrixFields_Entropy_InitialEntropy`, `MatrixFields_Entropy_InitialLeafRates`, `MatrixFields_Entropy_JointAmbientEntropy`, `MatrixFields_Entropy_JointExtractionRates`, `MatrixFields_Entropy_ParametersHalfLaws`, `MatrixFields_Entropy_StageCLaw`, `MatrixFields_Entropy_TerminalStatisticLaws`, `MatrixFields_Entropy_ZeroLeafRateFormula`, `MatrixFields_Extraction_ComplexRationalTypes`, `MatrixFields_Extraction_InitialHash`, `MatrixFields_Extraction_JointExtraction`, `MatrixFields_Extraction_JointMaskedSelection`, `MatrixFields_Extraction_JointPairClassWindows`, `MatrixFields_Extraction_JointTypeCounts`, `MatrixFields_Histories_GroupOrbitCount`, `MatrixFields_Histories_GroupOrbitTransport`, `MatrixFields_Histories_HistoryChildLaws`, `MatrixFields_Histories_HistoryGroupCore`, `MatrixFields_Histories_HistoryPositions`, `MatrixFields_Histories_HistoryRecoveryBudget`, `MatrixFields_Histories_HistorySourceAssignment`, `MatrixFields_Histories_InheritedMaskMargins`, `MatrixFields_Histories_InverseLinearRecovery`, `MatrixFields_Histories_ScheduledPositivity`, `MatrixFields_Parameters_GroupSelectionParameters`, `MatrixFields_Parameters_JointOrdinaryPopulationSelection`, `MatrixFields_Parameters_JointPopulation`, `MatrixFields_Parameters_JointPopulationMixedCompatibility`, `MatrixFields_Parameters_NativeCapacity`, `MatrixFields_Parameters_ParametersWeights`, `MatrixFields_Parameters_PopulationCounts`, `MatrixFields_Tensors_CWCompleteStatistics`, `MatrixFields_Tensors_ComplexDotPairing`, `MatrixFields_Tensors_TerminalRelabel`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ254M002`, `OAIQ254M003`, `OAIQ254M004`, `OAIQ254M005` and `OAIQ254M006`; the statements `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.log_center_lipschitz`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.weighted_shape_fiber_count`, `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.normalized_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.entropyTerm_ball`; the proofs of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.log_center_lipschitz`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.weighted_shape_fiber_count` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.entropyTerm_ball`.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/LinearAlgebra at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ254_MF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_ComplexDotPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def power (T : Tensor K X Y Z) (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

@[simp] theorem directSum_matching {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (i : ι) (x : X) (y : Y) (z : Z) :
    directSum T (i, x) (i, y) (i, z) = T i x y z := by
  simp [directSum]

@[simp] theorem rankAtMost_zero : RankAtMost (0 : Tensor K X Y Z) 0 := by
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  funext x y z
  simp

theorem RankAtMost.map {L : Type*} [CommSemiring L]
    (f : K →+* L) {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (fun x y z => f (T x y z)) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => f (a i x), fun i y => f (b i y), fun i z => f (c i z), ?_⟩
  funext x y z
  simp [rankOne]

theorem rankAtMost_sum_rankOne {ι : Type*} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) := by
  classical
  refine ⟨fun i => a ((Fintype.equivFin ι).symm i),
    fun i => b ((Fintype.equivFin ι).symm i),
    fun i => c ((Fintype.equivFin ι).symm i), ?_⟩
  funext x y z
  exact ((Fintype.equivFin ι).symm.sum_comp
    (fun i => rankOne (a i) (b i) (c i) x y z)).symm

theorem RankAtMost.product {U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (Tensor.product T S) (r * s) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  let aa : (Fin r × Fin s) → (X × U) → K := fun i x => a i.1 x.1 * d i.2 x.2
  let bb : (Fin r × Fin s) → (Y × V) → K := fun i y => b i.1 y.1 * e i.2 y.2
  let cc : (Fin r × Fin s) → (Z × W) → K := fun i z => c i.1 z.1 * f i.2 z.2
  have heq : Tensor.product
      (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (fun u v w => ∑ j, rankOne (d j) (e j) (f j) u v w) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    simp only [Tensor.product, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [rankOne, aa, bb, cc]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  let aa : (Fin n → Fin r) → (Fin n → X) → K := fun f x => ∏ i, a (f i) (x i)
  let bb : (Fin n → Fin r) → (Fin n → Y) → K := fun f y => ∏ i, b (f i) (y i)
  let cc : (Fin n → Fin r) → (Fin n → Z) → K := fun f z => ∏ i, c (f i) (z i)
  have heq : Tensor.power (fun x y z => ∑ j, rankOne (a j) (b j) (c j) x y z) n =
      fun x y z => ∑ f, rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [Tensor.power, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi_const, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_rankOne (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (a : X → K) (b : Y → K) (c : Z → K) :
    restrict A B C (rankOne a b c) =
      rankOne (fun x' => ∑ x, A x' x * a x)
        (fun y' => ∑ y, B y' y * b y)
        (fun z' => ∑ z, C z' z * c z) := by
  funext x' y' z'
  simp only [restrict, rankOne]
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem restrict_sum {ι : Type*} [Fintype ι]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : ι → Tensor K X Y Z) :
    restrict A B C (fun x y z => ∑ i, T i x y z) =
      fun x' y' z' => ∑ i, restrict A B C (T i) x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  calc
    (∑ x, ∑ y, ∑ z, ∑ i, A x' x * B y' y * C z' z * T i x y z) =
        ∑ x, ∑ y, ∑ i, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z :=
      Finset.sum_comm

theorem RankAtMost.restrict {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : RankAtMost (Tensor.restrict A B C T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x' => ∑ x, A x' x * a i x,
    fun i y' => ∑ y, B y' y * b i y,
    fun i z' => ∑ z, C z' z * c i z, ?_⟩
  rw [restrict_sum]
  funext x' y' z'
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (congrFun (congrFun (restrict_rankOne A B C (a i) (b i) (c i)) x') y') z'

end Algebra

section Pullback
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0)
      (fun z' z => if z = fz z' then 1 else 0) T := by
  classical
  funext x y z
  simp [pullback, restrict, ite_mul, mul_ite]

theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y),
    fun i z => c i (fz z), rfl⟩

end Pullback

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def diagonal (ι : Type*) [DecidableEq ι] : Tensor K ι ι ι :=
  fun i j k => if i = j ∧ i = k then 1 else 0

theorem diagonal_rankAtMost (ι : Type*) [Fintype ι] [DecidableEq ι] :
    RankAtMost (diagonal (K := K) ι) (Fintype.card ι) := by
  let a : ι → ι → K := fun i j => if i = j then 1 else 0
  have heq : diagonal (K := K) ι =
      fun x y z => ∑ i, rankOne (a i) (a i) (a i) x y z := by
    funext x y z
    simp [diagonal, rankOne, a, mul_ite, ite_and]
    split_ifs <;> simp_all
  rw [heq]
  exact rankAtMost_sum_rankOne a a a

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' X'' Y'' Z'' : Type*} [CommSemiring K]

def composeRestrictionMatrix [Fintype X']
    (D : X'' → X' → K) (A : X' → X → K) : X'' → X → K :=
  fun x'' x => ∑ x', D x'' x' * A x' x

theorem sum_three_mul [Fintype X] [Fintype Y] [Fintype Z]
    (a : X → K) (b : Y → K) (c : Z → K) (t : K) :
    (∑ x, a x) * (∑ y, b y) * (∑ z, c z) * t =
      ∑ x, ∑ y, ∑ z, a x * b y * c z * t := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]

theorem sum_six_comm [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (f : X' → Y' → Z' → X → Y → Z → K) :
    (∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z, f x' y' z' x y z) =
      ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z', f x' y' z' x y z := by
  calc
    _ = ∑ p : X' × Y' × Z', ∑ q : X × Y × Z,
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ q : X × Y × Z, ∑ p : X' × Y' × Z',
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

theorem sum_interleaved_triples {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X → Y → Z → U → V → W → K) :
    (∑ x, ∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
      ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w, f x y z u v w := by
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
        ∑ y, ∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        (∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w) =
            ∑ u, ∑ z, ∑ v, ∑ w, f x y z u v w := by
          apply Finset.sum_congr rfl
          intro u hu
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem restrict_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : X'' → X' → K) (E : Y'' → Y' → K) (F : Z'' → Z' → K)
    (T : Tensor K X Y Z) :
    restrict D E F (restrict A B C T) =
      restrict (composeRestrictionMatrix D A) (composeRestrictionMatrix E B)
        (composeRestrictionMatrix F C) T := by
  funext x'' y'' z''
  unfold restrict composeRestrictionMatrix
  calc
    _ = ∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z,
        D x'' x' * E y'' y' * F z'' z' *
          (A x' x * B y' y * C z' z * T x y z) := by
      simp only [Finset.mul_sum]
    _ = ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z',
        D x'' x' * E y'' y' * F z'' z' *
          (A x' x * B y' y * C z' z * T x y z) := sum_six_comm _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      rw [sum_three_mul]
      apply Finset.sum_congr rfl
      intro x' hx'
      apply Finset.sum_congr rfl
      intro y' hy'
      apply Finset.sum_congr rfl
      intro z' hz'
      ring

theorem restrict_product {U V W U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : U' → U → K) (E : V' → V → K) (F : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    restrict (fun (x : X' × U') (u : X × U) => A x.1 u.1 * D x.2 u.2)
      (fun (y : Y' × V') (v : Y × V) => B y.1 v.1 * E y.2 v.2)
      (fun (z : Z' × W') (w : Z × W) => C z.1 w.1 * F z.2 w.2) (product T S) =
      product (restrict A B C T) (restrict D E F S) := by
  funext x' y' z'
  simp only [restrict, product, Fintype.sum_prod_type]
  calc
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * D x'.2 u) * (B y'.1 y * E y'.2 v) *
          (C z'.1 z * F z'.2 w) * (T x y z * S u v w) :=
      sum_interleaved_triples _
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * B y'.1 y * C z'.1 z * T x y z) *
          (D x'.2 u * E y'.2 v * F z'.2 w * S u v w) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = _ := by
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]

end Algebra

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.Replication

variable {K I R X Y Z X' Y' Z' : Type*} [CommSemiring K]

theorem restrict_directSum
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] [Fintype Z]
    (T : I → Tensor K X Y Z)
    (a : I → X' → X → K) (b : I → Y' → Y → K) (c : I → Z' → Z → K) :
    Tensor.restrict
      (fun x s => if x.1 = s.1 then a x.1 x.2 s.2 else 0)
      (fun y s => if y.1 = s.1 then b y.1 y.2 s.2 else 0)
      (fun z s => if z.1 = s.1 then c z.1 z.2 s.2 else 0)
      (Tensor.directSum T) = Tensor.directSum (fun i => Tensor.restrict (a i) (b i) (c i) (T i)) := by
  classical
  funext x y z
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
        ite_and, ite_mul, mul_ite]
    · simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
        ite_and, ite_mul, mul_ite, hik]
  · simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
      ite_and, ite_mul, mul_ite, hij]
    intro hjk hik
    exact (hij (hik.trans hjk.symm)).elim

theorem swap_replication [DecidableEq I] [DecidableEq R]
    (T : I → Tensor K X Y Z) :
    Tensor.pullback
      (fun x : I × (R × X) => (x.2.1, (x.1, x.2.2)))
      (fun y : I × (R × Y) => (y.2.1, (y.1, y.2.2)))
      (fun z : I × (R × Z) => (z.2.1, (z.1, z.2.2)))
      (Tensor.directSum (fun _ : R => Tensor.directSum T)) =
      Tensor.directSum (fun i => Tensor.directSum (fun _ : R => T i)) := by
  funext x y z
  simp only [Tensor.pullback, Tensor.directSum]
  split_ifs <;> simp_all

theorem repair_branches
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : I → Tensor K X Y Z) (Q : I → Tensor K X' Y' Z')
    (a : I → X' → (R × X) → K) (b : I → Y' → (R × Y) → K)
    (c : I → Z' → (R × Z) → K)
    (h : ∀ i, Tensor.restrict (a i) (b i) (c i)
      (Tensor.directSum (fun _ : R => T i)) = Q i) :
    ∃ (A : (I × X') → (R × (I × X)) → K)
      (B : (I × Y') → (R × (I × Y)) → K)
      (C : (I × Z') → (R × (I × Z)) → K),
      Tensor.restrict A B C (Tensor.directSum (fun _ : R => Tensor.directSum T)) =
        Tensor.directSum Q := by
  classical
  have hb := restrict_directSum (fun i => Tensor.directSum (fun _ : R => T i)) a b c
  simp_rw [h] at hb
  rw [← swap_replication T, Tensor.pullback_eq_restrict, Tensor.restrict_restrict] at hb
  exact ⟨_, _, _, hb⟩

end MatrixMultiplication.Replication

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_TerminalRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

def matrixCoefficients (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

end Tensor






namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X :=
  fun y z x => T x y z

theorem RankAtMost.cyclic {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) : RankAtMost (Tensor.cyclic T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, c, a, ?_⟩
  funext y z x
  simp only [Tensor.cyclic, rankOne]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Tensor
end MatrixMultiplication.Foundation

end




end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_CommonDimensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CommonDimensions

variable {K H : Type*} [CommSemiring K] [Fintype H] [DecidableEq H]

def familyProduct {X Y Z : H → Type*} (T : ∀ h, Tensor K (X h) (Y h) (Z h)) :
    Tensor K (∀ h, X h) (∀ h, Y h) (∀ h, Z h) :=
  fun x y z => ∏ h, T h (x h) (y h) (z h)

end MatrixMultiplication.CommonDimensions

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates

structure Ball where
  center : ℚ
  radius : ℚ
  deriving DecidableEq

namespace Ball

def Encloses (b : Ball) (x : ℝ) : Prop := |x - (b.center : ℝ)| ≤ (b.radius : ℝ)

def exact (q : ℚ) : Ball := ⟨q, 0⟩
def add (a b : Ball) : Ball := ⟨a.center + b.center, a.radius + b.radius⟩
def neg (a : Ball) : Ball := ⟨-a.center, a.radius⟩
def mul (a b : Ball) : Ball :=
  ⟨a.center * b.center,
    |a.center| * b.radius + |b.center| * a.radius + a.radius * b.radius⟩

def lower (b : Ball) : ℚ := b.center - b.radius
def upper (b : Ball) : ℚ := b.center + b.radius

def ofBounds (lo hi : ℚ) : Ball := ⟨(lo + hi) / 2, (hi - lo) / 2⟩

def inv (a : Ball) : Ball := ofBounds (1 / a.upper) (1 / a.lower)

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates.Replay

def contains (a b : Ball) : Bool :=
  decide (|a.center - b.center| + a.radius ≤ b.radius)

def traceHead (trace : List Ball) : Ball := trace.headD (.exact 0)

def checkPolynomial (t : Ball) : List ℚ → List Ball → Bool
  | [], [] => true
  | a :: as, b :: bs =>
      contains (Ball.add (.exact a) (Ball.mul t (traceHead bs))) b &&
        checkPolynomial t as bs
  | _, _ => false

def logCoefficients : List ℚ :=
  (List.range 24).map (fun i => 1 / (2 * (i : ℚ) + 1))

def pad (b : Ball) (error : ℚ) : Ball := ⟨b.center, b.radius + error⟩

def logVariable (m : ℚ) : ℚ := (m - 1) / (m + 1)

def normalizedLogBall (m : ℚ) (trace : List Ball) : Ball :=
  pad (Ball.mul (.exact (2 * logVariable m)) (traceHead trace)) (1 / 2 ^ 72)

end MatrixMultiplication.AllFieldCertificates.Replay

namespace MatrixMultiplication.CompactCertificate

structure NInterval where
  lo : ℕ
  hi : ℕ
  deriving DecidableEq, Repr

namespace NInterval

def zero : NInterval := ⟨0, 0⟩
def add (a b : NInterval) : NInterval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def mul (S : ℕ) (a b : NInterval) : NInterval :=
  ⟨a.lo * b.lo / S, a.hi * b.hi / S + 1⟩
def frac (S n d : ℕ) : NInterval := ⟨n * S / d, n * S / d + 1⟩

def oddHorner (S : ℕ) (t : NInterval) (start : ℕ) : ℕ → NInterval
  | 0 => zero
  | n + 1 => add (frac S 1 (2 * start + 1))
      (mul S t (oddHorner S t (start + 1) n))

end NInterval
end MatrixMultiplication.CompactCertificate

namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay

def scale : ℕ := 10 ^ 40

def logApprox (n d : ℕ) : NInterval :=
  let u := NInterval.frac scale (n - d) (n + d)
  NInterval.mul scale (NInterval.add u u)
    (NInterval.oddHorner scale (NInterval.mul scale u u) 0 24)

def NInterval.ball (a : NInterval) : Ball :=
  Ball.ofBounds ((a.lo : ℚ) / scale) ((a.hi : ℚ) / scale)

def normalized (n d : ℕ) : Ball := pad (logApprox n d).ball (1 / 2 ^ 72)

structure LogData where
  exponent : ℤ
  numerator : ℕ
  denominator : ℕ
  deriving DecidableEq

def logResult (two a : Ball) (w : LogData) : Ball :=
  pad (Ball.add (normalized w.numerator w.denominator)
    (Ball.mul (.exact w.exponent) two)) (a.radius / a.lower)

end MatrixMultiplication.CompactCertificate

namespace MatrixMultiplication.AllFieldCertificates.Replay
abbrev LogWitness := MatrixMultiplication.CompactCertificate.LogData
abbrev logResult := MatrixMultiplication.CompactCertificate.logResult

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointLossCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.JointLossCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω V I : Type*}

def randomLossCount (passing : Finset V) (bad : V → Ω → Prop) (ω : Ω) : ℕ := by
  classical
  exact (passing.filter (fun v => bad v ω)).card

def randomLossFraction (full passing : Finset V) (bad : V → Ω → Prop) (ω : Ω) : ℝ :=
  (randomLossCount passing bad ω : ℝ) / (full.card : ℝ)

def targetBad (orbits : Finset I) (full passing : I → Finset V)
    (bad : I → V → Ω → Prop) (eligible : Ω → Prop) (N : ℝ) (ω : Ω) : Prop :=
  ¬ eligible ω ∨ ∃ i ∈ orbits, 1 / N < randomLossFraction (full i) (passing i) (bad i) ω

end MatrixMultiplication.JointLossCounts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointAPFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.JointAPFree

def natSet (N : ℕ) : Finset ℕ := (rothNumberNat_spec N).choose

theorem natSet_subset (N : ℕ) : natSet N ⊆ Finset.range N :=
  (rothNumberNat_spec N).choose_spec.1

theorem natSet_threeAPFree (N : ℕ) : ThreeAPFree (natSet N : Set ℕ) :=
  (rothNumberNat_spec N).choose_spec.2.2

theorem mem_natSet_lt {N a : ℕ} (ha : a ∈ natSet N) : a < N :=
  Finset.mem_range.mp (natSet_subset N ha)

theorem natCast_injective_below {M a b : ℕ} (ha : a < M) (hb : b < M)
    (hab : (a : ZMod M) = (b : ZMod M)) : a = b := by
  have h := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using h

theorem add_lt_modulus {M a b : ℕ} (ha : a < M / 2) (hb : b < M / 2) :
    a + b < M := by
  have h := Nat.div_mul_le_self M 2
  omega

def modularSet (M : ℕ) : Finset (ZMod M) :=
  (natSet (M / 2)).image (fun a : ℕ => (a : ZMod M))

theorem modularSet_threeAPFree (M : ℕ) :
    ThreeAPFree (modularSet M : Set (ZMod M)) := by
  intro a ha b hb c hc habc
  change a ∈ (natSet (M / 2)).image (fun n : ℕ => (n : ZMod M)) at ha
  change b ∈ (natSet (M / 2)).image (fun n : ℕ => (n : ZMod M)) at hb
  change c ∈ (natSet (M / 2)).image (fun n : ℕ => (n : ZMod M)) at hc
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
  have hac := add_lt_modulus (mem_natSet_lt ha') (mem_natSet_lt hc')
  have hbb := add_lt_modulus (mem_natSet_lt hb') (mem_natSet_lt hb')
  have hnat : a' + c' = b' + b' := natCast_injective_below hac hbb (by
    simpa only [Nat.cast_add] using habc)
  exact congrArg (fun n : ℕ => (n : ZMod M)) (natSet_threeAPFree (M / 2) ha' hb' hc' hnat)

theorem modularSet_hashAP (M : ℕ) :
    ∀ x ∈ modularSet M, ∀ y ∈ modularSet M, ∀ z ∈ modularSet M,
      x + y = 2 * z → x = z ∧ y = z := by
  intro x hx y hy z hz h
  have h' : x + y = z + z := by simpa only [two_mul] using h
  exact ⟨modularSet_threeAPFree M hx hz hy h',
    ((modularSet_threeAPFree M).eq_right hx hz hy h').symm⟩

end MatrixMultiplication.JointAPFree

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointExtractionRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section






namespace MatrixMultiplication.JointExtractionRates

open Filter
open scoped BigOperators Topology

def hashModulus (H : ℝ) (N : ℕ) : ℕ :=
  37 ^ (⌊(N : ℝ) * H / Real.log 37⌋₊ + 1)

end MatrixMultiplication.JointExtractionRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointMaskedSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.JointHashing

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {P R : Type*} [Fintype P] [CommRing R]

def dot (v w : P → R) : R := ∑ i, v i * w i

@[simp] theorem dot_add_right (v w u : P → R) : dot v (w + u) = dot v w + dot v u := by
  simp [dot, mul_add, Finset.sum_add_distrib]

@[simp] theorem dot_sub_right (v w u : P → R) : dot v (w - u) = dot v w - dot v u := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem dot_add_left (v w u : P → R) : dot (v + w) u = dot v u + dot w u := by
  simp [dot, add_mul, Finset.sum_add_distrib]

@[simp] theorem dot_sub_left (v w u : P → R) : dot (v - w) u = dot v u - dot w u := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

abbrev Sample (P R : Type*) := (P → R) × R × R

def xHash (s : Sample P R) (I : P → R) := s.2.1 + dot s.1 I
def yHash (s : Sample P R) (J : P → R) := s.2.2 + dot s.1 J

def zHash (two : Rˣ) (s : Sample P R) (S K : P → R) :=
  (↑(two⁻¹) : R) * (s.2.1 + s.2.2 + dot s.1 (S - K))

def Survives (U : Set R) (I J : P → R) (s : Sample P R) : Prop :=
  xHash s I = yHash s J ∧ xHash s I ∈ U

theorem hash_relation (two : Rˣ) (htwo : (two : R) = 2)
    (s : Sample P R) (I J K S : P → R) (hs : I + J + K = S) :
    xHash s I + yHash s J = 2 * zHash two s S K := by
  have hSK : S - K = I + J := by rw [← hs]; abel
  rw [zHash, ← htwo, ← mul_assoc]
  rw [Units.mul_inv, one_mul, hSK, dot_add_right]
  simp only [xHash, yHash]
  ring

theorem full_survival_iff (two : Rˣ) (htwo : (two : R) = 2)
    (U : Set R)
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample P R) (I J K S : P → R) (hs : I + J + K = S) :
    (xHash s I ∈ U ∧ yHash s J ∈ U ∧ zHash two s S K ∈ U) ↔
      Survives U I J s := by
  have hr := hash_relation two htwo s I J K S hs
  constructor
  · rintro ⟨hx, hy, hz⟩
    obtain ⟨h1, h2⟩ := hAP _ hx _ hy _ hz hr
    exact ⟨h1.trans h2.symm, hx⟩
  · rintro ⟨hxy, hx⟩
    have hz : zHash two s S K = xHash s I := by
      have hh : (two : R) * zHash two s S K = (two : R) * xHash s I := by
        rw [htwo, ← hr, hxy]; ring
      exact two.isUnit.mul_left_cancel hh
    exact ⟨hx, hxy ▸ hx, hz ▸ hx⟩

omit [CommRing R] in
@[simp] theorem sample_card [Fintype R] :
    Fintype.card (Sample P R) = Fintype.card R ^ Fintype.card P * Fintype.card R ^ 2 := by
  simp [Sample, pow_two]

theorem small_nat_isUnit (k n : ℕ) (hn : 0 < n) (hn16 : n ≤ 16) :
    IsUnit (n : ZMod (37 ^ k)) := by
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)).mpr
  intro h
  have := Nat.le_of_dvd hn h
  omega

end MatrixMultiplication.JointHashing





noncomputable section

namespace MatrixMultiplication.JointCoarseHashing

attribute [local instance] Classical.propDecidable

abbrev Word (P : Type*) := P → Fin 17
abbrev Triple (P : Type*) := Word P × Word P × Word P

variable {P : Type*}

def HasSupportSum (S : P → ℕ) (e : Triple P) : Prop :=
  ∀ p, (e.1 p).val + (e.2.1 p).val + (e.2.2 p).val = S p

def castWord (k : ℕ) (w : Word P) : P → ZMod (37 ^ k) :=
  fun p => (w p).val

def twoUnit (k : ℕ) : (ZMod (37 ^ k))ˣ :=
  (JointHashing.small_nat_isUnit k 2 (by decide) (by decide)).unit

theorem twoUnit_coe (k : ℕ) : (twoUnit k : ZMod (37 ^ k)) = 2 := by
  exact (JointHashing.small_nat_isUnit k 2 (by decide) (by decide)).unit_spec

theorem supportSum_cast (k : ℕ) (S : P → ℕ) (e : Triple P)
    (he : HasSupportSum S e) :
    castWord k e.1 + castWord k e.2.1 + castWord k e.2.2 =
      fun p => (S p : ZMod (37 ^ k)) := by
  funext p
  have h := congrArg (fun n : ℕ => (n : ZMod (37 ^ k))) (he p)
  simpa only [Nat.cast_add, Pi.add_apply, castWord] using h

section FiniteHashing

variable [Fintype P]

abbrev Sample (P : Type*) (k : ℕ) := JointHashing.Sample P (ZMod (37 ^ k))

def Survives (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) (s : Sample P k) : Prop :=
  JointHashing.Survives (U : Set (ZMod (37 ^ k))) (castWord k e.1) (castWord k e.2.1) s

theorem full_survival_iff (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (s : Sample P k) :
    (JointHashing.xHash s (castWord k e.1) ∈ U ∧
      JointHashing.yHash s (castWord k e.2.1) ∈ U ∧
      JointHashing.zHash (twoUnit k) s (fun p => (S p : ZMod (37 ^ k)))
        (castWord k e.2.2) ∈ U) ↔ Survives k U e s := by
  exact JointHashing.full_survival_iff (twoUnit k) (twoUnit_coe k)
    (U : Set (ZMod (37 ^ k))) hAP s (castWord k e.1) (castWord k e.2.1)
    (castWord k e.2.2) (fun p => (S p : ZMod (37 ^ k))) (supportSum_cast k S e he)

def SharesSide (e f : Triple P) : Prop :=
  f.1 = e.1 ∨ f.2.1 = e.2.1 ∨ f.2.2 = e.2.2

def ownEvent (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) : Finset (Sample P k) :=
  Finset.univ.filter (Survives k U e)

end FiniteHashing

end MatrixMultiplication.JointCoarseHashing






namespace MatrixMultiplication.JointOrdinarySelection

open JointCoarseHashing JointExtractionRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {P E : Type*}

def neighbors (ambient : Finset (Triple P)) (e : Triple P) : Finset (Triple P) :=
  ambient.filter (fun f => f ≠ e ∧ SharesSide e f)

@[simp] theorem mem_neighbors (ambient : Finset (Triple P)) (e f : Triple P) :
    f ∈ neighbors ambient e ↔ f ∈ ambient ∧ f ≠ e ∧ SharesSide e f := by
  simp only [neighbors, Finset.mem_filter]

section Finite

variable [Fintype P]

def Bad (k : ℕ) (U : Finset (ZMod (37 ^ k))) (ambient : Finset (Triple P))
    (e : Triple P) (s : Sample P k) : Prop :=
  ∃ f ∈ neighbors ambient e, Survives k U f s

def Good (k : ℕ) (U : Finset (ZMod (37 ^ k))) (ambient : Finset (Triple P))
    (e : Triple P) (s : Sample P k) : Prop :=
  Survives k U e s ∧ ¬ Bad k U ambient e s

def goodEvent (k : ℕ) (U : Finset (ZMod (37 ^ k))) (ambient : Finset (Triple P))
    (e : Triple P) : Finset (Sample P k) :=
  (ownEvent k U e).filter (fun s => ¬ Bad k U ambient e s)

@[simp] theorem mem_goodEvent (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (e : Triple P) (s : Sample P k) :
    s ∈ goodEvent k U ambient e ↔ Good k U ambient e s := by
  simp only [goodEvent, ownEvent, Finset.mem_filter, Finset.mem_univ, true_and, Good]

theorem good_excludes_neighbor (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (e f : Triple P) (s : Sample P k)
    (hg : Good k U ambient e s) (hf : f ∈ ambient) (hne : f ≠ e)
    (hshare : SharesSide e f) : ¬ Survives k U f s := by
  intro hs
  exact hg.2 ⟨f, (mem_neighbors ambient e f).2 ⟨hf, hne, hshare⟩, hs⟩

end Finite

def hashLevel (H : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) * H / Real.log 37⌋₊ + 1

def hashSet (H : ℝ) (N : ℕ) : Finset (ZMod (37 ^ hashLevel H N)) :=
  JointAPFree.modularSet (hashModulus H N)

theorem hashSet_AP (H : ℝ) (N : ℕ) :
    ∀ x ∈ hashSet H N, ∀ y ∈ hashSet H N, ∀ z ∈ hashSet H N,
      x + y = 2 * z → x = z ∧ y = z :=
  JointAPFree.modularSet_hashAP (hashModulus H N)

end MatrixMultiplication.JointOrdinarySelection






namespace MatrixMultiplication.JointMaskedSelection

open JointCoarseHashing JointExtractionRates

attribute [local instance] Classical.propDecidable

variable {P E O V : Type*}

structure OrbitData (P E O V : Type*) where
  ambient : Finset (Triple P)
  support : P → ℕ
  coarse : E → Triple P
  support_ambient : ∀ f ∈ ambient, HasSupportSum support f
  target_mem : ∀ e, coarse e ∈ ambient
  orbits : E → Finset O
  full : E → O → Finset V
  passing : E → O → Finset V
  full_pos : ∀ e, ∀ o ∈ orbits e, 0 < (full e o).card
  passing_subset : ∀ e, ∀ o ∈ orbits e, passing e o ⊆ full e o
  competitors : E → O → V → Finset (Triple P)
  competitor_mem : ∀ e, ∀ o ∈ orbits e, ∀ v ∈ passing e o,
    ∀ f ∈ competitors e o v, f ∈ ambient
  competitor_ne : ∀ e, ∀ o ∈ orbits e, ∀ v ∈ passing e o,
    ∀ f ∈ competitors e o v, f ≠ coarse e
  competitor_shares : ∀ e, ∀ o ∈ orbits e, ∀ v ∈ passing e o,
    ∀ f ∈ competitors e o v, SharesSide (coarse e) f

namespace OrbitData

def eligibilityCompetitors (d : OrbitData P E O V) (e : E) : Finset (Triple P) :=
  d.ambient.filter (fun f => f ≠ d.coarse e ∧ f.1 = (d.coarse e).1)

@[simp] theorem mem_eligibilityCompetitors (d : OrbitData P E O V) (e : E) (f : Triple P) :
    f ∈ d.eligibilityCompetitors e ↔
      f ∈ d.ambient ∧ f ≠ d.coarse e ∧ f.1 = (d.coarse e).1 := by
  simp only [eligibilityCompetitors, Finset.mem_filter]

section Finite

variable [Fintype P]

def variableBad (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (e : E) (o : O) (v : V) (s : Sample P k) : Prop :=
  ∃ f ∈ d.competitors e o v, Survives k U f s

def eligibilityGood (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (e : E) (s : Sample P k) : Prop :=
  ¬ ∃ f ∈ d.eligibilityCompetitors e, Survives k U f s

def Failure (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (N : ℝ) (e : E) (s : Sample P k) : Prop :=
  JointLossCounts.targetBad (d.orbits e) (d.full e) (d.passing e)
    (d.variableBad k U e) (d.eligibilityGood k U e) N s

def Good (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (N : ℝ) (e : E) (s : Sample P k) : Prop :=
  Survives k U (d.coarse e) s ∧ ¬ d.Failure k U N e s

def goodEvent (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (N : ℝ) (e : E) : Finset (Sample P k) :=
  (ownEvent k U (d.coarse e)).filter (fun s => ¬ d.Failure k U N e s)

@[simp] theorem mem_goodEvent (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) (s : Sample P k) :
    s ∈ d.goodEvent k U N e ↔ d.Good k U N e s := by
  simp only [goodEvent, ownEvent, Finset.mem_filter, Finset.mem_univ, true_and, Good]

end Finite

end OrbitData

end MatrixMultiplication.JointMaskedSelection

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCoarseReorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.JointCoarseReorder
open JointCoarseHashing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def tripleSide {P : Type*} (s : Fin 3) (t : Triple P) : Word P :=
  (Matrix.vecCons (t.1) (Matrix.vecCons (t.2.1) (Matrix.vecCons (t.2.2) Matrix.vecEmpty))) s

def reorder {P : Type*} (sigma : Equiv.Perm (Fin 3)) (t : Triple P) : Triple P :=
  (tripleSide (sigma 0) t, tripleSide (sigma 1) t, tripleSide (sigma 2) t)

@[simp] theorem tripleSide_reorder {P : Type*} (sigma : Equiv.Perm (Fin 3))
    (t : Triple P) (s : Fin 3) :
    tripleSide s (reorder sigma t) = tripleSide (sigma s) t := by
  fin_cases s <;> rfl

theorem reorder_injective {P : Type*} (sigma : Equiv.Perm (Fin 3)) :
    Function.Injective (reorder (P := P) sigma) := by
  intro t u h
  have hs (s : Fin 3) : tripleSide s t = tripleSide s u := by
    have hh := congrArg (tripleSide (sigma.symm s)) h
    simpa only [tripleSide_reorder, sigma.apply_symm_apply] using hh
  exact Prod.ext (hs 0) (Prod.ext (hs 1) (hs 2))

end MatrixMultiplication.JointCoarseReorder

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ComplexRectangularASI
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {F X Y Z : Type*} [Field F]

structure PolynomialApproximation (T : Tensor F X Y Z) (r d D : ℕ) where
  polynomial : Tensor (Polynomial F) X Y Z
  rank_bound : RankAtMost polynomial r
  vanishes : ∀ x y z k, k < d → (polynomial x y z).coeff k = 0
  leading : ∀ x y z, (polynomial x y z).coeff d = T x y z
  degree_bound : ∀ x y z, (polynomial x y z).degree ≤ D

namespace PolynomialApproximation

variable {T : Tensor F X Y Z} {r d D : ℕ}

def normalized (A : PolynomialApproximation T r d D) :
    Tensor (Polynomial F) X Y Z :=
  fun x y z => Classical.choose (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem polynomial_eq (A : PolynomialApproximation T r d D) (x : X) (y : Y) (z : Z) :
    A.polynomial x y z = Polynomial.X ^ d * A.normalized x y z :=
  Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem normalized_constant (A : PolynomialApproximation T r d D)
    (x : X) (y : Y) (z : Z) : (A.normalized x y z).coeff 0 = T x y z := by
  have h := A.leading x y z
  rw [A.polynomial_eq] at h
  simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, if_true, Nat.sub_self] using h

theorem power_polynomial_eq (A : PolynomialApproximation T r d D) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
    Tensor.power A.polynomial n x y z =
      Polynomial.X ^ (d * n) * Tensor.power A.normalized n x y z := by
  simp [Tensor.power, A.polynomial_eq, Finset.prod_mul_distrib, ← pow_mul]

def power (A : PolynomialApproximation T r d D) (n : ℕ) :
    PolynomialApproximation (Tensor.power T n) (r ^ n) (d * n) (D * n) where
  polynomial := Tensor.power A.polynomial n
  rank_bound := A.rank_bound.power n
  vanishes := by
    intro x y z k hk
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk, ite_false, if_false]
  leading := by
    intro x y z
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, if_true, Nat.sub_self,
      Tensor.power, Polynomial.coeff_zero_prod, A.normalized_constant]
  degree_bound := by
    intro x y z
    apply Polynomial.degree_le_of_natDegree_le
    calc
      (Tensor.power A.polynomial n x y z).natDegree ≤
          ∑ i, (A.polynomial (x i) (y i) (z i)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin n, D := by
        apply Finset.sum_le_sum
        intro i hi
        exact Polynomial.natDegree_le_of_degree_le (A.degree_bound (x i) (y i) (z i))
      _ = D * n := by simp [Nat.mul_comm]

end PolynomialApproximation

end Tensor
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

def batchCount (R k : ℕ) : ℕ := (R + k - 1) / k

@[simp] theorem batchCount_zero (k : ℕ) : batchCount 0 k = 0 := by
  unfold batchCount
  by_cases hk : k = 0
  · simp [hk]
  · apply Nat.div_eq_of_lt
    omega

def batchRank (k r : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => batchCount (batchRank k r t) k * r

@[simp] theorem batchRank_zero (k r : ℕ) : batchRank k r 0 = 1 := rfl

@[simp] theorem batchRank_succ (k r t : ℕ) :
    batchRank k r (t + 1) = batchCount (batchRank k r t) k * r := rfl

end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section ConstantRestriction

variable {F X Y Z X' Y' Z' : Type*} [CommSemiring F]
variable [Fintype X] [Fintype Y] [Fintype Z]

def restrictPolynomial (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) :
    Tensor (Polynomial F) X' Y' Z' :=
  restrict (fun x' x => Polynomial.C (A x' x))
    (fun y' y => Polynomial.C (B y' y))
    (fun z' z => Polynomial.C (C z' z)) P

@[simp] theorem restrictPolynomial_coeff (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) (k : ℕ)
    (x' : X') (y' : Y') (z' : Z') :
    (restrictPolynomial A B C P x' y' z').coeff k =
      restrict A B C (fun x y z => (P x y z).coeff k) x' y' z' := by
  simp only [restrictPolynomial, restrict, Polynomial.finsetSum_coeff,
    mul_assoc, Polynomial.coeff_C_mul]

theorem RankAtMost.restrictPolynomial {P : Tensor (Polynomial F) X Y Z} {r : ℕ}
    (hP : RankAtMost P r) (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) : RankAtMost (restrictPolynomial A B C P) r :=
  hP.restrict (fun x' x => Polynomial.C (A x' x))
    (fun y' y => Polynomial.C (B y' y))
    (fun z' z => Polynomial.C (C z' z))

theorem restrictPolynomial_degree_le (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) (D : ℕ)
    (hdegree : ∀ x y z, (P x y z).degree ≤ D)
    (x' : X') (y' : Y') (z' : Z') :
    (restrictPolynomial A B C P x' y' z').degree ≤ D := by
  apply (Polynomial.degree_le_iff_coeff_zero _ _).2
  intro k hk
  rw [restrictPolynomial_coeff]
  have hzero (x : X) (y : Y) (z : Z) : (P x y z).coeff k = 0 :=
    (Polynomial.degree_le_iff_coeff_zero _ _).1 (hdegree x y z) k hk
  simp only [restrict, hzero, mul_zero, Finset.sum_const_zero]

end ConstantRestriction

namespace PolynomialApproximation

variable {F X Y Z X' Y' Z' : Type*} [Field F]

def ofRankAtMost (T : Tensor F X Y Z) (r : ℕ) (hT : RankAtMost T r) :
    PolynomialApproximation T r 0 0 where
  polynomial := fun x y z => Polynomial.C (T x y z)
  rank_bound := hT.map Polynomial.C
  vanishes := by
    intro x y z k hk
    exact (Nat.not_lt_zero k hk).elim
  leading := by
    intro x y z
    exact Polynomial.coeff_C_zero
  degree_bound := by
    intro x y z
    simpa only [Nat.cast_zero] using (Polynomial.degree_C_le (a := T x y z))

@[simp] theorem ofRankAtMost_polynomial (T : Tensor F X Y Z) (r : ℕ)
    (hT : RankAtMost T r) :
    (ofRankAtMost T r hT).polynomial = (fun x y z => Polynomial.C (T x y z)) := rfl

variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor F X Y Z} {r d D : ℕ}

def restrict (W : PolynomialApproximation T r d D)
    (A : X' → X → F) (B : Y' → Y → F) (C : Z' → Z → F) :
    PolynomialApproximation (Tensor.restrict A B C T) r d D where
  polynomial := restrictPolynomial A B C W.polynomial
  rank_bound := W.rank_bound.restrictPolynomial A B C
  vanishes := by
    intro x' y' z' k hk
    rw [restrictPolynomial_coeff]
    have hzero (x : X) (y : Y) (z : Z) : (W.polynomial x y z).coeff k = 0 :=
      W.vanishes x y z k hk
    simp only [Tensor.restrict, hzero, mul_zero, Finset.sum_const_zero]
  leading := by
    intro x' y' z'
    rw [restrictPolynomial_coeff]
    simp only [W.leading]
  degree_bound := restrictPolynomial_degree_le A B C W.polynomial D W.degree_bound

@[simp] theorem restrict_polynomial (W : PolynomialApproximation T r d D)
    (A : X' → X → F) (B : Y' → Y → F) (C : Z' → Z → F) :
    (W.restrict A B C).polynomial = restrictPolynomial A B C W.polynomial := rfl

end PolynomialApproximation

end Tensor
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ComplexPolynomialWitnessProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.Foundation
namespace Tensor
namespace PolynomialApproximation

variable {F X Y Z U V W X' Y' Z' : Type*} [Field F]
variable {T : Tensor F X Y Z} {S : Tensor F U V W}
variable {r s d e D E : ℕ}

theorem product_polynomial_eq (A : PolynomialApproximation T r d D)
    (B : PolynomialApproximation S s e E) (x : X × U) (y : Y × V) (z : Z × W) :
    Tensor.product A.polynomial B.polynomial x y z =
      Polynomial.X ^ (d + e) * Tensor.product A.normalized B.normalized x y z := by
  dsimp only [Tensor.product]
  rw [A.polynomial_eq, B.polynomial_eq, pow_add]
  ring

def product (A : PolynomialApproximation T r d D)
    (B : PolynomialApproximation S s e E) :
    PolynomialApproximation (Tensor.product T S) (r * s) (d + e) (D + E) where
  polynomial := Tensor.product A.polynomial B.polynomial
  rank_bound := A.rank_bound.product B.rank_bound
  vanishes := by
    intro x y z k hk
    rw [A.product_polynomial_eq B]
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk, ite_false, if_false]
  leading := by
    intro x y z
    rw [A.product_polynomial_eq B]
    simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, if_true, Nat.sub_self,
      Tensor.product, Polynomial.mul_coeff_zero, A.normalized_constant, B.normalized_constant]
  degree_bound := by
    intro x y z
    apply Polynomial.degree_le_of_natDegree_le
    exact Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_le_of_degree_le (A.degree_bound x.1 y.1 z.1))
      (Polynomial.natDegree_le_of_degree_le (B.degree_bound x.2 y.2 z.2))

@[simp] theorem product_polynomial (A : PolynomialApproximation T r d D)
    (B : PolynomialApproximation S s e E) :
    (A.product B).polynomial = Tensor.product A.polynomial B.polynomial := rfl

def pullback (A : PolynomialApproximation T r d D)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    PolynomialApproximation (Tensor.pullback fx fy fz T) r d D where
  polynomial := Tensor.pullback fx fy fz A.polynomial
  rank_bound := A.rank_bound.pullback fx fy fz
  vanishes := fun x y z k hk => A.vanishes (fx x) (fy y) (fz z) k hk
  leading := fun x y z => A.leading (fx x) (fy y) (fz z)
  degree_bound := fun x y z => A.degree_bound (fx x) (fy y) (fz z)

@[simp] theorem pullback_polynomial (A : PolynomialApproximation T r d D)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    (A.pullback fx fy fz).polynomial = Tensor.pullback fx fy fz A.polynomial := rfl

def cyclic (A : PolynomialApproximation T r d D) :
    PolynomialApproximation (Tensor.cyclic T) r d D where
  polynomial := Tensor.cyclic A.polynomial
  rank_bound := A.rank_bound.cyclic
  vanishes := fun y z x k hk => A.vanishes x y z k hk
  leading := fun y z x => A.leading x y z
  degree_bound := fun y z x => A.degree_bound x y z

@[simp] theorem cyclic_polynomial (A : PolynomialApproximation T r d D) :
    A.cyclic.polynomial = Tensor.cyclic A.polynomial := rfl

end PolynomialApproximation
end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_ParametersWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

abbrev Shape := Fin 3 → ℕ

def shape (a b c : ℕ) : Shape := (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (c) Matrix.vecEmpty)))

def shapes (n : ℕ) : List Shape :=
  (List.range (n + 1)).flatMap fun a =>
    (List.range (n + 1 - a)).map fun b => shape a b (n - a - b)

def positive (s : Shape) : Bool := s 0 > 0 && s 1 > 0 && s 2 > 0

def sorted (s : Shape) : Bool := s 0 ≤ s 1 && s 1 ≤ s 2

def sortedInitial : List Shape := (shapes 16).filter sorted

def positiveInitial : List Shape := sortedInitial.filter positive

def positiveSecond : List Shape := (shapes 8).filter positive

def zeroSecond : List Shape := (shapes 8).filter (fun s => !positive s)

def shapeMax (s : Shape) : ℕ := max (s 0) (max (s 1) (s 2))

def below (s : Shape) : List Shape :=
  (shapes ((s 0 + s 1 + s 2) / 2)).filter
    (fun u => u 0 ≤ s 0 && u 1 ≤ s 1 && u 2 ≤ s 2)

def complement (s u : Shape) : Shape := fun i => s i - u i

def tablea : List ℤ :=
  [-55839, -36137, -17449, -1780, 11561, 22640, 31188, 36731, 38593, 35898,
   29051, 18387, 3823, -14569, -39776, -38598, -23708]

def tableP : List ℤ :=
  [-3070, 295, -20546, -1514, -38211, -9654, -7530, -2765, -55230, -16412,
   -14246, -5912, -78106, -32809, -7009, -26324, -13519, -3592, -96458, -47439,
   -16217, -46871, -25058, -9643, -95643, -62269, -28725, -8576, -2535, -2550,
   -34711, -7207, -3270, -6376, -53221, -15352, -3477, -14828, -4187, -74924,
   -32439, -7231, -3578, -24599, -8700, -92989, -46655, -16926, -3517, -42976,
   -20283, -5132, -107049, -63201, -31013, -9730, -3705, -67421, -35684, -13735,
   -68829, -36752, -13993, -7658, -7586, -76746, -33496, -7329, -7447, -17336,
   -4721, -96770, -49297, -17874, -7143, -30044, -10107, -116558, -68325, -33467,
   -10424, -7476, -51341, -24711, -5530, -76548, -41988, -15608, -17266, -4357,
   -17106, -4343, -120770, -70820, -34294, -10580, -16819, -4315, -32943, -9992,
   -83616, -44202, -16154, -17098, -4371, -56609, -25990, -5564, -56356, -25900,
   -5561, -33052, -9918, -32951, -9906, -57255, -26128, -5560]

def tablep : List ℤ :=
  [-39594, -5561, -55254, -15178, -62331, -19672, -54917, -18539, -16455, -32184,
   -5716, -11688, -5527, -53009, -6669, -6669, -64938, -20286, -6616, -26336,
   -26429, -6696, -60888, -19760, -6690, -5724, -32216, -15829, -58477, -18987,
   -26339, -6619, -26393, -26340, -26359, -6620, -16239, -55176, -18587, -55107,
   -18571, -16272, -60868, -19755, -6696, -6692, -55133, -18580, -16247, -32128,
   -5727, -32138, -5725, -122]

def tabled : List ℤ :=
  [63, 97655, 0, 42132, 92966, 1204, 42148, 95604, 41743, 3057,
   109933, 42092, 3747, 41991, 1, 100622, 42166, 103562, 9039, 42157,
   103577, 42165, 63582, 110082, 4584, 42175, 104091, 38838, 102383, 104793,
   42126, 11814, 63338, 42165, 104864, 3587, 42166, 110086, 2207, 94768,
   42166, 104185, 4735, 38889, 110065, 42166, 102372, 104314, 38956, 4876,
   102395, 42166, 110068, 2953, 42166, 96000, 41863, 95723, 3031, 63321,
   42040, 42174, 104662, 11860, 104902, 42189, 2967, 96042, 42047, 109872,
   3986, 42200, 3834, 110106, 60257]

def tablez : List ℤ :=
  [-11037, -36170, -4779, 23107, -12831, 29263, 45052, 22289, -6216, 23895,
   -14326, -40670, -9623, -34674, -12708, -36610, -2174, 21564, -5587, 22521,
   -9766, 28961, 43809, 22299, -12216, 28778, 44147, 22176, -7811, 21870,
   -6053, 23786, -166, 94, -52, 17]

def statisticWeight : Fin 6 → ℕ := (Matrix.vecCons (0) (Matrix.vecCons (1) (Matrix.vecCons (2) (Matrix.vecCons (2) (Matrix.vecCons (3) (Matrix.vecCons (4) Matrix.vecEmpty))))))

def kappa : Fin 6 → Fin 6 := (Matrix.vecCons (5) (Matrix.vecCons (4) (Matrix.vecCons (2) (Matrix.vecCons (3) (Matrix.vecCons (1) (Matrix.vecCons (0) Matrix.vecEmpty))))))

theorem kappa_involution (i : Fin 6) : kappa (kappa i) = i := by
  revert i
  decide +kernel

def weight (n : ℤ) : ℚ :=
  (∑ j ∈ Finset.range 17, ((n : ℚ) / 640000) ^ j / Nat.factorial j) ^ 64

abbrev SplitKey := Shape × Fin 3 × ℕ

def splitKeys (parents : List Shape) : List SplitKey :=
  parents.flatMap fun s =>
    ([0, 1, 2] : List (Fin 3)).flatMap fun i =>
      (List.range (s i / 2)).filterMap fun j =>
        if s i - (s 0 + s 1 + s 2) / 2 ≤ j then some (s, i, j) else none

def assigned {α : Type} [BEq α] (keys : List α) (data : List ℤ) (key : α) : ℤ :=
  (((keys.zip data).find? (fun e => e.1 == key)).map Prod.snd).getD 0

def splitSignature (parents : List Shape) (data : List ℤ) (s u : Shape) : Fin 3 → ℤ :=
  fun i => assigned (splitKeys parents) data (s, i, min (u i) (s i - u i))

def splitWeight (parents : List Shape) (data : List ℤ) (s u : Shape) : ℚ :=
  ∏ i : Fin 3, weight (splitSignature parents data s u i)

def splitLaw (parents : List Shape) (data : List ℤ) (s u : Shape) : ℚ :=
  if u ∈ below s then
    splitWeight parents data s u / ((below s).map (splitWeight parents data s)).sum
  else 0

def stageALaw := splitLaw positiveInitial tableP

def stageBLaw := splitLaw positiveSecond tablep

def binaryKeys : List (Shape × Shape) :=
  positiveSecond.flatMap fun t =>
    ((below t).filter (fun u => shapeMax u == 2)).map fun u => (t, u)

def binaryInteger (t u : Shape) : ℤ := assigned binaryKeys tabled (t, u)

def binaryParameter (t u : Shape) : ℚ := (binaryInteger t u : ℚ) / 1000000

abbrev PairSlot := Fin 6 × Fin 6

def unorderedPairs (t : Shape) : List PairSlot :=
  (List.finRange 6).flatMap fun i =>
    (List.finRange 6).filterMap fun j =>
      if i ≤ j ∧ statisticWeight i + statisticWeight j = shapeMax t
      then some (i, j) else none

def pairKeys : List (Shape × PairSlot) :=
  zeroSecond.flatMap fun t =>
    ((unorderedPairs t).dropLast).map fun ij => (t, ij)

def orderedPairInteger (t : Shape) (i j : Fin 6) : ℤ :=
  assigned pairKeys tablez (t, min i j, max i j)

def orderedPairs (t : Shape) : List PairSlot :=
  (List.finRange 6).flatMap fun i =>
    (List.finRange 6).filterMap fun j =>
      if statisticWeight i + statisticWeight j = shapeMax t then some (i, j) else none

def zeroPairLaw (t : Shape) (i j : Fin 6) : ℚ :=
  if statisticWeight i + statisticWeight j = shapeMax t then
    weight (orderedPairInteger t i j) /
      ((orderedPairs t).map (fun ij => weight (orderedPairInteger t ij.1 ij.2))).sum
  else 0

theorem truncated_polynomial_positive (y : ℚ) (hy : |y| ≤ 1 / 4) :
    0 < ∑ j ∈ Finset.range 17, y ^ j / Nat.factorial j := by
  have term_bound (j : ℕ) :
      |y ^ (j + 1) / (Nat.factorial (j + 1) : ℚ)| ≤ (1 / 4 : ℚ) ^ (j + 1) := by
    have hd : (1 : ℚ) ≤ Nat.factorial (j + 1) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (j + 1)))
    calc
      _ = |y| ^ (j + 1) / (Nat.factorial (j + 1) : ℚ) := by
        simp only [abs_div, abs_pow,
          abs_of_nonneg (Nat.cast_nonneg (Nat.factorial (j + 1)) :
            (0 : ℚ) ≤ (Nat.factorial (j + 1) : ℚ))]
      _ ≤ (1 / 4 : ℚ) ^ (j + 1) / (Nat.factorial (j + 1) : ℚ) := by gcongr
      _ ≤ _ := div_le_self (by positivity) hd
  have hb : |∑ j ∈ Finset.range 16, y ^ (j + 1) / (Nat.factorial (j + 1) : ℚ)| < 1 := by
    calc
      _ ≤ ∑ j ∈ Finset.range 16, |y ^ (j + 1) / (Nat.factorial (j + 1) : ℚ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range 16, (1 / 4 : ℚ) ^ (j + 1) :=
        Finset.sum_le_sum (fun j _ => term_bound j)
      _ < 1 := by norm_num [Finset.sum_range_succ]
  rw [show 17 = 16 + 1 by decide, Finset.sum_range_succ']
  norm_num only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  linarith [(abs_lt.mp hb).1]

theorem weight_positive_of_argument_bound (n : ℤ) (hn : |n| ≤ 160000) :
    0 < weight n := by
  unfold weight
  apply pow_pos
  apply truncated_polynomial_positive
  have hn' : |(n : ℚ)| ≤ 160000 := by exact_mod_cast hn
  rw [abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℚ) < 640000)]
  exact (div_le_iff₀ (by norm_num)).mpr (by linarith)

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_StageCLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem assigned_mem_or_zero {α : Type} [BEq α] (keys : List α) (data : List ℤ) (key : α) :
    assigned keys data key = 0 ∨ assigned keys data key ∈ data := by
  unfold assigned
  cases h : (keys.zip data).find? (fun e => e.1 == key) with
  | none => simp
  | some pair =>
    right
    exact (List.of_mem_zip (List.mem_of_find?_eq_some h)).2

theorem assigned_argument_bound {α : Type} [BEq α] (keys : List α) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (key : α) : |assigned keys data key| ≤ 160000 := by
  rcases assigned_mem_or_zero keys data key with h | h
  · rw [h]; norm_num
  · exact hd _ h

theorem splitWeight_positive (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) :
    0 < splitWeight parents data s u := by
  apply Finset.prod_pos
  intro i _
  apply weight_positive_of_argument_bound
  exact assigned_argument_bound _ data hd _

theorem list_sum_map_nonnegative {α : Type} (xs : List α) (f : α → ℚ)
    (hf : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (hf x (by simp)) (ih (fun y hy => hf y (by simp [hy])))

theorem list_sum_map_positive {α : Type} (xs : List α) (f : α → ℚ)
    (hne : xs ≠ []) (hf : ∀ x ∈ xs, 0 < f x) : 0 < (xs.map f).sum := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    simp only [List.map_cons, List.sum_cons]
    exact add_pos_of_pos_of_nonneg (hf x (by simp))
      (list_sum_map_nonnegative xs f (fun y hy => (hf y (by simp [hy])).le))

theorem list_sum_map_div {α : Type} (xs : List α) (f : α → ℚ) (d : ℚ) :
    (xs.map (fun x => f x / d)).sum = (xs.map f).sum / d := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_div]

theorem splitLaw_positive (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) (hu : u ∈ below s) :
    0 < splitLaw parents data s u := by
  rw [splitLaw, ite_eq_left hu]
  apply div_pos (splitWeight_positive parents data hd s u)
  apply list_sum_map_positive
  · intro he
    simp only [he, List.not_mem_nil] at hu
  · intro v _
    exact splitWeight_positive parents data hd s v

theorem splitLaw_normalized (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s : Shape) (hne : below s ≠ []) :
    ((below s).map (splitLaw parents data s)).sum = 1 := by
  have he : (below s).map (splitLaw parents data s) =
      (below s).map (fun u => splitWeight parents data s u /
        ((below s).map (splitWeight parents data s)).sum) := by
    apply List.map_congr_left
    intro u hu
    simp only [splitLaw, hu, ite_true, if_true]
  rw [he, list_sum_map_div, div_self]
  exact ne_of_gt (list_sum_map_positive (below s) _ hne
    (fun u _ => splitWeight_positive parents data hd s u))

theorem stageA_table_arguments_bounded : ∀ n ∈ tableP, |n| ≤ 160000 := by decide +kernel

theorem stageB_table_arguments_bounded : ∀ n ∈ tablep, |n| ≤ 160000 := by decide +kernel

theorem stageA_support_nonempty : ∀ s ∈ positiveInitial, below s ≠ [] := by decide +kernel

theorem stageB_support_nonempty : ∀ s ∈ positiveSecond, below s ≠ [] := by decide +kernel

theorem stageB_support_complement : ∀ s ∈ positiveSecond, ∀ u ∈ below s,
    complement s u ∈ below s ∧ ∀ i, u i ≤ s i := by decide +kernel

theorem stageALaw_positive (s u : Shape) (hu : u ∈ below s) : 0 < stageALaw s u :=
  splitLaw_positive _ _ stageA_table_arguments_bounded s u hu

theorem stageBLaw_positive (s u : Shape) (hu : u ∈ below s) : 0 < stageBLaw s u :=
  splitLaw_positive _ _ stageB_table_arguments_bounded s u hu

theorem stageALaw_normalized (s : Shape) (hs : s ∈ positiveInitial) :
    ((below s).map (stageALaw s)).sum = 1 :=
  splitLaw_normalized _ _ stageA_table_arguments_bounded s (stageA_support_nonempty s hs)

theorem stageBLaw_normalized (s : Shape) (hs : s ∈ positiveSecond) :
    ((below s).map (stageBLaw s)).sum = 1 :=
  splitLaw_normalized _ _ stageB_table_arguments_bounded s (stageB_support_nonempty s hs)

def initialMultiplicity (s : Shape) : ℕ :=
  if s 0 = s 1 ∧ s 1 = s 2 then 1 else if s 0 = s 1 ∨ s 1 = s 2 ∨ s 0 = s 2 then 3 else 6

def initialInteger (i : ℕ) : ℤ := assigned (List.range 17) tablea i

def initialWeight (s : Shape) : ℚ :=
  initialMultiplicity s * ∏ i : Fin 3, weight (initialInteger (s i))

def initialLaw (s : Shape) : ℚ :=
  if s ∈ sortedInitial then initialWeight s / (sortedInitial.map initialWeight).sum else 0

theorem initial_table_arguments_bounded : ∀ n ∈ tablea, |n| ≤ 160000 := by decide +kernel

theorem initialWeight_positive (s : Shape) : 0 < initialWeight s := by
  apply mul_pos
  · unfold initialMultiplicity
    split_ifs <;> norm_num
  · apply Finset.prod_pos
    intro i _
    apply weight_positive_of_argument_bound
    exact assigned_argument_bound _ tablea initial_table_arguments_bounded _

theorem initialLaw_positive (s : Shape) (hs : s ∈ sortedInitial) : 0 < initialLaw s := by
  rw [initialLaw, ite_eq_left hs]
  apply div_pos (initialWeight_positive s)
  exact list_sum_map_positive _ _ (by decide +kernel) (fun t _ => initialWeight_positive t)

theorem initialLaw_normalized : (sortedInitial.map initialLaw).sum = 1 := by
  have he : sortedInitial.map initialLaw = sortedInitial.map
      (fun s => initialWeight s / (sortedInitial.map initialWeight).sum) := by
    apply List.map_congr_left
    intro s hs
    simp only [initialLaw, hs, ite_true, if_true]
  rw [he, list_sum_map_div, div_self]
  exact ne_of_gt (list_sum_map_positive _ _ (by decide +kernel)
    (fun s _ => initialWeight_positive s))

theorem binary_table_bounds : ∀ n ∈ tabled, 0 ≤ n ∧ n ≤ 110106 := by decide +kernel

theorem binaryInteger_bounds (t u : Shape) :
    0 ≤ binaryInteger t u ∧ binaryInteger t u ≤ 110106 := by
  rcases assigned_mem_or_zero binaryKeys tabled (t, u) with h | h
  · change 0 ≤ assigned binaryKeys tabled (t, u) ∧ assigned binaryKeys tabled (t, u) ≤ 110106
    rw [h]
    norm_num
  · exact binary_table_bounds _ h

theorem binaryParameter_bounds (t u : Shape) :
    0 ≤ binaryParameter t u ∧ binaryParameter t u ≤ (110106 : ℚ) / 1000000 := by
  obtain ⟨hlo, hhi⟩ := binaryInteger_bounds t u
  have hl : (0 : ℚ) ≤ binaryInteger t u := by exact_mod_cast hlo
  have hh : (binaryInteger t u : ℚ) ≤ 110106 := by exact_mod_cast hhi
  unfold binaryParameter
  constructor
  · exact div_nonneg hl (by norm_num)
  · exact div_le_div_of_nonneg_right hh (by norm_num)

def singletonSlot (k : ℕ) : Fin 6 :=
  match k with
  | 0 => 0
  | 1 => 1
  | 3 => 4
  | 4 => 5
  | _ => 0

def littleLaw (t u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - binaryParameter t u else if i = 3 then binaryParameter t u else 0
  else if i = singletonSlot (u w) then 1 else 0

end MatrixMultiplication.AllFieldParameters

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators

def stageCDistinguished (u : Shape) : Fin 3 :=
  if u 0 = 2 then 0 else if u 1 = 2 then 1 else 2

def stageCCanonicalAtom : Fin 4 → Shape :=
  (Matrix.vecCons (shape 1 1 0) (Matrix.vecCons (shape 0 0 2) (Matrix.vecCons (shape 1 0 1) (Matrix.vecCons (shape 0 1 1) Matrix.vecEmpty))))

def stageCAtom (u : Shape) (i : Fin 4) : Shape :=
  if stageCDistinguished u = 0 then
    shape (stageCCanonicalAtom i 2) (stageCCanonicalAtom i 1) (stageCCanonicalAtom i 0)
  else if stageCDistinguished u = 1 then
    shape (stageCCanonicalAtom i 0) (stageCCanonicalAtom i 2) (stageCCanonicalAtom i 1)
  else stageCCanonicalAtom i

def stageCWeight (t u : Shape) (i : Fin 4) : ℚ :=
  if i.val < 2 then binaryParameter t u / 2 else (1 - binaryParameter t u) / 2

theorem stageCAtom_injective : ∀ u ∈ shapes 4, positive u = true →
    Function.Injective (stageCAtom u) := by
  decide +kernel

theorem stageCAtom_mem : ∀ u ∈ shapes 4, positive u = true →
    ∀ i, stageCAtom u i ∈ below u := by
  decide +kernel

theorem stageCWeight_nonnegative (t u : Shape) (i : Fin 4) :
    0 ≤ stageCWeight t u i := by
  obtain ⟨hlo, hhi⟩ := binaryParameter_bounds t u
  unfold stageCWeight
  split_ifs <;> linarith

theorem stageCWeight_normalized (t u : Shape) : ∑ i, stageCWeight t u i = 1 := by
  norm_num [stageCWeight, Fin.sum_univ_succ] <;> ring

end MatrixMultiplication.AllFieldHistory

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

def entropyTerm (p : ℝ) : ℝ := -p * Real.log p

def finiteEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ := ∑ a, entropyTerm (p a)

@[simp] theorem entropyTerm_zero : entropyTerm 0 = 0 := by simp [entropyTerm]

structure FiniteLaw (A : Type*) [Fintype A] where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def map (p : FiniteLaw A) (f : A → B) : FiniteLaw B := by
  classical
  exact
    { mass := fun b => ∑ a, if f a = b then p.mass a else 0
      nonneg := fun b => Finset.sum_nonneg fun a _ => by
        split_ifs
        · exact p.nonneg a
        · exact le_rfl
      total := by
        rw [Finset.sum_comm]
        simpa using p.total }

@[simp] theorem map_mass [DecidableEq B] (p : FiniteLaw A) (f : A → B) (b : B) :
    (p.map f).mass b = ∑ a, if f a = b then p.mass a else 0 := by
  classical
  dsimp only [map]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp only [h, ite_true, if_true, ite_false, if_false]

def joint (p : FiniteLaw A) (q : A → FiniteLaw B) : FiniteLaw (A × B) where
  mass ab := p.mass ab.1 * (q ab.1).mass ab.2
  nonneg ab := mul_nonneg (p.nonneg ab.1) ((q ab.1).nonneg ab.2)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, (q _).total, p.total]

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

def homogeneousEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ :=
  (∑ a, p a) * Real.log (∑ a, p a) + finiteEntropy p

end

end MatrixMultiplication.AllFieldParameters

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

@[simp] theorem entropyTerm_one : entropyTerm 1 = 0 := by simp [entropyTerm]

@[fun_prop] theorem continuous_entropyTerm : Continuous entropyTerm :=
  Real.continuous_negMulLog

@[fun_prop] theorem continuous_finiteEntropy {A : Type*} [Fintype A] :
    Continuous (finiteEntropy : (A → ℝ) → ℝ) := by
  unfold finiteEntropy
  exact continuous_finsetSum _ fun a _ => continuous_entropyTerm.comp (continuous_apply a)

namespace FiniteLaw

variable {A : Type*} [Fintype A]

def uniform (A : Type*) [Fintype A] [Nonempty A] : FiniteLaw A where
  mass _a := (Fintype.card A : ℝ)⁻¹
  nonneg _a := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hn : (Fintype.card A : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card A)).ne'
    simp [Finset.sum_const, nsmul_eq_mul, hn]

@[simp] theorem uniform_mass [Nonempty A] (a : A) :
    (uniform A).mass a = (Fintype.card A : ℝ)⁻¹ := rfl

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

noncomputable section

def LabelRecord (Label : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => LabelRecord Label n × Label n

instance labelRecordFintype (Label : ℕ → Type u) [∀ n, Fintype (Label n)] :
    (n : ℕ) → Fintype (LabelRecord Label n)
  | 0 => by
      change Fintype PUnit
      infer_instance
  | n + 1 => by
      letI := labelRecordFintype Label n
      change Fintype (LabelRecord Label n × Label n)
      infer_instance

structure FiniteLabelHierarchy (Label : ℕ → Type u) [∀ n, Fintype (Label n)]
    (depth : ℕ) where
  conditional : ∀ n, n < depth → LabelRecord Label n → FiniteLaw (Label n)

namespace FiniteLabelHierarchy

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)] {depth : ℕ}

def prefixLaw (h : FiniteLabelHierarchy Label depth) :
    (n : ℕ) → n ≤ depth → FiniteLaw (LabelRecord Label n)
  | 0, _ =>
      { mass := fun _ => 1
        nonneg := fun _ => zero_le_one
        total := by
          change (∑ _ : PUnit, (1 : ℝ)) = 1
          simp }
  | n + 1, hn =>
      (h.prefixLaw n (Nat.le_of_succ_le hn)).joint
        (h.conditional n (Nat.lt_of_succ_le hn))

@[simp] theorem prefixLaw_zero_mass (h : FiniteLabelHierarchy Label depth)
    (hn : 0 ≤ depth) (r : LabelRecord Label 0) :
    (h.prefixLaw 0 hn).mass r = 1 := rfl

@[simp] theorem prefixLaw_succ (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) :
    h.prefixLaw (n + 1) hn =
      (h.prefixLaw n (Nat.le_of_succ_le hn)).joint
        (h.conditional n (Nat.lt_of_succ_le hn)) := rfl

@[simp] theorem prefixLaw_succ_mass (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) (r : LabelRecord Label n) (s : Label n) :
    (h.prefixLaw (n + 1) hn).mass (r, s) =
      (h.prefixLaw n (Nat.le_of_succ_le hn)).mass r *
        (h.conditional n (Nat.lt_of_succ_le hn) r).mass s := rfl

end FiniteLabelHierarchy

end
end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointPairClassWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]

def wordPopulation (w : I → A) (a : A) : ℕ := Fintype.card {i // w i = a}

omit [DecidableEq I] in
theorem wordPopulation_sum (w : I → A) :
    ∑ a, wordPopulation w a = Fintype.card I := by
  simpa [wordPopulation] using Fintype.card_congr (Equiv.sigmaFiberEquiv w)

omit [Fintype A] [DecidableEq I] in
theorem wordPopulation_reindex (w : I → A) (e : J ≃ I) (a : A) :
    wordPopulation (w ∘ e) a = wordPopulation w a :=
  Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

abbrev ExactWords (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → A // ∀ a, wordPopulation w a = counts a}

theorem wordPopulation_sigma_fst (counts : A → ℕ) (a : A) :
    wordPopulation (fun i : Σ b, Fin (counts b) => i.1) a = counts a := by
  let e : {i : Σ b, Fin (counts b) // i.1 = a} ≃ Fin (counts a) :=
    { toFun := fun i => i.property ▸ i.val.2
      invFun := fun i => ⟨⟨a, i⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨b, i⟩, h⟩
        cases h
        rfl
      right_inv := by intro i; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

theorem exactWords_nonempty (counts : A → ℕ) : Nonempty (ExactWords counts) := by
  classical
  let e : Fin (∑ a, counts a) ≃ (Σ a, Fin (counts a)) :=
    Fintype.equivOfCardEq (by simp)
  refine ⟨⟨(fun i : Σ a, Fin (counts a) => i.1) ∘ e, ?_⟩⟩
  intro a
  rw [wordPopulation_reindex, wordPopulation_sigma_fst]

omit [Fintype A] [DecidableEq I] in
theorem samePopulation_iff_permutation (w v : I → A) :
    (∀ a, wordPopulation v a = wordPopulation w a) ↔
      ∃ e : Equiv.Perm I, w ∘ e = v := by
  classical
  constructor
  · intro h
    let es : ∀ a, {i // v i = a} ≃ {i // w i = a} :=
      fun a => Fintype.equivOfCardEq (h a)
    refine ⟨Equiv.ofFiberEquiv es, ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map es i
  · rintro ⟨e, rfl⟩ a
    exact wordPopulation_reindex w e a

end MatrixMultiplication.Foundation





namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A B I : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

abbrev PopulationWords (I : Type*) [Fintype I] (counts : A → ℕ) :=
  {w : I → A // ∀ a, wordPopulation w a = counts a}

abbrev ConditionalWords (w : I → A) (counts : A → B → ℕ) :=
  {r : I → B // ∀ a b, Fintype.card {i // w i = a ∧ r i = b} = counts a b}

def fiberWordEquiv (w : I → A) : (I → B) ≃ (∀ a, {i // w i = a} → B) where
  toFun r _ i := r i.val
  invFun r i := r (w i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv := by
    intro r
    funext a i
    rcases i with ⟨i, hi⟩
    cases hi
    rfl

omit [Fintype A] [Fintype B] [DecidableEq I] in
theorem wordPopulation_fiber (w : I → A) (r : I → B) (a : A) (b : B) :
    wordPopulation (fun i : {i // w i = a} => r i.val) b =
      Fintype.card {i // w i = a ∧ r i = b} :=
  Fintype.card_congr
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun i => w i = a) (fun i => r i = b))

def conditionalWordsEquiv (w : I → A) (counts : A → B → ℕ) :
    ConditionalWords w counts ≃ ∀ a, PopulationWords {i // w i = a} (counts a) := by
  let e : ConditionalWords w counts ≃
      {r : ∀ a, {i // w i = a} → B // ∀ a b, wordPopulation (r a) b = counts a b} :=
    Equiv.subtypeEquiv (fiberWordEquiv w) fun r => by
      change (∀ a b, Fintype.card {i // w i = a ∧ r i = b} = counts a b) ↔
        ∀ a b, wordPopulation (fun i : {i // w i = a} => r i.val) b = counts a b
      simp only [wordPopulation_fiber]
  exact e.trans (Equiv.subtypePiEquivPi
    (β := fun a : A => {i // w i = a} → B)
    (p := fun a r => ∀ b, wordPopulation r b = counts a b))

end MatrixMultiplication.Foundation





end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointPopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulation

open MatrixMultiplication.Foundation
open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev Shape := Fin 17 × Fin 17 × Fin 17

def shapeSide (s : Fin 3) (u : Shape) : Fin 17 :=
  if s = 0 then u.1 else if s = 1 then u.2.1 else u.2.2

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ)

abbrev Positions (h : H) := Fin (∑ u, counts h u)
abbrev Target := ∀ h, ExactWords (counts h)

def canonicalTarget : Target counts :=
  fun h => Classical.choice (exactWords_nonempty (counts h))

abbrev Position := Σ h, Positions counts h

def triple (e : Target counts) : JointCoarseHashing.Triple (Position counts) :=
  (fun p => (e p.1).val p.2 |>.1,
    fun p => (e p.1).val p.2 |>.2.1,
    fun p => (e p.1).val p.2 |>.2.2)

omit [Fintype H] [DecidableEq H] in
theorem triple_injective : Function.Injective (triple counts) := by
  intro e f h
  funext c
  apply Subtype.ext
  funext i
  apply Prod.ext
  · exact congrArg (fun t : JointCoarseHashing.Triple (Position counts) => t.1 ⟨c, i⟩) h
  · apply Prod.ext
    · exact congrArg (fun t : JointCoarseHashing.Triple (Position counts) => t.2.1 ⟨c, i⟩) h
    · exact congrArg (fun t : JointCoarseHashing.Triple (Position counts) => t.2.2 ⟨c, i⟩) h

def targetSet : Finset (JointCoarseHashing.Triple (Position counts)) :=
  Finset.univ.image (triple counts)

abbrev Class (e : Target counts) (h : H) (u : Shape) :=
  {i : Positions counts h // (e h).val i = u}

omit [Fintype H] [DecidableEq H] in
theorem class_card (e : Target counts) (h : H) (u : Shape) :
    Fintype.card (Class counts e h u) = counts h u := (e h).property u

omit [Fintype H] [DecidableEq H] in
theorem symbol_count_pos (e : Target counts) (h : H) (i : Positions counts h) :
    0 < counts h ((e h).val i) := by
  rw [← class_card counts e h ((e h).val i)]
  exact Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩

omit [Fintype H] [DecidableEq H] in
theorem triple_support (sum : H → ℕ)
    (hsupport : ∀ h u, 0 < counts h u →
      u.1.val + u.2.1.val + u.2.2.val = sum h) (e : Target counts) :
    JointCoarseHashing.HasSupportSum (fun p : Position counts => sum p.1) (triple counts e) := by
  intro p
  exact hsupport p.1 ((e p.1).val p.2) (symbol_count_pos counts e p.1 p.2)

omit [Fintype H] [DecidableEq H] in
theorem exists_position_permutation (e f : Target counts) :
    ∃ p : ∀ h, Equiv.Perm (Positions counts h), ∀ h, (e h).val ∘ p h = (f h).val := by
  have hp : ∀ h, ∃ p : Equiv.Perm (Positions counts h), (e h).val ∘ p = (f h).val := by
    intro h
    apply (samePopulation_iff_permutation _ _).mp
    intro u
    rw [(e h).property, (f h).property]
  choose p hp using hp
  exact ⟨p, hp⟩

def sideWord (s : Fin 3) (t : JointCoarseHashing.Triple (Position counts))
    (h : H) : Positions counts h → Fin 17 :=
  fun i => shapeSide s (t.1 ⟨h, i⟩, t.2.1 ⟨h, i⟩, t.2.2 ⟨h, i⟩)

omit [Fintype H] [DecidableEq H] in
theorem sideWord_triple (s : Fin 3) (e : Target counts) (h : H) :
    sideWord counts s (triple counts e) h = shapeSide s ∘ (e h).val := rfl

omit [Fintype H] [DecidableEq H] in
theorem marginal_population_eq (e f : Target counts) (h : H) (s : Fin 3) (a : Fin 17) :
    wordPopulation (sideWord counts s (triple counts e) h) a =
      wordPopulation (sideWord counts s (triple counts f) h) a := by
  obtain ⟨p, hp⟩ := exists_position_permutation counts e f
  rw [sideWord_triple, sideWord_triple, ← hp h]
  exact (wordPopulation_reindex (shapeSide s ∘ (e h).val) (p h) a).symm

def ambientSet (sum : H → ℕ) : Finset (JointCoarseHashing.Triple (Position counts)) :=
  Finset.univ.filter fun t =>
    JointCoarseHashing.HasSupportSum (fun p : Position counts => sum p.1) t ∧
    ∀ h s a, wordPopulation (sideWord counts s t h) a =
      wordPopulation (sideWord counts s (triple counts (canonicalTarget counts)) h) a

theorem targetSet_subset_ambient (sum : H → ℕ)
    (hsupport : ∀ h u, 0 < counts h u →
      u.1.val + u.2.1.val + u.2.2.val = sum h) :
    targetSet counts ⊆ ambientSet counts sum := by
  intro t ht
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, triple_support counts sum hsupport e, ?_⟩
  intro h s a
  exact marginal_population_eq counts e (canonicalTarget counts) h s a

end MatrixMultiplication.JointPopulation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ShapeEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators

def shapeTotal (u : Shape) : ℕ := u 0 + u 1 + u 2

def ShapeBounded (u : Shape) : Prop := ∀ i, u i ≤ 16

def encodeShape (u : Shape) (h : ShapeBounded u) : JointPopulation.Shape :=
  (⟨u 0, Nat.lt_succ_of_le (h 0)⟩,
    ⟨u 1, Nat.lt_succ_of_le (h 1)⟩, ⟨u 2, Nat.lt_succ_of_le (h 2)⟩)

def decodeShape (u : JointPopulation.Shape) : Shape :=
  fun i => (JointPopulation.shapeSide i u).val

@[simp] theorem decode_encodeShape (u : Shape) (h : ShapeBounded u) :
    decodeShape (encodeShape u h) = u := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem encodeShape_side (u : Shape) (h : ShapeBounded u) (i : Fin 3) :
    (JointPopulation.shapeSide i (encodeShape u h)).val = u i :=
  congrFun (decode_encodeShape u h) i

theorem encodeShape_inj {u v : Shape} {hu : ShapeBounded u} {hv : ShapeBounded v}
    (h : encodeShape u hu = encodeShape v hv) : u = v := by
  simpa only [decode_encodeShape] using congrArg decodeShape h

@[simp] theorem encodeShape_total (u : Shape) (h : ShapeBounded u) :
    (encodeShape u h).1.val + (encodeShape u h).2.1.val +
      (encodeShape u h).2.2.val = shapeTotal u := rfl

def physicalShape (phi : Equiv.Perm (Fin 3)) (u : Shape) : Shape :=
  fun i => u (phi.symm i)

@[simp] theorem physicalShape_source (phi : Equiv.Perm (Fin 3)) (u : Shape) (i : Fin 3) :
    physicalShape phi u (phi i) = u i := by
  simp only [physicalShape, Equiv.symm_apply_apply]

theorem physicalShape_bounded (phi : Equiv.Perm (Fin 3)) (u : Shape)
    (h : ShapeBounded u) : ShapeBounded (physicalShape phi u) :=
  fun i => h (phi.symm i)

@[simp] theorem physicalShape_complement (phi : Equiv.Perm (Fin 3)) (u v : Shape) :
    physicalShape phi (complement u v) =
      complement (physicalShape phi u) (physicalShape phi v) := rfl

theorem physicalShape_total (phi : Equiv.Perm (Fin 3)) (u : Shape) :
    shapeTotal (physicalShape phi u) = shapeTotal u := by
  simpa [shapeTotal, physicalShape, Fin.sum_univ_succ, Nat.add_assoc] using
    (Equiv.sum_comp phi.symm u)

theorem physicalShape_injective (phi : Equiv.Perm (Fin 3)) :
    Function.Injective (physicalShape phi) := by
  intro u v h
  funext i
  simpa only [physicalShape_source] using congrFun h (phi i)

def encodePhysicalShape (phi : Equiv.Perm (Fin 3)) (u : Shape) (h : ShapeBounded u) :
    JointPopulation.Shape := encodeShape (physicalShape phi u) (physicalShape_bounded phi u h)

@[simp] theorem decode_encodePhysicalShape (phi : Equiv.Perm (Fin 3))
    (u : Shape) (h : ShapeBounded u) :
    decodeShape (encodePhysicalShape phi u h) = physicalShape phi u :=
  decode_encodeShape _ _

@[simp] theorem encodePhysicalShape_side (phi : Equiv.Perm (Fin 3))
    (u : Shape) (h : ShapeBounded u) (i : Fin 3) :
    (JointPopulation.shapeSide i (encodePhysicalShape phi u h)).val = u (phi.symm i) :=
  encodeShape_side _ _ i

theorem encodePhysicalShape_inj (phi : Equiv.Perm (Fin 3))
    {u v : Shape} {hu : ShapeBounded u} {hv : ShapeBounded v}
    (h : encodePhysicalShape phi u hu = encodePhysicalShape phi v hv) : u = v :=
  physicalShape_injective phi (encodeShape_inj h)

theorem encodePhysicalShape_total (phi : Equiv.Perm (Fin 3))
    (u : Shape) (h : ShapeBounded u) :
    (encodePhysicalShape phi u h).1.val + (encodePhysicalShape phi u h).2.1.val +
      (encodePhysicalShape phi u h).2.2.val = shapeTotal u :=
  physicalShape_total phi u

theorem mem_shapes_total {n : ℕ} {u : Shape} (hu : u ∈ shapes n) : shapeTotal u = n := by
  simp only [shapes, List.mem_flatMap, List.mem_map, List.mem_range] at hu
  obtain ⟨a, ha, b, hb, rfl⟩ := hu
  change a + b + (n - a - b) = n
  omega

theorem coordinate_le_total (u : Shape) (i : Fin 3) : u i ≤ shapeTotal u := by
  fin_cases i
  · change u 0 ≤ u 0 + u 1 + u 2
    omega
  · change u 1 ≤ u 0 + u 1 + u 2
    omega
  · change u 2 ≤ u 0 + u 1 + u 2
    omega

theorem mem_shapes_bound {n : ℕ} {u : Shape} (hu : u ∈ shapes n) (i : Fin 3) : u i ≤ n := by
  simpa only [mem_shapes_total hu] using coordinate_le_total u i

theorem mem_shapes_bounded {n : ℕ} {u : Shape} (hu : u ∈ shapes n) (hn : n ≤ 16) :
    ShapeBounded u := fun i => (mem_shapes_bound hu i).trans hn

theorem below_mem_shapes {u v : Shape} (hv : v ∈ below u) :
    v ∈ shapes (shapeTotal u / 2) := (List.mem_filter.mp hv).1

theorem below_total {u v : Shape} (hv : v ∈ below u) :
    shapeTotal v = shapeTotal u / 2 := mem_shapes_total (below_mem_shapes hv)

theorem below_le {u v : Shape} (hv : v ∈ below u) : ∀ i, v i ≤ u i := by
  have h := (List.mem_filter.mp hv).2
  have hb : v 0 ≤ u 0 ∧ v 1 ≤ u 1 ∧ v 2 ≤ u 2 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h
  intro i
  fin_cases i
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.2

theorem below_bounded {u v : Shape} (hu : ShapeBounded u) (hv : v ∈ below u) :
    ShapeBounded v := fun i => (below_le hv i).trans (hu i)

theorem root_shape_spec (s : Shape) (hs : s ∈ sortedInitial) :
    ShapeBounded s ∧ shapeTotal s = 16 := by
  have hm : s ∈ shapes 16 := (List.mem_filter.mp hs).1
  exact ⟨mem_shapes_bounded hm (by omega), mem_shapes_total hm⟩

theorem stageA_below_nodup : ∀ s ∈ positiveInitial, (below s).Nodup := by
  decide +kernel

theorem stageB_below_nodup : ∀ t ∈ positiveSecond, (below t).Nodup := by
  decide +kernel

theorem stageA_get_injective (s : Shape) (hs : s ∈ positiveInitial) :
    Function.Injective (below s).get :=
  List.nodup_iff_injective_get.mp (stageA_below_nodup s hs)

theorem stageB_get_injective (t : Shape) (ht : t ∈ positiveSecond) :
    Function.Injective (below t).get :=
  List.nodup_iff_injective_get.mp (stageB_below_nodup t ht)

theorem positiveInitial_shape_spec (s : Shape) (hs : s ∈ positiveInitial) :
    ShapeBounded s ∧ shapeTotal s = 16 :=
  root_shape_spec s (List.mem_filter.mp hs).1

theorem positiveSecond_shape_spec (t : Shape) (ht : t ∈ positiveSecond) :
    ShapeBounded t ∧ shapeTotal t = 8 := by
  have hm : t ∈ shapes 8 := (List.mem_filter.mp ht).1
  exact ⟨mem_shapes_bounded hm (by omega), mem_shapes_total hm⟩

theorem stageA_shape_spec (s t : Shape) (hs : s ∈ positiveInitial) (ht : t ∈ below s) :
    ShapeBounded t ∧ shapeTotal t = 8 := by
  obtain ⟨hb, hsum⟩ := positiveInitial_shape_spec s hs
  exact ⟨below_bounded hb ht, by simpa only [hsum] using below_total ht⟩

theorem stageB_shape_spec (t u : Shape) (ht : t ∈ positiveSecond) (hu : u ∈ below t) :
    ShapeBounded u ∧ shapeTotal u = 4 := by
  obtain ⟨hb, hsum⟩ := positiveSecond_shape_spec t ht
  exact ⟨below_bounded hb hu, by simpa only [hsum] using below_total hu⟩

theorem stageC_shape_spec (u : Shape) (hu : u ∈ shapes 4) (hpos : positive u = true)
    (i : Fin 4) : ShapeBounded (stageCAtom u i) ∧ shapeTotal (stageCAtom u i) = 2 := by
  have hi := stageCAtom_mem u hu hpos i
  exact ⟨below_bounded (mem_shapes_bounded hu (by omega)) hi,
    by simpa only [mem_shapes_total hu] using below_total hi⟩

end MatrixMultiplication.AllFieldHistory

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ParametersHalfLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

def positiveHalfLaw (t : Shape) (w : Fin 3) (ij : PairSlot) : ℚ :=
  ((below t).map fun u => stageBLaw t u * littleLaw t u w ij.1 *
    littleLaw t (complement t u) w ij.2).sum

def halfMaxAxis (t : Shape) : Fin 3 :=
  (([0,1,2] : List (Fin 3)).find? (fun w => t w == shapeMax t)).getD 0

def halfLaw (t : Shape) (w : Fin 3) (ij : PairSlot) : ℚ :=
  if positive t then positiveHalfLaw t w ij
  else if t w = 0 then if ij = (0,0) then 1 else 0
  else if w = halfMaxAxis t then zeroPairLaw t ij.1 ij.2
  else zeroPairLaw t (kappa ij.1) (kappa ij.2)

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_PopulationCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldPopulationCounts

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

def denominator (w : I → ℚ) : ℕ := ∏ i, (w i).den

def baseCount (w : I → ℚ) (i : I) : ℕ :=
  (w i).num.toNat * ∏ j ∈ Finset.univ.erase i, (w j).den

def count (w : I → ℚ) (m : ℕ) (i : I) : ℕ := m * baseCount w i

def blockLength (w : I → ℚ) (m : ℕ) : ℕ := m * denominator w

theorem denominator_factor (w : I → ℚ) (i : I) :
    (w i).den * (∏ j ∈ Finset.univ.erase i, (w j).den) = denominator w := by
  exact Finset.mul_prod_erase Finset.univ (fun j => (w j).den) (Finset.mem_univ i)

theorem baseCount_cast (w : I → ℚ) (hw : ∀ i, 0 ≤ w i) (i : I) :
    (baseCount w i : ℚ) = (denominator w : ℚ) * w i := by
  have hnum : ((w i).num.toNat : ℚ) = ((w i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hw i))
  have hden : ((w i).den : ℚ) ≠ 0 := by exact_mod_cast (w i).den_ne_zero
  have hq : ((w i).num : ℚ) = w i * ((w i).den : ℚ) := by
    calc
      ((w i).num : ℚ) =
          (((w i).num : ℚ) / ((w i).den : ℚ)) * ((w i).den : ℚ) :=
        (div_mul_cancel₀ _ hden).symm
      _ = w i * ((w i).den : ℚ) := by rw [(w i).num_div_den]
  rw [baseCount, ← denominator_factor w i]
  push_cast
  rw [hnum, hq]
  ring

theorem count_cast (w : I → ℚ) (hw : ∀ i, 0 ≤ w i) (m : ℕ) (i : I) :
    (count w m i : ℚ) = (m : ℚ) * (denominator w : ℚ) * w i := by
  simp only [count, Nat.cast_mul, baseCount_cast w hw, mul_assoc]

theorem count_cast_blockLength (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    (m : ℕ) (i : I) :
    (count w m i : ℚ) = (blockLength w m : ℚ) * w i := by
  simpa only [blockLength, Nat.cast_mul] using count_cast w hw m i

theorem count_eq_of_mass_eq (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    (m : ℕ) {i j : I} (h : w i = w j) : count w m i = count w m j := by
  apply Nat.cast_injective (R := ℚ)
  rw [count_cast w hw, count_cast w hw, h]

end

end MatrixMultiplication.AllFieldPopulationCounts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_CompleteWordPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.PermutationMatching

variable {C : Type*} {P X Y : C → Type*}

structure CompleteWordPair (P X Y : C → Type*) where
  left : ∀ c, P c → X c
  right : ∀ c, P c → Y c

abbrev HalfClassPermutations (P : C → Type*) :=
  (∀ c, Equiv.Perm (P c)) × (∀ c, Equiv.Perm (P c))

instance completeWordPairMulAction :
    MulAction (HalfClassPermutations P) (CompleteWordPair P X Y) where
  smul g w :=
    { left := fun c i => w.left c ((g.1 c).symm i)
      right := fun c i => w.right c ((g.2 c).symm i) }
  one_smul w := by cases w; rfl
  mul_smul g h w := rfl

@[simp] theorem smul_completeWordPair_left (g : HalfClassPermutations P)
    (w : CompleteWordPair P X Y) (c : C) (i : P c) :
    (g • w).left c i = w.left c ((g.1 c).symm i) := rfl

@[simp] theorem smul_completeWordPair_right (g : HalfClassPermutations P)
    (w : CompleteWordPair P X Y) (c : C) (i : P c) :
    (g • w).right c i = w.right c ((g.2 c).symm i) := rfl

end MatrixMultiplication.PermutationMatching

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InverseLinearRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.ExactRecovery

variable {K X Y Z I A B C : Type*} [CommSemiring K]

def delete (Q : Tensor K X Y Z) (px : X → Prop) (py : Y → Prop)
    (pz : Z → Prop) [DecidablePred px] [DecidablePred py] [DecidablePred pz] :
    Tensor K X Y Z := fun x y z => if px x ∧ py y ∧ pz z then Q x y z else 0

end MatrixMultiplication.ExactRecovery

end




section
open scoped BigOperators

namespace MatrixMultiplication.OrbitCounting

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [DecidableEq X]

def orbitSet (x : X) : Finset X := Finset.univ.image fun g : G => g • x

@[simp] theorem smul_mem_orbitSet (x : X) (g : G) : g • x ∈ orbitSet (G := G) x := by
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩

end MatrixMultiplication.OrbitCounting

end




end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InheritedMaskMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.InheritedMasks

open MatrixMultiplication.Foundation
open scoped BigOperators

section TensorAction

variable {F C : Type*} [CommSemiring F] [Fintype C]
  {P X Y Z : C → Type*} [∀ c, Fintype (P c)]

def classProduct (T : ∀ c, Tensor F (X c) (Y c) (Z c)) :
    Tensor F (∀ c, P c → X c) (∀ c, P c → Y c) (∀ c, P c → Z c) :=
  fun x y z => ∏ c, ∏ i, T c (x c i) (y c i) (z c i)

end TensorAction

section EmpiricalWindows

variable {P A B : Type*} [Fintype P] [DecidableEq P]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

noncomputable def empiricalLaw (w : P → A) (a : A) : ℝ :=
  (wordPopulation w a : ℝ) / Fintype.card P

def typeWindow (ν : A → ℝ) (η : ℝ) (w : P → A) : Prop :=
  ∀ a, |empiricalLaw w a - ν a| ≤ η

end EmpiricalWindows

end MatrixMultiplication.InheritedMasks

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.PermutationMatching
open MatrixMultiplication.InheritedMasks

namespace MatrixMultiplication.HistorySymmetry

variable {C : Type*} {P X Y : C → Type*}

def completeWordPairEquiv : CompleteWordPair P X Y ≃
    ((∀ c, P c → X c) × (∀ c, P c → Y c)) where
  toFun w := (w.left, w.right)
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance completeWordPairFintype
    [Fintype C] [DecidableEq C] [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    [∀ c, Fintype (X c)] [∀ c, Fintype (Y c)] : Fintype (CompleteWordPair P X Y) :=
  Fintype.ofEquiv _ completeWordPairEquiv.symm

end MatrixMultiplication.HistorySymmetry

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointExtraction
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.JointExtraction

open MatrixMultiplication.Foundation

variable {F X Y Z I : Type*} [CommSemiring F]

structure Assignment (X Y Z I : Type*) where
  x : X → Option I
  y : Y → Option I
  z : Z → Option I

noncomputable def uniqueAssignment {A : Type*} (eligible : Finset I)
    (compatible : I → A → Prop) (v : A) : Option I := by
  classical
  exact if h : ∃ i, i ∈ eligible ∧ compatible i v ∧
      ∀ j, j ∈ eligible → compatible j v → j = i
    then some (Classical.choose h) else none

theorem uniqueAssignment_spec {A : Type*} (eligible : Finset I)
    (compatible : I → A → Prop) (v : A) (i : I)
    (h : uniqueAssignment eligible compatible v = some i) :
    i ∈ eligible ∧ compatible i v ∧
      ∀ j, j ∈ eligible → compatible j v → j = i := by
  classical
  unfold uniqueAssignment at h
  split_ifs at h with hex
  · have hi : Classical.choose hex = i := Option.some.inj h
    simpa only [hi] using Classical.choose_spec hex

noncomputable def retainAssignment {A : Type*} (f : A → Option I)
    (keep : A → Prop) (v : A) : Option I := by
  classical
  exact if keep v then f v else none

theorem retainAssignment_some {A : Type*} (f : A → Option I)
    (keep : A → Prop) (v : A) (i : I)
    (h : retainAssignment f keep v = some i) : f v = some i := by
  classical
  unfold retainAssignment at h
  split_ifs at h
  · exact h

def Coherent (T : Tensor F X Y Z) (a : Assignment X Y Z I) : Prop :=
  ∀ x y z i j k, T x y z ≠ 0 →
    a.x x = some i → a.y y = some j → a.z z = some k → i = j ∧ i = k

noncomputable def branch (T : Tensor F X Y Z) (a : Assignment X Y Z I)
    (i : I) : Tensor F X Y Z := by
  classical
  exact fun x y z => if a.x x = some i ∧ a.y y = some i ∧ a.z z = some i
    then T x y z else 0

noncomputable def assignmentMatrix {A : Type*} (f : A → Option I) :
    (I × A) → A → F := by
  classical
  exact fun p a => if a = p.2 ∧ f a = some p.1 then 1 else 0

theorem restrict_assignments_apply [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq I]
    (T : Tensor F X Y Z) (a : Assignment X Y Z I)
    (x : I × X) (y : I × Y) (z : I × Z) :
    Tensor.restrict (assignmentMatrix a.x) (assignmentMatrix a.y)
      (assignmentMatrix a.z) T x y z =
    if a.x x.2 = some x.1 ∧ a.y y.2 = some y.1 ∧ a.z z.2 = some z.1
      then T x.2 y.2 z.2 else 0 := by
  classical
  simp [Tensor.restrict, assignmentMatrix, ite_and, ite_mul, mul_ite]
  split_ifs <;> simp_all

theorem restrict_assignments_eq_directSum
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq I]
    (T : Tensor F X Y Z) (a : Assignment X Y Z I) (h : Coherent T a) :
    Tensor.restrict (assignmentMatrix a.x) (assignmentMatrix a.y)
      (assignmentMatrix a.z) T = Tensor.directSum (branch T a) := by
  classical
  funext x y z
  rw [restrict_assignments_apply]
  by_cases hx : x.1 = y.1
  · by_cases hz : x.1 = z.1
    · simp [Tensor.directSum, branch, ← hx, ← hz]
    · by_cases ht : T x.2 y.2 z.2 = 0
      · simp [Tensor.directSum, hz, ht]
      · have hn : ¬ (a.x x.2 = some x.1 ∧ a.y y.2 = some y.1 ∧
            a.z z.2 = some z.1) := by
          intro ha
          exact hz (h _ _ _ _ _ _ ht ha.1 ha.2.1 ha.2.2).2
        simp [Tensor.directSum, hz, hn]
  · by_cases ht : T x.2 y.2 z.2 = 0
    · simp [Tensor.directSum, hx, ht]
    · have hn : ¬ (a.x x.2 = some x.1 ∧ a.y y.2 = some y.1 ∧
          a.z z.2 = some z.1) := by
        intro ha
        exact hx (h _ _ _ _ _ _ ht ha.1 ha.2.1 ha.2.2).1
      simp [Tensor.directSum, hx, hn]

end MatrixMultiplication.JointExtraction

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointMaskedAssignment
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCoarseAssignment

open MatrixMultiplication.Foundation JointExtraction

attribute [local instance] Classical.propDecidable

variable {F X Y Z A B C I V : Type*} [CommSemiring F]

abbrev Triple (A B C : Type*) := A × B × C

def survives (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (e : Triple A B C) : Prop := hx e.1 ∧ hy e.2.1 ∧ hz e.2.2

def eligible (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) : Finset (Triple A B C) :=
  ambient.filter fun e => e ∈ targets ∧ survives hx hy hz e ∧
    ∀ f ∈ ambient, survives hx hy hz f → f.1 = e.1 → f = e

theorem mem_eligible_iff (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) (e : Triple A B C) :
    e ∈ eligible ambient targets hx hy hz ↔
      e ∈ ambient ∧ e ∈ targets ∧ survives hx hy hz e ∧
        ∀ f ∈ ambient, survives hx hy hz f → f.1 = e.1 → f = e := by
  simp [eligible]

def assignUseful (eligible : Finset I) (compatible useful : I → V → Prop)
    (v : V) : Option I :=
  retainAssignment (uniqueAssignment eligible compatible)
    (fun v => ∃ i, uniqueAssignment eligible compatible v = some i ∧ useful i v) v

theorem assignUseful_spec (eligible : Finset I) (compatible useful : I → V → Prop)
    (v : V) (i : I) (h : assignUseful eligible compatible useful v = some i) :
    i ∈ eligible ∧ compatible i v ∧ useful i v ∧
      ∀ j, j ∈ eligible → compatible j v → j = i := by
  classical
  have hu : uniqueAssignment eligible compatible v = some i :=
    retainAssignment_some _ _ v i h
  have hh := uniqueAssignment_spec eligible compatible v i hu
  have huse : useful i v := by
    unfold assignUseful retainAssignment at h
    split_ifs at h with hk
    obtain ⟨j, hj, hju⟩ := hk
    have hji : j = i := Option.some.inj (hj.symm.trans hu)
    exact hji ▸ hju
  exact ⟨hh.1, hh.2.1, huse, hh.2.2⟩

def assignments (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (compatibleY : Triple A B C → Y → Prop)
    (compatibleZ : Triple A B C → Z → Prop)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) : Assignment X Y Z (Triple A B C) where
  x := assignUseful (eligible ambient targets hx hy hz) (fun e x => cx x = e.1) usefulX
  y := assignUseful (eligible ambient targets hx hy hz)
    (fun e y => cy y = e.2.1 ∧ compatibleY e y) usefulY
  z := assignUseful (eligible ambient targets hx hy hz)
    (fun e z => cz z = e.2.2 ∧ compatibleZ e z) usefulZ

theorem assignments_coherent
    (T : Tensor F X Y Z) (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (compatibleY : Triple A B C → Y → Prop)
    (compatibleZ : Triple A B C → Z → Prop)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop)
    (support : ∀ x y z, T x y z ≠ 0 → (cx x, cy y, cz z) ∈ ambient)
    (transferY : ∀ x y z e, T x y z ≠ 0 → (cx x, cy y, cz z) = e →
      usefulX e x → compatibleY e y)
    (transferZ : ∀ x y z e, T x y z ≠ 0 → (cx x, cy y, cz z) = e →
      usefulX e x → usefulY e y → compatibleZ e z) :
    Coherent T (assignments ambient targets hx hy hz cx cy cz
      compatibleY compatibleZ usefulX usefulY usefulZ) := by
  intro x y z i j k hT hxi hyj hzk
  have hi := assignUseful_spec (eligible ambient targets hx hy hz)
    (fun e x => cx x = e.1) usefulX x i hxi
  have hj := assignUseful_spec (eligible ambient targets hx hy hz)
    (fun e y => cy y = e.2.1 ∧ compatibleY e y) usefulY y j hyj
  have hk := assignUseful_spec (eligible ambient targets hx hy hz)
    (fun e z => cz z = e.2.2 ∧ compatibleZ e z) usefulZ z k hzk
  have hie := (mem_eligible_iff ambient targets hx hy hz i).mp hi.1
  have hje := (mem_eligible_iff ambient targets hx hy hz j).mp hj.1
  have hke := (mem_eligible_iff ambient targets hx hy hz k).mp hk.1
  have hs : survives hx hy hz (cx x, cy y, cz z) :=
    ⟨hi.2.1.symm ▸ hie.2.2.1.1, hj.2.1.1.symm ▸ hje.2.2.1.2.1,
      hk.2.1.1.symm ▸ hke.2.2.1.2.2⟩
  have he : (cx x, cy y, cz z) = i :=
    hie.2.2.2 _ (support x y z hT) hs hi.2.1
  have hyi : cy y = i.2.1 := congrArg (fun e : Triple A B C => e.2.1) he
  have hzi : cz z = i.2.2 := congrArg (fun e : Triple A B C => e.2.2) he
  have hij : i = j := hj.2.2.2 i hi.1
    ⟨hyi, transferY x y z i hT he hi.2.2.1⟩
  have huy : usefulY i y := hij.symm ▸ hj.2.2.1
  have hik : i = k := hk.2.2.2 i hi.1
    ⟨hzi, transferZ x y z i hT he hi.2.2.1 huy⟩
  exact ⟨hij, hik⟩

end MatrixMultiplication.JointCoarseAssignment






namespace MatrixMultiplication.JointIdealBranches

open MatrixMultiplication.Foundation JointExtraction JointCoarseAssignment

attribute [local instance] Classical.propDecidable

variable {F X Y Z A B C : Type*} [CommSemiring F]

def ideal (T : Tensor F X Y Z)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) : Tensor F X Y Z :=
  ExactRecovery.delete T (fun x => cx x = e.1 ∧ usefulX e x)
    (fun y => cy y = e.2.1 ∧ usefulY e y)
    (fun z => cz z = e.2.2 ∧ usefulZ e z)

theorem branch_eq_delete_ideal
    (T : Tensor F X Y Z) (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (compatibleY : Triple A B C → Y → Prop)
    (compatibleZ : Triple A B C → Z → Prop)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) :
    let a := assignments ambient targets hx hy hz cx cy cz
      compatibleY compatibleZ usefulX usefulY usefulZ
    branch T a e = ExactRecovery.delete (ideal T cx cy cz usefulX usefulY usefulZ e)
      (fun x => a.x x = some e) (fun y => a.y y = some e) (fun z => a.z z = some e) := by
  classical
  dsimp only
  funext x y z
  by_cases h :
      (assignments ambient targets hx hy hz cx cy cz compatibleY compatibleZ
        usefulX usefulY usefulZ).x x = some e ∧
      (assignments ambient targets hx hy hz cx cy cz compatibleY compatibleZ
        usefulX usefulY usefulZ).y y = some e ∧
      (assignments ambient targets hx hy hz cx cy cz compatibleY compatibleZ
        usefulX usefulY usefulZ).z z = some e
  · have hX := assignUseful_spec (eligible ambient targets hx hy hz)
      (fun e x => cx x = e.1) usefulX x e h.1
    have hY := assignUseful_spec (eligible ambient targets hx hy hz)
      (fun e y => cy y = e.2.1 ∧ compatibleY e y) usefulY y e h.2.1
    have hZ := assignUseful_spec (eligible ambient targets hx hy hz)
      (fun e z => cz z = e.2.2 ∧ compatibleZ e z) usefulZ z e h.2.2
    simp [branch, ExactRecovery.delete, ideal, h, hX.2.1, hX.2.2.1,
      hY.2.1.1, hY.2.2.1, hZ.2.1.1, hZ.2.2.1]
  · simp [branch, ExactRecovery.delete, h]

theorem ideal_delete (T : Tensor F X Y Z)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) :
    ideal (ExactRecovery.delete T px py pz) cx cy cz usefulX usefulY usefulZ e =
      ExactRecovery.delete (ideal T cx cy cz usefulX usefulY usefulZ e) px py pz := by
  funext x y z
  simp only [ideal, ExactRecovery.delete]
  split_ifs <;> simp_all

theorem branch_masked_eq_delete_ideal
    (T : Tensor F X Y Z) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (compatibleY : Triple A B C → Y → Prop)
    (compatibleZ : Triple A B C → Z → Prop)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) :
    let a := assignments ambient targets hx hy hz cx cy cz
      compatibleY compatibleZ usefulX usefulY usefulZ
    branch (ExactRecovery.delete T px py pz) a e =
      ExactRecovery.delete (ideal T cx cy cz usefulX usefulY usefulZ e)
        (fun x => a.x x = some e ∧ px x)
        (fun y => a.y y = some e ∧ py y)
        (fun z => a.z z = some e ∧ pz z) := by
  dsimp only
  rw [branch_eq_delete_ideal, ideal_delete]
  funext x y z
  simp only [ExactRecovery.delete]
  split_ifs <;> simp_all

end MatrixMultiplication.JointIdealBranches






namespace MatrixMultiplication.JointCanonicalization

open MatrixMultiplication.Foundation JointPopulation InheritedMasks
open PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ)

def fiberEquiv (e : Target counts) (h : H) (u : Shape) :
    Class counts e h u ≃ Fin (counts h u) :=
  Fintype.equivOfCardEq (by rw [class_card, Fintype.card_fin])

def positionEquiv (e : Target counts) (h : H) :
    Positions counts h ≃ (Σ u, Fin (counts h u)) :=
  (Equiv.sigmaFiberEquiv (e h).val).symm.trans
    (Equiv.sigmaCongrRight (fiberEquiv counts e h))

omit [Fintype H] [DecidableEq H] in
@[simp] theorem positionEquiv_shape (e : Target counts) (h : H) (i : Positions counts h) :
    (positionEquiv counts e h i).1 = (e h).val i := rfl

omit [Fintype H] [DecidableEq H] in
@[simp] theorem positionEquiv_symm_shape (e : Target counts) (h : H)
    (i : Σ u, Fin (counts h u)) :
    (e h).val ((positionEquiv counts e h).symm i) = i.1 := by
  have hh := congrArg Sigma.fst ((positionEquiv counts e h).apply_symm_apply i)
  simpa only [positionEquiv_shape] using hh

abbrev ClassKey := H × Shape
abbrev ClassPositions (c : ClassKey (H := H)) := Fin (counts c.1 c.2)

variable (L R : H → Type*)

abbrev RawPairs := ∀ h, Positions counts h → L h × R h
abbrev CanonicalPairs := CompleteWordPair (ClassPositions counts)
  (fun c => L c.1) (fun c => R c.1)

def pairEquiv (e : Target counts) : RawPairs counts L R ≃ CanonicalPairs counts L R where
  toFun w :=
    { left := fun c j => (w c.1 ((positionEquiv counts e c.1).symm ⟨c.2, j⟩)).1
      right := fun c j => (w c.1 ((positionEquiv counts e c.1).symm ⟨c.2, j⟩)).2 }
  invFun w := fun h i =>
    (w.left (h, (e h).val i) (positionEquiv counts e h i).2,
      w.right (h, (e h).val i) (positionEquiv counts e h i).2)
  left_inv w := by
    funext h i
    change ((w h ((positionEquiv counts e h).symm
      (positionEquiv counts e h i))).1,
      (w h ((positionEquiv counts e h).symm (positionEquiv counts e h i))).2) = w h i
    simp
  right_inv w := by
    cases w with
    | mk wl wr =>
      dsimp only
      congr 1 <;> funext c j
      · exact congrArg (β := L c.1)
          (fun p : Σ u, Fin (counts c.1 u) => wl (c.1, p.1) p.2)
          ((positionEquiv counts e c.1).apply_symm_apply ⟨c.2, j⟩)
      · exact congrArg (β := R c.1)
          (fun p : Σ u, Fin (counts c.1 u) => wr (c.1, p.1) p.2)
          ((positionEquiv counts e c.1).apply_symm_apply ⟨c.2, j⟩)

section Windows

variable {SL SR : H → Type*}
    [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)]
    [∀ h, DecidableEq (SL h)] [∀ h, DecidableEq (SR h)]
    (sl : ∀ c : ClassKey (H := H), L c.1 → SL c.1)
    (sr : ∀ c : ClassKey (H := H), R c.1 → SR c.1)
    (νl : ∀ c : ClassKey (H := H), SL c.1 → ℝ)
    (νr : ∀ c : ClassKey (H := H), SR c.1 → ℝ)
    (ηl ηr : ClassKey (H := H) → ℝ)

def rawWindows (e : Target counts) (w : RawPairs counts L R) : Prop :=
  ∀ h u, 0 < counts h u →
    typeWindow (νl (h, u)) (ηl (h, u))
      (fun i : Class counts e h u => sl (h, u) (w h i.val).1) ∧
    typeWindow (νr (h, u)) (ηr (h, u))
      (fun i : Class counts e h u => sr (h, u) (w h i.val).2)

end Windows

section Coefficients

variable {F : Type*} [CommSemiring F]
    (T : ∀ h, Tensor F (L h × R h) (L h × R h) (L h × R h))
    (coarse : Fin 3 → ∀ h, L h × R h → Fin 17)

def coarseMask (s : Fin 3) (e : Target counts) (w : RawPairs counts L R) : Prop :=
  ∀ h i, coarse s h (w h i) = shapeSide s ((e h).val i)

end Coefficients

end MatrixMultiplication.JointCanonicalization






namespace MatrixMultiplication.JointAssignmentLoss

open JointExtraction JointCoarseAssignment

attribute [local instance] Classical.propDecidable

variable {A B C I V Ω : Type*}

theorem uniqueAssignment_of_unique (candidates : Finset I)
    (compatible : I → V → Prop) (v : V) (i : I)
    (hi : i ∈ candidates) (hc : compatible i v)
    (hu : ∀ j, j ∈ candidates → compatible j v → j = i) :
    uniqueAssignment candidates compatible v = some i := by
  classical
  have hex : ∃ j, j ∈ candidates ∧ compatible j v ∧
      ∀ k, k ∈ candidates → compatible k v → k = j := ⟨i, hi, hc, hu⟩
  unfold uniqueAssignment
  rw [dite_eq_left hex]
  exact congrArg some (hu _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2.1)

theorem assignUseful_of_unique (candidates : Finset I)
    (compatible useful : I → V → Prop) (v : V) (i : I)
    (hi : i ∈ candidates) (hc : compatible i v) (huse : useful i v)
    (hu : ∀ j, j ∈ candidates → compatible j v → j = i) :
    assignUseful candidates compatible useful v = some i := by
  have hassign := uniqueAssignment_of_unique candidates compatible v i hi hc hu
  have hkeep : ∃ j, uniqueAssignment candidates compatible v = some j ∧ useful j v :=
    ⟨i, hassign, huse⟩
  simp only [assignUseful, retainAssignment, ite_eq_left hkeep]
  exact hassign

end MatrixMultiplication.JointAssignmentLoss






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWCompleteStatistics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.FieldCoefficientExtraction

variable {F X Y Z : Type*}

theorem coeff_triple [CommSemiring F] (a b c : Polynomial F) (d : ℕ) :
    (a * b * c).coeff d =
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        (if j.val ≤ d - i.val then a.coeff (d - i.val - j.val) else 0) *
          b.coeff j.val * c.coeff i.val := by
  classical
  rw [show a * b * c = c * (b * a) by ring]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
      b.coeff j * c.coeff i.val) (d + 1)]
  symm
  calc
    (∑ j ∈ Finset.range (d + 1),
        (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
          b.coeff j * c.coeff i.val) =
        ∑ j ∈ Finset.range (d - i.val + 1),
          (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
            b.coeff j * c.coeff i.val := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hjnot
      have h : ¬ j ≤ d - i.val := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hjnot
      simp [h]
    _ = ∑ j ∈ Finset.range (d - i.val + 1),
        c.coeff i.val * (b.coeff j * a.coeff (d - i.val - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
      ring

theorem rankAtMost_coeff [CommSemiring F]
    {P : Tensor (Polynomial F) X Y Z} {r : ℕ}
    (hP : Tensor.RankAtMost P r) (d : ℕ) :
    Tensor.RankAtMost (fun x y z => (P x y z).coeff d) ((d + 1) ^ 2 * r) := by
  classical
  rcases hP with ⟨a, b, c, rfl⟩
  let aa : (Fin r × Fin (d + 1) × Fin (d + 1)) → X → F :=
    fun v x => if v.2.2.val ≤ d - v.2.1.val then
      (a v.1 x).coeff (d - v.2.1.val - v.2.2.val) else 0
  let bb : (Fin r × Fin (d + 1) × Fin (d + 1)) → Y → F :=
    fun v y => (b v.1 y).coeff v.2.2.val
  let cc : (Fin r × Fin (d + 1) × Fin (d + 1)) → Z → F :=
    fun v z => (c v.1 z).coeff v.2.1.val
  have heq : (fun x y z => (∑ j, Tensor.rankOne (a j) (b j) (c j) x y z).coeff d) =
      fun x y z => ∑ v, Tensor.rankOne (aa v) (bb v) (cc v) x y z := by
    funext x y z
    simp only [Polynomial.finsetSum_coeff, Tensor.rankOne, Fintype.sum_prod_type,
      coeff_triple, aa, bb, cc]
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using Tensor.rankAtMost_sum_rankOne aa bb cc

theorem rank_power [Field F] {T : Tensor F X Y Z} {r d D : ℕ}
    (A : Tensor.PolynomialApproximation T r d D) (n : ℕ) :
    Tensor.RankAtMost (Tensor.power T n) ((d * n + 1) ^ 2 * r ^ n) := by
  have h := rankAtMost_coeff (A.power n).rank_bound (d * n)
  have heq : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power T n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [heq] at h
  exact h

end MatrixMultiplication.FieldCoefficientExtraction

end




noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation Polynomial

namespace MatrixMultiplication.FieldCW

section Integral

variable (F : Type*) [CommRing F] (q : ℕ)

def zeroForm (x : Fin (q + 2)) : F := if x.val = 0 then 1 else 0

def interiorForm (i : Fin q) (x : Fin (q + 2)) : F :=
  if x.val = i.val + 1 then 1 else 0

def lastForm (x : Fin (q + 2)) : F := if x.val = q + 1 then 1 else 0

def interiorSum (x : Fin (q + 2)) : F := ∑ i, interiorForm F q i x

def tensor : Tensor F (Fin (q + 2)) (Fin (q + 2)) (Fin (q + 2)) :=
  fun x y z =>
    (∑ i : Fin q,
      (zeroForm F q x * interiorForm F q i y * interiorForm F q i z +
      interiorForm F q i x * zeroForm F q y * interiorForm F q i z +
      interiorForm F q i x * interiorForm F q i y * zeroForm F q z)) +
    lastForm F q x * zeroForm F q y * zeroForm F q z +
    zeroForm F q x * lastForm F q y * zeroForm F q z +
    zeroForm F q x * zeroForm F q y * lastForm F q z

theorem interior_pair_sum (x y : Fin (q + 2)) :
    (∑ i : Fin q, interiorForm F q i x * interiorForm F q i y) =
      if x = y ∧ 1 ≤ x.val ∧ x.val ≤ q then 1 else 0 := by
  classical
  by_cases hx : 1 ≤ x.val ∧ x.val ≤ q
  · let i : Fin q := ⟨x.val - 1, by omega⟩
    rw [Finset.sum_eq_single i]
    · simp [interiorForm, i, Nat.sub_add_cancel hx.1, hx.1, hx.2,
        Fin.ext_iff, eq_comm]
    · intro j hj hji
      have hne : x.val ≠ j.val + 1 := by
        intro h
        apply hji
        apply Fin.ext
        dsimp [i]
        omega
      simp [interiorForm, hne]
    · simp
  · have hsum : (∑ i : Fin q, interiorForm F q i x * interiorForm F q i y) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : x.val ≠ i.val + 1 := by
        intro h
        apply hx
        have := i.isLt
        omega
      simp [interiorForm, hne]
    rw [hsum, ite_eq_right]
    intro h
    exact hx ⟨h.2.1, h.2.2⟩

theorem tensor_zero_side (x y z : Fin (q + 2)) (hx : x.val = 0) :
    tensor F q x y z =
      if (y.val = 0 ∧ z.val = q + 1) ∨
          (y.val = q + 1 ∧ z.val = 0) ∨
          (1 ≤ y.val ∧ y.val ≤ q ∧ y = z) then 1 else 0 := by
  have hx0 : zeroForm F q x = 1 := by simp [zeroForm, hx]
  have hxlast : lastForm F q x = 0 := by simp [lastForm, hx]
  have hxmid (i : Fin q) : interiorForm F q i x = 0 := by
    simp [interiorForm, hx]
  simp only [tensor, hx0, hxlast, hxmid, one_mul, zero_mul, add_zero]
  rw [interior_pair_sum]
  by_cases hy0 : y.val = 0
  · simp [zeroForm, lastForm, hy0]
  · by_cases hylast : y.val = q + 1
    · have hyinter : ¬ y.val ≤ q := by omega
      simp [zeroForm, lastForm, hylast]
    · have hylo : 1 ≤ y.val := by omega
      have hyhi : y.val ≤ q := by have := y.isLt; omega
      simp [zeroForm, lastForm, hy0, hylast, hylo, hyhi]

theorem tensor_cyclic (x y z : Fin (q + 2)) :
    tensor F q x y z = tensor F q y z x := by
  unfold tensor
  have hsum :
      (∑ i : Fin q,
        (zeroForm F q x * interiorForm F q i y * interiorForm F q i z +
        interiorForm F q i x * zeroForm F q y * interiorForm F q i z +
        interiorForm F q i x * interiorForm F q i y * zeroForm F q z)) =
      ∑ i : Fin q,
        (zeroForm F q y * interiorForm F q i z * interiorForm F q i x +
        interiorForm F q i y * zeroForm F q z * interiorForm F q i x +
        interiorForm F q i y * interiorForm F q i z * zeroForm F q x) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

def form (e : ℕ) (u v : F) : Polynomial F := C u + X ^ e * C v

def left : Option (Option (Fin q)) → Fin (q + 2) → Polynomial F
  | some (some i), x => X * form F 1 (zeroForm F q x) (interiorForm F q i x)
  | some none, x => -form F 2 (zeroForm F q x) (interiorSum F q x)
  | none, x => (1 - C (q : F) * X) * form F 3 (zeroForm F q x) (lastForm F q x)

def other : Option (Option (Fin q)) → Fin (q + 2) → Polynomial F
  | some (some i), x => form F 1 (zeroForm F q x) (interiorForm F q i x)
  | some none, x => form F 2 (zeroForm F q x) (interiorSum F q x)
  | none, x => form F 3 (zeroForm F q x) (lastForm F q x)

def polynomial : Tensor (Polynomial F) (Fin (q + 2)) (Fin (q + 2)) (Fin (q + 2)) :=
  fun x y z => ∑ i, Tensor.rankOne (left F q i) (other F q i) (other F q i) x y z

theorem rank_bound : Tensor.RankAtMost (polynomial F q) (q + 2) := by
  unfold polynomial
  simpa only [Fintype.card_option, Fintype.card_fin, Nat.add_assoc,
    Nat.reduceAdd] using
    Tensor.rankAtMost_sum_rankOne (left F q) (other F q) (other F q)

theorem polynomial_apply (x y z : Fin (q + 2)) :
    polynomial F q x y z =
      (∑ i : Fin q, X * form F 1 (zeroForm F q x) (interiorForm F q i x) *
        form F 1 (zeroForm F q y) (interiorForm F q i y) *
        form F 1 (zeroForm F q z) (interiorForm F q i z)) -
      form F 2 (zeroForm F q x) (interiorSum F q x) *
        form F 2 (zeroForm F q y) (interiorSum F q y) *
        form F 2 (zeroForm F q z) (interiorSum F q z) +
      (1 - C (q : F) * X) * form F 3 (zeroForm F q x) (lastForm F q x) *
        form F 3 (zeroForm F q y) (lastForm F q y) *
        form F 3 (zeroForm F q z) (lastForm F q z) := by
  simp only [polynomial, Fintype.sum_option, Tensor.rankOne, left, other]
  ring

theorem coeff_mul_two (a b : Polynomial F) :
    (a * b).coeff 2 = a.coeff 0 * b.coeff 2 + a.coeff 1 * b.coeff 1 +
      a.coeff 2 * b.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, add_assoc]

theorem coeff_mul_three (a b : Polynomial F) :
    (a * b).coeff 3 = a.coeff 0 * b.coeff 3 + a.coeff 1 * b.coeff 2 +
      a.coeff 2 * b.coeff 1 + a.coeff 3 * b.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, add_assoc]

theorem vanishes (x y z : Fin (q + 2)) (k : ℕ) (hk : k < 3) :
    (polynomial F q x y z).coeff k = 0 := by
  interval_cases k <;>
    simp [polynomial_apply, Polynomial.mul_coeff_zero,
      Polynomial.mul_coeff_one, coeff_mul_two, form, Polynomial.coeff_add,
      Polynomial.coeff_sub, interiorSum,
      Polynomial.coeff_one, Polynomial.coeff_X,
      Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum] <;>
    simp only [mul_assoc, mul_comm] <;> ring_nf
  simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_comm]
  ring

theorem leading (x y z : Fin (q + 2)) :
    (polynomial F q x y z).coeff 3 = tensor F q x y z := by
  simp [polynomial_apply, Polynomial.mul_coeff_zero,
    Polynomial.mul_coeff_one, coeff_mul_two, coeff_mul_three, form,
    Polynomial.coeff_add, Polynomial.coeff_sub,
    tensor, Polynomial.coeff_one, Polynomial.coeff_X,
    Finset.sum_add_distrib]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  simp only [Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm]
  ring

def degreeBound : ℕ := Finset.univ.sup fun xyz :
    Fin (q + 2) × Fin (q + 2) × Fin (q + 2) =>
      (polynomial F q xyz.1 xyz.2.1 xyz.2.2).natDegree

theorem degree_bound (x y z : Fin (q + 2)) :
    (polynomial F q x y z).degree ≤ degreeBound F q := by
  let f : (Fin (q + 2) × Fin (q + 2) × Fin (q + 2)) → ℕ :=
    fun xyz => (polynomial F q xyz.1 xyz.2.1 xyz.2.2).natDegree
  have h := Finset.le_sup (s := Finset.univ) (f := f) (b := (x, y, z))
    (Finset.mem_univ (x, y, z))
  exact Polynomial.degree_le_of_natDegree_le h

end Integral

variable (F : Type*) [Field F] (q : ℕ)

def approximation : Tensor.PolynomialApproximation (tensor F q) (q + 2) 3
    (degreeBound F q) where
  polynomial := polynomial F q
  rank_bound := rank_bound F q
  vanishes := vanishes F q
  leading := leading F q
  degree_bound := degree_bound F q

theorem rank_power (n : ℕ) :
    Tensor.RankAtMost (Tensor.power (tensor F q) n) ((3 * n + 1) ^ 2 * (q + 2) ^ n) :=
  FieldCoefficientExtraction.rank_power (approximation F q) n

end MatrixMultiplication.FieldCW

end




namespace MatrixMultiplication.CWLeafRestrictions

open MatrixMultiplication.Foundation

def lastLabel (q : ℕ) : Fin (q + 2) := ⟨q + 1, by omega⟩

def complement (q : ℕ) : Fin (q + 2) ≃ Fin (q + 2) :=
  Equiv.swap 0 (lastLabel q)

@[simp] theorem complement_zero (q : ℕ) : complement q 0 = lastLabel q := by
  simp [complement]

@[simp] theorem complement_last (q : ℕ) : complement q (lastLabel q) = 0 := by
  simp [complement]

@[simp] theorem complement_involution (q : ℕ) (x : Fin (q + 2)) :
    complement q (complement q x) = x := by
  simp [complement]

theorem complement_interior (q : ℕ) (x : Fin (q + 2))
    (hx0 : x.val ≠ 0) (hxlast : x.val ≠ q + 1) : complement q x = x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact hx0 (congrArg Fin.val h)
  · intro h
    exact hxlast (congrArg Fin.val h)

theorem zero_support_iff (q : ℕ) (y z : Fin (q + 2)) :
    ((y.val = 0 ∧ z.val = q + 1) ∨
      (y.val = q + 1 ∧ z.val = 0) ∨
      (1 ≤ y.val ∧ y.val ≤ q ∧ y = z)) ↔ complement q y = z := by
  by_cases hy0 : y.val = 0
  · have hy : y = 0 := Fin.ext hy0
    subst y
    rw [complement_zero]
    constructor
    · rintro (⟨_, hz⟩ | ⟨hy, _⟩ | ⟨hy, _⟩)
      · exact Fin.ext hz.symm
      · have : (0 : ℕ) = q + 1 := hy
        omega
      · have : 1 ≤ (0 : ℕ) := hy
        omega
    · intro h
      exact Or.inl ⟨rfl, (congrArg Fin.val h).symm⟩
  · by_cases hylast : y.val = q + 1
    · have hy : y = lastLabel q := Fin.ext hylast
      subst y
      rw [complement_last]
      constructor
      · rintro (⟨hy, _⟩ | ⟨_, hz⟩ | ⟨_, hy, _⟩)
        · have : q + 1 = 0 := hy
          omega
        · exact Fin.ext hz.symm
        · have : q + 1 ≤ q := hy
          omega
      · intro h
        exact Or.inr (Or.inl ⟨rfl, (congrArg Fin.val h).symm⟩)
    · have hlo : 1 ≤ y.val := by omega
      have hhi : y.val ≤ q := by have := y.isLt; omega
      rw [complement_interior q y hy0 hylast]
      simp [hy0, hylast, hlo, hhi]

theorem tensor_zero_matching (F : Type*) [CommRing F] (q : ℕ)
    (y z : Fin (q + 2)) :
    FieldCW.tensor F q 0 y (complement q z) = if y = z then 1 else 0 := by
  rw [FieldCW.tensor_zero_side F q 0 y (complement q z) rfl]
  simp only [zero_support_iff, Equiv.apply_eq_iff_eq]

end MatrixMultiplication.CWLeafRestrictions





namespace MatrixMultiplication.CWLeafStatistics

open MatrixMultiplication.Foundation

def weight (x : Fin 7) : ℕ := if x.val = 0 then 0 else if x.val = 6 then 2 else 1

def pairStatistic (x : Fin 7 × Fin 7) : Fin 6 :=
  if weight x.1 + weight x.2 = 0 then 0
  else if weight x.1 + weight x.2 = 1 then 1
  else if weight x.1 + weight x.2 = 2 then
    if weight x.1 = 1 ∧ weight x.2 = 1 then 2 else 3
  else if weight x.1 + weight x.2 = 3 then 4 else 5

theorem complement_weight : ∀ x : Fin 7,
    weight (CWLeafRestrictions.complement 5 x) + weight x = 2 := by
  decide +kernel

end MatrixMultiplication.CWLeafStatistics





noncomputable section






namespace MatrixMultiplication.CWStrands

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {F : Type*} [CommRing F]

theorem site_weight_support (x y z : Fin 7)
    (h : FieldCW.tensor F 5 x y z ≠ 0) :
    CWLeafStatistics.weight x + CWLeafStatistics.weight y + CWLeafStatistics.weight z = 2 := by
  have hzero (a b : Fin 7) (hh : FieldCW.tensor F 5 0 a b ≠ 0) :
      CWLeafStatistics.weight a + CWLeafStatistics.weight b = 2 := by
    have he := CWLeafRestrictions.tensor_zero_matching F 5 a
      (CWLeafRestrictions.complement 5 b)
    simp only [CWLeafRestrictions.complement_involution] at he
    by_cases hm : a = CWLeafRestrictions.complement 5 b
    · subst a
      exact CWLeafStatistics.complement_weight b
    · rw [ite_eq_right hm] at he
      exact False.elim (hh he)
  by_cases hx : x = 0
  · subst x
    simpa [CWLeafStatistics.weight] using hzero y z h
  by_cases hy : y = 0
  · subst y
    have hh : FieldCW.tensor F 5 0 z x ≠ 0 := by
      rwa [← FieldCW.tensor_cyclic]
    have hw := hzero z x hh
    simp only [CWLeafStatistics.weight, Fin.val_zero, ite_eq_left, add_zero] at *
    omega
  by_cases hz : z = 0
  · subst z
    have hh : FieldCW.tensor F 5 0 x y ≠ 0 := by
      rwa [FieldCW.tensor_cyclic]
    have hw := hzero x y hh
    simpa [CWLeafStatistics.weight] using hw
  have hx0 : x.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hx
  have hy0 : y.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hy
  have hz0 : z.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hz
  apply False.elim (h _)
  simp only [FieldCW.tensor, FieldCW.zeroForm, hx0, hy0, hz0, ite_false, if_false,
    zero_mul, mul_zero, add_zero, Finset.sum_const_zero]

def weight {P : Type*} [Fintype P] (w : P → Fin 7) : ℕ :=
  ∑ i, CWLeafStatistics.weight (w i)

def strand (P : Type*) [Fintype P] : Tensor F (P → Fin 7) (P → Fin 7) (P → Fin 7) :=
  fun x y z => ∏ i, FieldCW.tensor F 5 (x i) (y i) (z i)

theorem strand_support {P : Type*} [Fintype P]
    (x y z : P → Fin 7) (h : strand (F := F) P x y z ≠ 0) :
    weight x + weight y + weight z = 2 * Fintype.card P := by
  have hi (i : P) : FieldCW.tensor F 5 (x i) (y i) (z i) ≠ 0 := by
    intro he
    exact h (Finset.prod_eq_zero (Finset.mem_univ i) he)
  calc
    weight x + weight y + weight z =
        ∑ i, (CWLeafStatistics.weight (x i) + CWLeafStatistics.weight (y i) +
          CWLeafStatistics.weight (z i)) := by simp [weight, Finset.sum_add_distrib]
    _ = ∑ _i : P, 2 := Finset.sum_congr rfl (fun i _ => site_weight_support _ _ _ (hi i))
    _ = 2 * Fintype.card P := by simp [Nat.mul_comm]

def shapeTensor (P : Type*) [Fintype P] (g : Fin 3 → ℕ) :
    Tensor F (P → Fin 7) (P → Fin 7) (P → Fin 7) :=
  fun x y z => if weight x = g 0 ∧ weight y = g 1 ∧ weight z = g 2
    then strand P x y z else 0

end MatrixMultiplication.CWStrands






namespace MatrixMultiplication.CWCoarseIndices

open MatrixMultiplication.Foundation CWStrands
open scoped BigOperators

theorem label_weight_le_two : ∀ x : Fin 7, CWLeafStatistics.weight x ≤ 2 := by
  decide +kernel

theorem weight_le {P : Type*} [Fintype P] (w : P → Fin 7) :
    weight w ≤ 2 * Fintype.card P := by
  calc
    weight w ≤ ∑ _i : P, 2 := Finset.sum_le_sum fun i _ => label_weight_le_two (w i)
    _ = _ := by simp [Nat.mul_comm]

def coarseIndex {P : Type*} [Fintype P] (hP : Fintype.card P ≤ 8)
    (w : P → Fin 7) : Fin 17 := ⟨weight w, by have := weight_le w; omega⟩

theorem strand_coarse_support {F P : Type*} [CommRing F] [Fintype P]
    (hP : Fintype.card P ≤ 8) (x y z : P → Fin 7)
    (h : strand (F := F) P x y z ≠ 0) :
    (coarseIndex hP x).val + (coarseIndex hP y).val + (coarseIndex hP z).val =
      2 * Fintype.card P := strand_support x y z h

end MatrixMultiplication.CWCoarseIndices






namespace MatrixMultiplication.JointCanonicalCW

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization
open CWStrands HistorySymmetry InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ)
    (hleft : ∀ h, leftLength h ≤ 8)

abbrev Left (h : H) := Fin (leftLength h) → Fin 7
abbrev Right (h : H) := Fin (rightLength h) → Fin 7

def shapeNat (u : Shape) : Fin 3 → ℕ := fun s => (shapeSide s u).val

def coarse (_s : Fin 3) (h : H) (w : Left leftLength h × Right rightLength h) : Fin 17 :=
  CWCoarseIndices.coarseIndex (by simpa using hleft h) w.1

end MatrixMultiplication.JointCanonicalCW






namespace MatrixMultiplication.CWWindowedLeaves

open MatrixMultiplication.Foundation CWStrands CWLeafRestrictions InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev Raw (n : ℕ) := Fin n → Fin 7

end MatrixMultiplication.CWWindowedLeaves






namespace MatrixMultiplication.CWCompleteStatistics

open CWWindowedLeaves CWLeafStatistics CWStrands AllFieldParameters
open scoped BigOperators

attribute [local instance] Classical.propDecidable

def pairEquiv : Raw 2 ≃ (Fin 7 × Fin 7) where
  toFun w := (w 0, w 1)
  invFun u := (Matrix.vecCons (u.1) (Matrix.vecCons (u.2) Matrix.vecEmpty))
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv u := by cases u; rfl

def orderedEquiv : Raw 4 ≃ ((Fin 7 × Fin 7) × (Fin 7 × Fin 7)) where
  toFun w := ((w 0, w 1), (w 2, w 3))
  invFun u := (Matrix.vecCons (u.1.1) (Matrix.vecCons (u.1.2) (Matrix.vecCons (u.2.1) (Matrix.vecCons (u.2.2) Matrix.vecEmpty))))
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv u := by cases u with | mk u v => cases u; cases v; rfl

def twoStatistic (w : Raw 2) : Fin 6 := pairStatistic (pairEquiv w)
def fourStatistic (w : Raw 4) : Fin 6 × Fin 6 :=
  (pairStatistic (orderedEquiv w).1, pairStatistic (orderedEquiv w).2)

def complementStatistic : Fin 6 ≃ Fin 6 :=
  { toFun := kappa
    invFun := kappa
    left_inv := kappa_involution
    right_inv := kappa_involution }

def orderedComplementStatistic : (Fin 6 × Fin 6) ≃ (Fin 6 × Fin 6) :=
  Equiv.prodCongr complementStatistic complementStatistic

end MatrixMultiplication.CWCompleteStatistics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.Staggering

abbrev Capacity := Fin 3 → ℝ

end MatrixMultiplication.Staggering

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.FiniteSchedule

open Staggering

def lotTick {K : ℕ} (j : Fin K) (stage : Fin 3) : ℕ := j.val + stage.val

end MatrixMultiplication.FiniteSchedule

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.PhysicalOrders

open Staggering

abbrev PhysicalOrder := Equiv.Perm (Fin 3)

theorem card_physical_orders : Fintype.card PhysicalOrder = 6 := by
  norm_num [PhysicalOrder, Fintype.card_perm, Nat.factorial_succ]

end MatrixMultiplication.PhysicalOrders

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

structure Allocation where
  mass : Fin 3 → ℚ
  positive : ∀ i, 0 < mass i
  total : ∑ i, mass i = 1

abbrev Placement := PhysicalOrders.PhysicalOrder
abbrev Initial (K : ℕ) := Fin K × Fin sortedInitial.length

def initialShape {K : ℕ} (h : Initial K) : Shape := sortedInitial.get h.2

theorem initialShape_mem {K : ℕ} (h : Initial K) : initialShape h ∈ sortedInitial :=
  List.get_mem _ _

abbrev InitialPositive (K : ℕ) := {h : Initial K // initialShape h ∈ positiveInitial}

abbrev ASplit {K : ℕ} (h : InitialPositive K) := Fin (below (initialShape h.val)).length
abbrev AfterA (K : ℕ) := Σ h : InitialPositive K, ASplit h × Bool

def aSplit {K : ℕ} (h : AfterA K) : Shape :=
  (below (initialShape h.1.val)).get h.2.1

def halfShape (parent left : Shape) (right : Bool) : Shape :=
  if right then complement parent left else left

def aShape {K : ℕ} (h : AfterA K) : Shape :=
  halfShape (initialShape h.1.val) (aSplit h) h.2.2

theorem aSplit_mem {K : ℕ} (h : AfterA K) : aSplit h ∈ below (initialShape h.1.val) :=
  List.get_mem _ _

abbrev APositive (K : ℕ) := {h : AfterA K // aShape h ∈ positiveSecond}
abbrev BSplit {K : ℕ} (h : APositive K) := Fin (below (aShape h.val)).length
abbrev AfterB (K : ℕ) := Σ h : APositive K, BSplit h × Bool

def bSplit {K : ℕ} (h : AfterB K) : Shape :=
  (below (aShape h.1.val)).get h.2.1

def bShape {K : ℕ} (h : AfterB K) : Shape :=
  halfShape (aShape h.1.val) (bSplit h) h.2.2

theorem bSplit_mem {K : ℕ} (h : AfterB K) : bSplit h ∈ below (aShape h.1.val) :=
  List.get_mem _ _

theorem bShape_mem {K : ℕ} (h : AfterB K) : bShape h ∈ below (aShape h.1.val) := by
  have hc := (stageB_support_complement _ h.1.property _ (bSplit_mem h)).1
  cases hh : h.2.2 <;> simp [bShape, halfShape, hh, bSplit_mem h, hc]

theorem stageB_children_size : ∀ t ∈ positiveSecond, ∀ u ∈ below t, u ∈ shapes 4 := by
  decide +kernel

theorem bShape_size {K : ℕ} (h : AfterB K) : bShape h ∈ shapes 4 :=
  stageB_children_size _ h.1.property _ (bShape_mem h)

abbrev BPositive (K : ℕ) := {h : AfterB K // positive (bShape h) = true}
abbrev PartC (K : ℕ) := BPositive K × Fin 3
abbrev AfterC (K : ℕ) := PartC K × Fin 4 × Bool

def cParameterParent {K : ℕ} (h : PartC K) : Shape := aShape h.1.val.1.val
def cShapeParent {K : ℕ} (h : PartC K) : Shape := bShape h.1.val

def cSplit {K : ℕ} (h : AfterC K) : Shape := stageCAtom (cShapeParent h.1) h.2.1

def cShape {K : ℕ} (h : AfterC K) : Shape :=
  halfShape (cShapeParent h.1) (cSplit h) h.2.2

instance initialPositiveFintype (K : ℕ) : Fintype (InitialPositive K) :=
  Fintype.ofFinite _

instance aPositiveFintype (K : ℕ) : Fintype (APositive K) :=
  Fintype.ofFinite _

instance bPositiveFintype (K : ℕ) : Fintype (BPositive K) :=
  Fintype.ofFinite _

inductive CanonicalHistory (K : ℕ) where
  | initial (h : Initial K)
  | afterA (h : AfterA K)
  | afterB (h : AfterB K)
  | partC (h : PartC K)
  | afterC (h : AfterC K)
  deriving Fintype

abbrev History (K : ℕ) := CanonicalHistory K × Placement

def initialAmount {K : ℕ} (h : Initial K) : ℚ := initialLaw (initialShape h)
def aAmount {K : ℕ} (h : AfterA K) : ℚ :=
  initialAmount h.1.val * stageALaw (initialShape h.1.val) (aSplit h)
def bAmount {K : ℕ} (h : AfterB K) : ℚ :=
  aAmount h.1.val * stageBLaw (aShape h.1.val) (bSplit h)
def partAmount {K : ℕ} (allocation : Allocation) (h : PartC K) : ℚ :=
  bAmount h.1.val * allocation.mass h.2
def cAmount {K : ℕ} (allocation : Allocation) (h : AfterC K) : ℚ :=
  partAmount allocation h.1 * stageCWeight (cParameterParent h.1) (cShapeParent h.1) h.2.1

def canonicalAmount {K : ℕ} (allocation : Allocation) : CanonicalHistory K → ℚ
  | .initial h => initialAmount h
  | .afterA h => aAmount h
  | .afterB h => bAmount h
  | .partC h => partAmount allocation h
  | .afterC h => cAmount allocation h

def amount {K : ℕ} (allocation : Allocation) (h : History K) : ℚ :=
  canonicalAmount allocation h.1 / 6

theorem initialAmount_pos {K : ℕ} (h : Initial K) : 0 < initialAmount h :=
  initialLaw_positive _ (initialShape_mem h)

theorem aAmount_pos {K : ℕ} (h : AfterA K) : 0 < aAmount h :=
  mul_pos (initialAmount_pos _) (stageALaw_positive _ _ (aSplit_mem h))

theorem bAmount_pos {K : ℕ} (h : AfterB K) : 0 < bAmount h :=
  mul_pos (aAmount_pos _) (stageBLaw_positive _ _ (bSplit_mem h))

theorem partAmount_pos {K : ℕ} (allocation : Allocation) (h : PartC K) :
    0 < partAmount allocation h := mul_pos (bAmount_pos _) (allocation.positive _)

theorem cAmount_nonneg {K : ℕ} (allocation : Allocation) (h : AfterC K) :
    0 ≤ cAmount allocation h :=
  mul_nonneg (partAmount_pos allocation _).le (stageCWeight_nonnegative _ _ _)

theorem amount_nonneg {K : ℕ} (allocation : Allocation) (h : History K) :
    0 ≤ amount allocation h := by
  apply div_nonneg _ (by norm_num)
  cases h.1 with
  | initial h => exact (initialAmount_pos h).le
  | afterA h => exact (aAmount_pos h).le
  | afterB h => exact (bAmount_pos h).le
  | partC h => exact (partAmount_pos allocation h).le
  | afterC h => exact cAmount_nonneg allocation h

theorem sum_placement_amount {K : ℕ} (allocation : Allocation) (h : CanonicalHistory K) :
    ∑ phi : Placement, amount allocation (h, phi) = canonicalAmount allocation h := by
  simp only [amount, Finset.sum_const, Finset.card_univ,
    PhysicalOrders.card_physical_orders, nsmul_eq_mul]
  norm_num
  ring

theorem initial_amount_sum (K : ℕ) (j : Fin K) :
    ∑ g : Fin sortedInitial.length, initialAmount (j, g) = 1 := by
  change (∑ g : Fin sortedInitial.length, initialLaw sortedInitial[g.val]) = 1
  rw [Fin.sum_univ_fun_getElem]
  exact initialLaw_normalized

theorem root_mass_sum_lot {K : ℕ} (allocation : Allocation) (j : Fin K) :
    (∑ g : Fin sortedInitial.length, ∑ phi : Placement,
      amount allocation (.initial (j, g), phi)) = 1 := by
  simp only [sum_placement_amount, canonicalAmount]
  exact initial_amount_sum K j

def population {K : ℕ} (allocation : Allocation) (dilation : ℕ) : History K → ℕ :=
  AllFieldPopulationCounts.count (amount allocation) dilation

def populationLength {K : ℕ} (allocation : Allocation) (dilation : ℕ) : ℕ :=
  AllFieldPopulationCounts.blockLength (amount (K := K) allocation) dilation

theorem population_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ) (h : History K) :
    (population allocation dilation h : ℚ) =
      (populationLength (K := K) allocation dilation : ℚ) * amount allocation h :=
  AllFieldPopulationCounts.count_cast_blockLength _ (amount_nonneg allocation) dilation h

theorem initial_population_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) :
    (∑ g : Fin sortedInitial.length, ∑ phi : Placement,
      population allocation dilation (.initial (j, g), phi)) =
        populationLength (K := K) allocation dilation := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, population_cast, ← Finset.mul_sum,
    root_mass_sum_lot allocation j, mul_one]

theorem a_half_counts_eq {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : InitialPositive K) (k : ASplit h) (phi : Placement) :
    population allocation dilation (.afterA ⟨h, k, false⟩, phi) =
      population allocation dilation (.afterA ⟨h, k, true⟩, phi) :=
  AllFieldPopulationCounts.count_eq_of_mass_eq _ (amount_nonneg allocation) dilation rfl

theorem b_half_counts_eq {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : APositive K) (k : BSplit h) (phi : Placement) :
    population allocation dilation (.afterB ⟨h, k, false⟩, phi) =
      population allocation dilation (.afterB ⟨h, k, true⟩, phi) :=
  AllFieldPopulationCounts.count_eq_of_mass_eq _ (amount_nonneg allocation) dilation rfl

theorem c_half_counts_eq {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PartC K) (k : Fin 4) (phi : Placement) :
    population allocation dilation (.afterC (h, k, false), phi) =
      population allocation dilation (.afterC (h, k, true), phi) :=
  AllFieldPopulationCounts.count_eq_of_mass_eq _ (amount_nonneg allocation) dilation rfl

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def initialAncestor {K : ℕ} : CanonicalHistory K → Initial K
  | .initial h => h
  | .afterA h => h.1.val
  | .afterB h => h.1.val.1.val
  | .partC h => h.1.val.1.val.1.val
  | .afterC h => h.1.1.val.1.val.1.val

inductive Work (K : ℕ) where
  | stageA (h : InitialPositive K)
  | stageB (h : APositive K)
  | stageC (h : PartC K)
  deriving Fintype

def Work.source {K : ℕ} : Work K → CanonicalHistory K
  | .stageA h => .initial h.val
  | .stageB h => .afterA h.val
  | .stageC h => .partC h

def Work.stage {K : ℕ} : Work K → Fin 3
  | .stageA _ => 0
  | .stageB _ => 1
  | .stageC _ => 2

def Work.lot {K : ℕ} (w : Work K) : Fin K := (initialAncestor w.source).1

def Work.halfLength {K : ℕ} : Work K → ℕ
  | .stageA _ => 4
  | .stageB _ => 2
  | .stageC _ => 1

def Work.parentShape {K : ℕ} : Work K → Shape
  | .stageA h => initialShape h.val
  | .stageB h => aShape h.val
  | .stageC h => cShapeParent h

def Work.Branch {K : ℕ} : Work K → Type
  | .stageA h => ASplit h
  | .stageB h => BSplit h
  | .stageC _ => Fin 4

instance instFintypeBranch {K : ℕ} (w : Work K) : Fintype w.Branch := by
  cases w <;> dsimp [Work.Branch] <;> infer_instance

def Work.child {K : ℕ} (w : Work K) (b : w.Branch) (right : Bool) : CanonicalHistory K :=
  match w with
  | .stageA h => .afterA ⟨h, b, right⟩
  | .stageB h => .afterB ⟨h, b, right⟩
  | .stageC h => .afterC (h, b, right)

def Work.splitShape {K : ℕ} (w : Work K) (b : w.Branch) : Shape :=
  match w with
  | .stageA h => aSplit ⟨h, b, false⟩
  | .stageB h => bSplit ⟨h, b, false⟩
  | .stageC h => cSplit (h, b, false)

abbrev PlacedWork (K : ℕ) := Work K × Placement
abbrev Active (K tick : ℕ) := {w : PlacedWork K //
  FiniteSchedule.lotTick w.1.lot w.1.stage = tick}

def branchPopulation {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) : ℕ :=
  population allocation dilation (w.1.child b false, w.2)

theorem branchPopulation_half {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool) :
    population allocation dilation (w.1.child b right, w.2) =
      branchPopulation allocation dilation w b := by
  rcases w with ⟨w, phi⟩
  cases right with
  | false => rfl
  | true =>
      cases w with
      | stageA h => exact (a_half_counts_eq allocation dilation h b phi).symm
      | stageB h => exact (b_half_counts_eq allocation dilation h b phi).symm
      | stageC h => exact (c_half_counts_eq allocation dilation h b phi).symm

def resident {K : ℕ} (tick : ℕ) : CanonicalHistory K → Prop
  | .initial h => initialShape h ∈ positiveInitial → tick ≤ h.1.val
  | .afterA h => h.1.val.1.val + 1 ≤ tick ∧
      (aShape h ∈ positiveSecond → tick ≤ h.1.val.1.val + 1)
  | .afterB h => h.1.val.1.val.1.val + 2 ≤ tick ∧ positive (bShape h) ≠ true
  | .partC h => tick = h.1.val.1.val.1.val.1.val + 2
  | .afterC h => h.1.1.val.1.val.1.val.1.val + 3 ≤ tick

abbrev State (K tick : ℕ) := {h : History K // resident tick h.1}

theorem work_source_resident {K : ℕ} (w : Work K) :
    resident (FiniteSchedule.lotTick w.lot w.stage) w.source := by
  cases w with
  | stageA h => simp [resident, Work.source, Work.lot, Work.stage,
      initialAncestor, FiniteSchedule.lotTick]
  | stageB h => simp [resident, Work.source, Work.lot, Work.stage,
      initialAncestor, FiniteSchedule.lotTick]
  | stageC h => simp [resident, Work.source, Work.lot, Work.stage,
      initialAncestor, FiniteSchedule.lotTick]

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def shapeCounts {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (u : JointPopulation.Shape) : ℕ :=
  ∑ i, if code i = u then weight i else 0

theorem shapeCounts_sum {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) : ∑ u, shapeCounts code weight u = ∑ i, weight i := by
  unfold shapeCounts
  rw [Finset.sum_comm]
  simp

theorem shapeCounts_positive {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (u : JointPopulation.Shape) (hu : 0 < shapeCounts code weight u) :
    ∃ i, code i = u ∧ 0 < weight i := by
  by_contra hn
  have hz : shapeCounts code weight u = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    split_ifs with heq
    · by_contra hne
      exact hn ⟨i, heq, Nat.pos_of_ne_zero hne⟩
    · rfl
  omega

theorem shapeCounts_at {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (hi : Function.Injective code) (i : I) :
    shapeCounts code weight (code i) = weight i := by
  unfold shapeCounts
  simp only [hi.eq_iff]
  simp

theorem Work.splitShape_spec {K : ℕ} (w : Work K) (b : w.Branch) :
    ShapeBounded (w.splitShape b) ∧ shapeTotal (w.splitShape b) = 2 * w.halfLength := by
  cases w with
  | stageA h => exact stageA_shape_spec _ _ h.property (aSplit_mem ⟨h, b, false⟩)
  | stageB h => exact stageB_shape_spec _ _ h.property (bSplit_mem ⟨h, b, false⟩)
  | stageC h => exact stageC_shape_spec _ (bShape_size h.1.val) h.1.property b

theorem Work.splitShape_injective {K : ℕ} (w : Work K) :
    Function.Injective w.splitShape := by
  cases w with
  | stageA h => exact stageA_get_injective _ h.property
  | stageB h => exact stageB_get_injective _ h.property
  | stageC h => exact stageCAtom_injective _ (bShape_size h.1.val) h.1.property

def branchShape {K : ℕ} (w : PlacedWork K) (b : w.1.Branch) : JointPopulation.Shape :=
  encodePhysicalShape w.2 (w.1.splitShape b) (w.1.splitShape_spec b).1

theorem branchShape_injective {K : ℕ} (w : PlacedWork K) :
    Function.Injective (branchShape w) := by
  intro a b hab
  exact w.1.splitShape_injective (encodePhysicalShape_inj w.2 hab)

def jointCounts {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : JointPopulation.Shape → ℕ :=
  shapeCounts (branchShape w) (branchPopulation allocation dilation w)

def activeCounts {K tick : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) : JointPopulation.Shape → ℕ := jointCounts allocation dilation h.val

def activeParentShape {K tick : ℕ} (h : Active K tick) : Shape :=
  physicalShape h.val.2 h.val.1.parentShape

def activeHalfLength {K tick : ℕ} (h : Active K tick) : ℕ := h.val.1.halfLength

theorem jointCounts_at {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    jointCounts allocation dilation w (branchShape w b) =
      branchPopulation allocation dilation w b :=
  shapeCounts_at _ _ (branchShape_injective w) b

def shapePositionMap {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) :
    (Σ b : w.1.Branch, Fin (branchPopulation allocation dilation w b)) →
      (Σ u : JointPopulation.Shape, Fin (jointCounts allocation dilation w u)) :=
  fun p => ⟨branchShape w p.1,
    ⟨p.2.val, by rw [jointCounts_at]; exact p.2.isLt⟩⟩

theorem shapePositionMap_injective {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : Function.Injective (shapePositionMap allocation dilation w) := by
  rintro ⟨b, i⟩ ⟨c, j⟩ heq
  have hbc : b = c := branchShape_injective w (congrArg Sigma.fst heq)
  subst c
  have hij : i.val = j.val := congrArg (fun p => p.2.val) heq
  have : i = j := Fin.ext hij
  subst j
  rfl

theorem shapePositionMap_surjective {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) : Function.Surjective (shapePositionMap allocation dilation w) := by
  rintro ⟨u, i⟩
  obtain ⟨b, heq, hb⟩ := shapeCounts_positive _ _ u (Nat.zero_lt_of_lt i.isLt)
  subst u
  refine ⟨⟨b, ⟨i.val, ?_⟩⟩, ?_⟩
  · simpa only [jointCounts_at] using i.isLt
  · rfl

def branchPositionEquiv {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) :
    (Σ u : JointPopulation.Shape, Fin (jointCounts allocation dilation w u)) ≃
      (Σ b : w.1.Branch, Fin (branchPopulation allocation dilation w b)) :=
  (Equiv.ofBijective (shapePositionMap allocation dilation w)
    ⟨shapePositionMap_injective allocation dilation w,
      shapePositionMap_surjective allocation dilation w⟩).symm

@[simp] theorem branchPositionEquiv_shape {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K)
    (p : Σ u : JointPopulation.Shape, Fin (jointCounts allocation dilation w u)) :
    branchShape w (branchPositionEquiv allocation dilation w p).1 = p.1 := by
  exact congrArg Sigma.fst ((branchPositionEquiv allocation dilation w).symm_apply_apply p)

def rootShape {K : ℕ} (h : Initial K) (phi : Placement) : JointPopulation.Shape :=
  encodePhysicalShape phi (initialShape h) (root_shape_spec _ (initialShape_mem h)).1

def initialJointCounts {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) : JointPopulation.Shape → ℕ :=
  shapeCounts (fun p : Fin sortedInitial.length × Placement => rootShape (j, p.1) p.2)
    (fun p => population allocation dilation (.initial (j, p.1), p.2))

theorem initialJointCounts_sum {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) : ∑ u, initialJointCounts allocation dilation j u =
      populationLength (K := K) allocation dilation := by
  rw [initialJointCounts, shapeCounts_sum, Fintype.sum_prod_type]
  exact initial_population_sum allocation dilation j

theorem initialJointCounts_support {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) (u : JointPopulation.Shape)
    (hu : 0 < initialJointCounts allocation dilation j u) :
    u.1.val + u.2.1.val + u.2.2.val = 16 := by
  obtain ⟨p, rfl, _⟩ := shapeCounts_positive _ _ u hu
  exact (encodePhysicalShape_total _ _ _).trans (root_shape_spec _ (initialShape_mem _)).2

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters

def priorityPermutation (k : Fin 6) : Placement :=
  (Matrix.vecCons (Equiv.refl (Fin 3)) (Matrix.vecCons (Equiv.swap 1 2) (Matrix.vecCons (Equiv.swap 0 1) (Matrix.vecCons ((Equiv.swap 0 1).trans (Equiv.swap 0 2)) (Matrix.vecCons ((Equiv.swap 0 2).trans (Equiv.swap 0 1)) (Matrix.vecCons (Equiv.swap 0 2) Matrix.vecEmpty)))))) k

def stageBRepresentatives : List Shape :=
  [shape 1 1 6, shape 1 2 5, shape 1 3 4, shape 2 2 4, shape 3 2 3]

def readInPriority (t : Shape) (rho : Placement) : Shape := fun i => t (rho i)

def stageBPriorityIndex (t : Shape) : Fin 6 :=
  ((List.finRange 6).find? fun k =>
    stageBRepresentatives.contains (readInPriority t (priorityPermutation k))).getD 0

def stageBPriority (t : Shape) : Placement := priorityPermutation (stageBPriorityIndex t)

def cPriorityIndex : Fin 3 → Fin 3 → Fin 6 :=
  (Matrix.vecCons ((Matrix.vecCons (0) (Matrix.vecCons (2) (Matrix.vecCons (3) Matrix.vecEmpty)))) (Matrix.vecCons ((Matrix.vecCons (2) (Matrix.vecCons (0) (Matrix.vecCons (1) Matrix.vecEmpty)))) (Matrix.vecCons ((Matrix.vecCons (4) (Matrix.vecCons (1) (Matrix.vecCons (0) Matrix.vecEmpty)))) Matrix.vecEmpty)))

def stageCPriorityLabel (distinguished part : Fin 3) : Placement :=
  priorityPermutation (cPriorityIndex distinguished part)

def cPriority {K : ℕ} (h : PartC K) : Placement :=
  stageCPriorityLabel (stageCDistinguished (cShapeParent h)) h.2

def Work.priority {K : ℕ} : Work K → Placement
  | .stageA _ => Equiv.refl (Fin 3)
  | .stageB h => stageBPriority (aShape h.val)
  | .stageC h => cPriority h

@[simp] theorem Work.priority_stageA {K : ℕ} (h : InitialPositive K) :
    (Work.stageA h).priority = Equiv.refl (Fin 3) := rfl

def PlacedWork.physicalOrder {K : ℕ} (w : PlacedWork K) : Placement :=
  w.1.priority.trans w.2

abbrev ActiveOrder (K tick : ℕ) (sigma : Placement) :=
  {w : Active K tick // w.val.physicalOrder = sigma}

def workAmount {K : ℕ} (allocation : Allocation) (w : Work K) : ℝ :=
  canonicalAmount allocation w.source

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters CWStrands CWWindowedLeaves
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def Work.Statistic {K : ℕ} : Work K → Type
  | .stageA _ => PairSlot
  | .stageB _ => Fin 6
  | .stageC _ => PUnit

instance instFintypeStatistic {K : ℕ} (w : Work K) : Fintype w.Statistic := by
  cases w <;> dsimp [Work.Statistic] <;> infer_instance

instance instDecidableEqStatistic {K : ℕ} (w : Work K) : DecidableEq w.Statistic := Classical.decEq _

def Work.statistic {K : ℕ} (w : Work K) : Raw w.halfLength → w.Statistic :=
  match w with
  | .stageA _ => CWCompleteStatistics.fourStatistic
  | .stageB _ => CWCompleteStatistics.twoStatistic
  | .stageC _ => fun _ => PUnit.unit

def Work.childLaw {K : ℕ} (w : Work K) (u : Shape) (side : Fin 3) :
    w.Statistic → ℚ :=
  match w with
  | .stageA _ => halfLaw u side
  | .stageB h => littleLaw (aShape h.val) u side
  | .stageC _ => fun _ => 1

def canonicalChildShape {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape) : Shape :=
  fun i => decodeShape u (w.2 i)

@[simp] theorem canonicalChildShape_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) : canonicalChildShape w (branchShape w b) = w.1.splitShape b := by
  funext i
  simp [canonicalChildShape, branchShape, physicalShape]

def placedChildLawRat {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) (right : Bool) : w.1.Statistic → ℚ :=
  w.1.childLaw (halfShape w.1.parentShape (canonicalChildShape w u) right)
    (w.2.symm side)

def childLawRat {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) : w.1.Statistic → ℚ := placedChildLawRat w u side false

def rightChildLawRat {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) : w.1.Statistic → ℚ := placedChildLawRat w u side true

@[simp] theorem placedChildLawRat_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) (side : Fin 3) (right : Bool) :
    placedChildLawRat w (branchShape w b) side right =
      w.1.childLaw (halfShape w.1.parentShape (w.1.splitShape b) right)
        (w.2.symm side) := by
  simp only [placedChildLawRat, canonicalChildShape_branchShape]

def childLaw {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) (a : w.1.Statistic) : ℝ := childLawRat w u side a

def rightChildLaw {K : ℕ} (w : PlacedWork K) (u : JointPopulation.Shape)
    (side : Fin 3) (a : w.1.Statistic) : ℝ := rightChildLawRat w u side a

abbrev ActiveStatistic {K tick : ℕ} (h : Active K tick) := h.val.1.Statistic

def activeStatistic {K tick : ℕ} (h : Active K tick) :
    Raw (activeHalfLength h) → ActiveStatistic h := h.val.1.statistic

end MatrixMultiplication.AllFieldHistory

namespace MatrixMultiplication.AllFieldHistoryChildLaws

open AllFieldHistory
open scoped BigOperators

abbrev Statistic {K tick : ℕ} (h : Active K tick) := ActiveStatistic h

abbrev statistic {K tick : ℕ} (h : Active K tick) :
    CWWindowedLeaves.Raw (activeHalfLength h) → Statistic h := activeStatistic h

abbrev leftLaw {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) : Statistic h → ℝ := childLaw h.val u side

abbrev rightLaw {K tick : ℕ} (h : Active K tick) (u : JointPopulation.Shape)
    (side : Fin 3) : Statistic h → ℝ := rightChildLaw h.val u side

end MatrixMultiplication.AllFieldHistoryChildLaws

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_InitialHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem shapeCounts_fiber {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (u : JointPopulation.Shape) :
    shapeCounts code weight u = ∑ i : {i : I // code i = u}, weight i.val := by
  unfold shapeCounts
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro i; simp) weight

def shapeCountFiberEquiv {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (u : JointPopulation.Shape) :
    Fin (shapeCounts code weight u) ≃
      (Σ i : {i : I // code i = u}, Fin (weight i.val)) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sigma, shapeCounts_fiber])

abbrev InitialPlacement (K : ℕ) := Initial K × Placement

abbrev InitialShapeFiber {K : ℕ} (j : Fin K) (u : JointPopulation.Shape) :=
  {p : Fin sortedInitial.length × Placement // rootShape (j, p.1) p.2 = u}

def initialClassPositionEquiv {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) (u : JointPopulation.Shape) :
    Fin (initialJointCounts allocation dilation j u) ≃
      (Σ p : InitialShapeFiber j u,
        Fin (population allocation dilation (.initial (j, p.val.1), p.val.2))) :=
  shapeCountFiberEquiv _ _ u

theorem initialClassPosition_shape {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) (u : JointPopulation.Shape)
    (i : Fin (initialJointCounts allocation dilation j u)) :
    rootShape (j, (initialClassPositionEquiv allocation dilation j u i).1.val.1)
      (initialClassPositionEquiv allocation dilation j u i).1.val.2 = u :=
  (initialClassPositionEquiv allocation dilation j u i).1.property

def initialStateEquiv (K : ℕ) : State K 0 ≃ InitialPlacement K where
  toFun h := by
    rcases h with ⟨⟨h, phi⟩, hr⟩
    cases h with
    | initial g => exact (g, phi)
    | afterA a => have := hr.1; dsimp [resident] at hr; omega
    | afterB b => have := hr.1; dsimp [resident] at hr; omega
    | partC c => dsimp [resident] at hr; omega
    | afterC c => dsimp [resident] at hr; omega
  invFun h := ⟨(.initial h.1, h.2), fun _ => Nat.zero_le _⟩
  left_inv h := by
    rcases h with ⟨⟨h, phi⟩, hr⟩
    cases h with
    | initial g => rfl
    | afterA a => have := hr.1; dsimp [resident] at hr; omega
    | afterB b => have := hr.1; dsimp [resident] at hr; omega
    | partC c => dsimp [resident] at hr; omega
    | afterC c => dsimp [resident] at hr; omega
  right_inv h := rfl

end MatrixMultiplication.AllFieldHistory

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryPositions
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def due {K : ℕ} (tick : ℕ) : CanonicalHistory K → Prop
  | .initial h => initialShape h ∈ positiveInitial ∧ tick = h.1.val
  | .afterA h => aShape h ∈ positiveSecond ∧ tick = h.1.val.1.val + 1
  | .afterB _ => False
  | .partC h => tick = h.1.val.1.val.1.val.1.val + 2
  | .afterC _ => False

def produced {K : ℕ} (tick : ℕ) : CanonicalHistory K → Prop
  | .initial _ => False
  | .afterA h => tick = h.1.val.1.val
  | .afterB h => tick = h.1.val.1.val.1.val + 1 ∧ positive (bShape h) ≠ true
  | .partC h => tick = h.1.val.1.val.1.val.1.val + 1
  | .afterC h => tick = h.1.1.val.1.val.1.val.1.val + 2

abbrev Carried (K tick : ℕ) := {h : State K tick // ¬ due tick h.val.1}
abbrev Produced (K tick : ℕ) := {h : History K // produced tick h.1}

theorem produced_not_resident {K tick : ℕ} (h : CanonicalHistory K)
    (hp : produced tick h) : ¬ resident tick h := by
  cases h with
  | initial h => exact False.elim hp
  | afterA h => simp only [produced] at hp; simp only [resident]; omega
  | afterB h => simp only [produced] at hp; simp only [resident]; omega
  | partC h => simp only [produced] at hp; simp only [resident]; omega
  | afterC h => simp only [produced] at hp; simp only [resident]; omega

theorem resident_succ_iff {K tick : ℕ} (h : CanonicalHistory K) :
    resident (tick + 1) h ↔ (resident tick h ∧ ¬ due tick h) ∨ produced tick h := by
  cases h with
  | initial h =>
      by_cases hp : initialShape h ∈ positiveInitial
      · simp only [resident, due, produced, hp, true_implies, true_and, or_false]
        omega
      · simp [resident, due, produced, hp]
  | afterA h =>
      by_cases hp : aShape h ∈ positiveSecond
      · simp only [resident, due, produced, hp, true_implies, true_and]
        omega
      · simp only [resident, due, produced, hp, false_implies, and_true, false_and,
          not_false_eq_true]
        omega
  | afterB h =>
      by_cases hp : positive (bShape h) = true
      · simp [resident, due, produced, hp]
      · simp [resident, due, produced, hp, ne_eq]
        omega
  | partC h => simp only [resident, due, produced]; omega
  | afterC h => simp only [resident, due, produced, not_false_eq_true, and_true]; omega

def stateTransitionForward {K tick : ℕ} (h : State K (tick + 1)) :
    Carried K tick ⊕ Produced K tick := by
  by_cases hr : resident tick h.val.1
  · refine Sum.inl ⟨⟨h.val, hr⟩, ?_⟩
    rcases (resident_succ_iff h.val.1).mp h.property with hc | hp
    · exact hc.2
    · exact False.elim (produced_not_resident _ hp hr)
  · refine Sum.inr ⟨h.val, ?_⟩
    rcases (resident_succ_iff h.val.1).mp h.property with hc | hp
    · exact False.elim (hr hc.1)
    · exact hp

def stateTransitionBackward {K tick : ℕ} : Carried K tick ⊕ Produced K tick →
    State K (tick + 1)
  | .inl h => ⟨h.val.val, (resident_succ_iff _).mpr (.inl ⟨h.val.property, h.property⟩)⟩
  | .inr h => ⟨h.val, (resident_succ_iff _).mpr (.inr h.property)⟩

def stateTransition {K tick : ℕ} : State K (tick + 1) ≃ Carried K tick ⊕ Produced K tick where
  toFun := stateTransitionForward
  invFun := stateTransitionBackward
  left_inv h := by
    unfold stateTransitionForward
    split_ifs <;> rfl
  right_inv h := by
    cases h with
    | inl h => simp [stateTransitionForward, stateTransitionBackward, h.val.property]
    | inr h =>
        have hn := produced_not_resident h.val.1 h.property
        simp [stateTransitionForward, stateTransitionBackward, hn]

abbrev DueState (K tick : ℕ) := {h : State K tick // due tick h.val.1}

def activeToDue {K tick : ℕ} (w : Active K tick) : DueState K tick := by
  refine ⟨⟨(w.val.1.source, w.val.2), ?_⟩, ?_⟩
  · exact Eq.mp (congrArg (fun n => resident n w.val.1.source) w.property)
      (work_source_resident w.val.1)
  · rcases w with ⟨⟨w, phi⟩, hw⟩
    cases w with
    | stageA h => exact ⟨h.property, hw.symm⟩
    | stageB h => exact ⟨h.property, hw.symm⟩
    | stageC h => exact hw.symm

def dueToActive {K tick : ℕ} (h : DueState K tick) : Active K tick := by
  rcases h with ⟨⟨⟨h, phi⟩, hr⟩, hd⟩
  cases h with
  | initial h => exact ⟨(.stageA ⟨h, hd.1⟩, phi), hd.2.symm⟩
  | afterA h => exact ⟨(.stageB ⟨h, hd.1⟩, phi), hd.2.symm⟩
  | afterB h => exact False.elim hd
  | partC h => exact ⟨(.stageC h, phi), hd.symm⟩
  | afterC h => exact False.elim hd

def activeSourceEquiv {K tick : ℕ} : Active K tick ≃ DueState K tick where
  toFun := activeToDue
  invFun := dueToActive
  left_inv w := by
    rcases w with ⟨⟨w, phi⟩, hw⟩
    cases w <;> rfl
  right_inv h := by
    rcases h with ⟨⟨⟨h, phi⟩, hr⟩, hd⟩
    cases h with
    | initial h => rfl
    | afterA h => rfl
    | afterB h => exact False.elim hd
    | partC h => rfl
    | afterC h => exact False.elim hd

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
attribute [local instance] Classical.propDecidable Classical.decEq

def currentShape {K : ℕ} : CanonicalHistory K → Shape
  | .initial h => initialShape h
  | .afterA h => aShape h
  | .afterB h => bShape h
  | .partC h => cShapeParent h
  | .afterC h => cShape h

def currentLength {K : ℕ} : CanonicalHistory K → ℕ
  | .initial _ => 8
  | .afterA _ => 4
  | .afterB _ | .partC _ => 2
  | .afterC _ => 1

def currentPhysicalShape {K : ℕ} (h : History K) : Shape :=
  physicalShape h.2 (currentShape h.1)

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open MatrixMultiplication.Foundation AllFieldParameters CWStrands InheritedMasks
open scoped BigOperators Classical

def ResidentStatistic {K : ℕ} : CanonicalHistory K → Type
  | .initial _ => PUnit
  | .afterA _ => PairSlot
  | .afterB _ | .partC _ => Fin 6
  | .afterC _ => PUnit

instance instDecidableEqResidentStatistic {K : ℕ} (h : CanonicalHistory K) : DecidableEq (ResidentStatistic h) := Classical.decEq _

def residentStatistic {K : ℕ} (h : CanonicalHistory K) :
    (Fin (currentLength h) → Fin 7) → ResidentStatistic h :=
  match h with
  | .initial _ => fun _ => PUnit.unit
  | .afterA _ => CWCompleteStatistics.fourStatistic
  | .afterB _ | .partC _ => CWCompleteStatistics.twoStatistic
  | .afterC _ => fun _ => PUnit.unit

def residentLawRat {K : ℕ} (h : CanonicalHistory K) (canonicalSide : Fin 3) :
    ResidentStatistic h → ℚ :=
  match h with
  | .initial _ => fun _ => 1
  | .afterA h => halfLaw (aShape h) canonicalSide
  | .afterB h => littleLaw (aShape h.1.val) (bShape h) canonicalSide
  | .partC h => littleLaw (cParameterParent h) (cShapeParent h) canonicalSide
  | .afterC _ => fun _ => 1

def residentLaw {K : ℕ} (h : History K) (physicalSide : Fin 3) :
    ResidentStatistic h.1 → ℝ :=
  fun a => residentLawRat h.1 (h.2.symm physicalSide) a

def residentWidth {K : ℕ} (ε : ℝ) : CanonicalHistory K → ℝ
  | .initial _ => 0
  | .afterA _ => ε / 8
  | .afterB _ => ε / 128
  | .partC _ => ε / 256
  | .afterC _ => 0

abbrev HistoryWord {K : ℕ} (allocation : Allocation) (dilation : ℕ) (h : History K) :=
  Fin (population allocation dilation h) → Fin (currentLength h.1) → Fin 7

def residentMask {K : ℕ} (allocation : Allocation) (dilation : ℕ) (ε : ℝ)
    (h : History K) (side : Fin 3) (w : HistoryWord allocation dilation h) : Prop :=
  match h.1 with
  | .initial _ => True
  | .afterC _ => True
  | .afterA _ | .afterB _ | .partC _ =>
      0 < population allocation dilation h →
        typeWindow (residentLaw h side) (residentWidth ε h.1)
          (fun i => residentStatistic h.1 (w i))

def historyTensor (F : Type*) [Field F] {K : ℕ}
    (allocation : Allocation) (dilation : ℕ) (ε : ℝ) (h : History K) :
    Tensor F (HistoryWord allocation dilation h) (HistoryWord allocation dilation h)
      (HistoryWord allocation dilation h) :=
  ExactRecovery.delete
    (Tensor.power (shapeTensor (Fin (currentLength h.1)) (currentPhysicalShape h))
      (population allocation dilation h))
    (residentMask allocation dilation ε h 0) (residentMask allocation dilation ε h 1)
    (residentMask allocation dilation ε h 2)

def stateTensor (F : Type*) [Field F] {K : ℕ}
    (allocation : Allocation) (dilation : ℕ) (ε : ℝ) (tick : ℕ) :
    Tensor F (∀ h : State K tick, HistoryWord allocation dilation h.val)
      (∀ h : State K tick, HistoryWord allocation dilation h.val)
      (∀ h : State K tick, HistoryWord allocation dilation h.val) :=
  CommonDimensions.familyProduct (fun h : State K tick =>
    historyTensor F allocation dilation ε h.val)

@[simp] theorem historyTensor_initial (F : Type*) [Field F] {K : ℕ}
    (allocation : Allocation) (dilation : ℕ) (ε : ℝ) (h : Initial K) (phi : Placement) :
    historyTensor F allocation dilation ε (.initial h, phi) =
      Tensor.power (shapeTensor (Fin 8) (physicalShape phi (initialShape h)))
        (population allocation dilation (.initial h, phi)) := by
  funext x y z
  exact ite_eq_left ⟨trivial, trivial, trivial⟩

@[simp] theorem historyTensor_afterC (F : Type*) [Field F] {K : ℕ}
    (allocation : Allocation) (dilation : ℕ) (ε : ℝ) (h : AfterC K) (phi : Placement) :
    historyTensor F allocation dilation ε (.afterC h, phi) =
      Tensor.power (shapeTensor (Fin 1) (physicalShape phi (cShape h)))
        (population allocation dilation (.afterC h, phi)) := by
  funext x y z
  exact ite_eq_left ⟨trivial, trivial, trivial⟩

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
attribute [local instance] Classical.propDecidable Classical.decEq

def halfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (branchPopulation allocation dilation w b)) :
    Fin (population allocation dilation (w.1.child b right, w.2)) :=
  ⟨i.val, by rw [branchPopulation_half]; exact i.isLt⟩

def unhalfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (population allocation dilation (w.1.child b right, w.2))) :
    Fin (branchPopulation allocation dilation w b) :=
  ⟨i.val, by rw [← branchPopulation_half allocation dilation w b right]; exact i.isLt⟩

@[simp] theorem unhalf_halfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (branchPopulation allocation dilation w b)) :
    unhalfPosition allocation dilation w b right (halfPosition allocation dilation w b right i) = i := rfl

@[simp] theorem half_unhalfPosition {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool)
    (i : Fin (population allocation dilation (w.1.child b right, w.2))) :
    halfPosition allocation dilation w b right (unhalfPosition allocation dilation w b right i) = i := rfl

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_InitialState
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCoarseReorder.tripleSide_reorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

structure AllFieldWitness (F : Type*) [Field F] where
  rows : ℕ
  inner : ℕ
  columns : ℕ
  multiplicity : ℕ
  rankBound : ℕ
  order : ℕ
  degree : ℕ
  rows_pos : 0 < rows
  inner_pos : 0 < inner
  columns_pos : 0 < columns
  multiplicity_pos : 0 < multiplicity
  rankBound_pos : 0 < rankBound
  approximation : Tensor.PolynomialApproximation
    (Tensor.directSum (fun _ : Fin multiplicity =>
      Tensor.matrixCoefficients (K := F) (Fin rows) (Fin inner) (Fin columns)))
    rankBound order degree

end MatrixMultiplication

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AllFieldSource

abbrev Word (K N : ℕ) := Fin (8 * K * N) → Fin 7

abbrev Index (Copies : Type*) (K N : ℕ) := Copies × Word K N

def tensor (F Copies : Type*) [CommRing F] [DecidableEq Copies] (K N : ℕ) :
    Tensor F (Index Copies K N) (Index Copies K N) (Index Copies K N) :=
  Tensor.directSum (fun _ : Copies => Tensor.power (FieldCW.tensor F 5) (8 * K * N))

def rankBudget (Copies : Type*) [Fintype Copies] (K N : ℕ) : ℕ :=
  Fintype.card Copies * ((3 * (8 * K * N) + 1) ^ 2 * 7 ^ (8 * K * N))

theorem rank_bound (F Copies : Type*) [Field F]
    [Fintype Copies] [DecidableEq Copies] (K N : ℕ) :
    Tensor.RankAtMost (tensor F Copies K N) (rankBudget Copies K N) := by
  have h := (Tensor.diagonal_rankAtMost (K := F) Copies).product
    (FieldCW.rank_power F 5 (8 * K * N))
  convert h using 1
  · funext x y z
    simp [tensor, Tensor.directSum, Tensor.product, Tensor.diagonal, ite_mul]
  · rfl

theorem rankBudget_pos (Copies : Type*) [Fintype Copies] (K N : ℕ)
    (hcopies : 0 < Fintype.card Copies) : 0 < rankBudget Copies K N := by
  unfold rankBudget
  exact Nat.mul_pos hcopies
    (Nat.mul_pos (pow_pos (Nat.succ_pos _) _) (pow_pos (by decide) _))

def matrixTarget (F : Type*) [CommSemiring F] (a b c L : ℕ) :=
  Tensor.directSum (fun _ : Fin L =>
    Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin c))

section Consumer

variable {F Copies : Type*} [Field F] [Fintype Copies] [DecidableEq Copies]
variable {K N a b c L : ℕ}

theorem restricted_rank_bound
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z) :
    Tensor.RankAtMost (matrixTarget F a b c L) (rankBudget Copies K N) := by
  have heq : Tensor.restrict A B C (tensor F Copies K N) = matrixTarget F a b c L :=
    funext fun x => funext fun y => funext fun z => hcoeff x y z
  rw [← heq]
  exact (rank_bound F Copies K N).restrict A B C

def restrictedApproximation
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z) :
    Tensor.PolynomialApproximation (matrixTarget F a b c L) (rankBudget Copies K N) 0 0 :=
  Tensor.PolynomialApproximation.ofRankAtMost _ _ (restricted_rank_bound A B C hcoeff)

def ofRestriction
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z)
    (hcopies : 0 < Fintype.card Copies) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hL : 0 < L) : AllFieldWitness F where
  rows := a
  inner := b
  columns := c
  multiplicity := L
  rankBound := rankBudget Copies K N
  order := 0
  degree := 0
  rows_pos := ha
  inner_pos := hb
  columns_pos := hc
  multiplicity_pos := hL
  rankBound_pos := rankBudget_pos Copies K N hcopies
  approximation := restrictedApproximation A B C hcoeff

end Consumer

end MatrixMultiplication.AllFieldSource

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldFiniteFamily

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

variable {F : Type*} [Field F]

structure LocalMap {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (source : Tensor F X Y Z) (target : Tensor F X' Y' Z') where
  x : X' → X → F
  y : Y' → Y → F
  z : Z' → Z → F
  coefficient : Tensor.restrict x y z source = target

namespace LocalMap

variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type}
  [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z']
  {source : Tensor F X Y Z} {middle : Tensor F X' Y' Z'}
  {target : Tensor F X'' Y'' Z''}

def identity (source : Tensor F X Y Z) : LocalMap source source where
  x := fun x s => if s = x then 1 else 0
  y := fun y s => if s = y then 1 else 0
  z := fun z s => if s = z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    rfl

def delete (source : Tensor F X Y Z) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop) :
    LocalMap source (ExactRecovery.delete source px py pz) where
  x := fun x s => if s = x ∧ px x then 1 else 0
  y := fun y s => if s = y ∧ py y then 1 else 0
  z := fun z s => if s = z ∧ pz z then 1 else 0
  coefficient := by
    funext x y z
    by_cases hx : px x <;> by_cases hy : py y <;> by_cases hz : pz z <;>
      simp [Tensor.restrict, ExactRecovery.delete, hx, hy, hz, ite_mul, mul_ite]

def product {U V W U' V' W' : Type}
    [Fintype U] [Fintype V] [Fintype W]
    {other : Tensor F U V W} {otherTarget : Tensor F U' V' W'}
    (first : LocalMap source middle) (second : LocalMap other otherTarget) :
    LocalMap (Tensor.product source other) (Tensor.product middle otherTarget) where
  x := fun x s => first.x x.1 s.1 * second.x x.2 s.2
  y := fun y s => first.y y.1 s.1 * second.y y.2 s.2
  z := fun z s => first.z z.1 s.1 * second.z z.2 s.2
  coefficient := by
    rw [Tensor.restrict_product, first.coefficient, second.coefficient]

def comp (first : LocalMap source middle) (second : LocalMap middle target) :
    LocalMap source target where
  x := Tensor.composeRestrictionMatrix second.x first.x
  y := Tensor.composeRestrictionMatrix second.y first.y
  z := Tensor.composeRestrictionMatrix second.z first.z
  coefficient := by
    rw [← Tensor.restrict_restrict, first.coefficient, second.coefficient]

def withSource (map : LocalMap source middle) (newSource : Tensor F X Y Z)
    (same : newSource = source) : LocalMap newSource middle where
  x := map.x
  y := map.y
  z := map.z
  coefficient := by rw [same]; exact map.coefficient

def ofExists
    (h : ∃ (a : X' → X → F) (b : Y' → Y → F) (c : Z' → Z → F),
      Tensor.restrict a b c source = middle) : LocalMap source middle := by
  choose a b c habc using h
  exact ⟨a, b, c, habc⟩

def parallelCopies (map : LocalMap source middle) (R : Type) [Fintype R] :
    LocalMap (Tensor.directSum (fun _ : R => source))
      (Tensor.directSum (fun _ : R => middle)) where
  x := fun x s => if x.1 = s.1 then map.x x.2 s.2 else 0
  y := fun y s => if y.1 = s.1 then map.y y.2 s.2 else 0
  z := fun z s => if z.1 = s.1 then map.z z.2 s.2 else 0
  coefficient := by
    have h := Replication.restrict_directSum (fun _ : R => source)
      (fun _ => map.x) (fun _ => map.y) (fun _ => map.z)
    simpa only [map.coefficient] using h

def directSum {I : Type} [Fintype I]
    (T : I → Tensor F X Y Z) (Q : I → Tensor F X' Y' Z')
    (maps : ∀ i, LocalMap (T i) (Q i)) :
    LocalMap (Tensor.directSum T) (Tensor.directSum Q) where
  x := fun x s => if x.1 = s.1 then (maps x.1).x x.2 s.2 else 0
  y := fun y s => if y.1 = s.1 then (maps y.1).y y.2 s.2 else 0
  z := fun z s => if z.1 = s.1 then (maps z.1).z z.2 s.2 else 0
  coefficient := by
    have h := Replication.restrict_directSum T
      (fun i => (maps i).x) (fun i => (maps i).y) (fun i => (maps i).z)
    simpa only [fun i => (maps i).coefficient] using h

def selectBranches {I J : Type} [Fintype I] [Fintype J]
    (T : I → Tensor F X Y Z) (select : J → I) (injective : Function.Injective select) :
    LocalMap (Tensor.directSum T) (Tensor.directSum (fun j => T (select j))) where
  x := fun x s => if s = (select x.1, x.2) then 1 else 0
  y := fun y s => if s = (select y.1, y.2) then 1 else 0
  z := fun z s => if s = (select z.1, z.2) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, Tensor.directSum, injective.eq_iff]

def unflatten (source : Tensor F X Y Z) (R I : Type) [Fintype R] [Fintype I] :
    LocalMap (Tensor.directSum (fun _ : R × I => source))
      (Tensor.directSum (fun _ : R => Tensor.directSum (fun _ : I => source))) where
  x := fun x s => if s = ((x.1, x.2.1), x.2.2) then 1 else 0
  y := fun y s => if s = ((y.1, y.2.1), y.2.2) then 1 else 0
  z := fun z s => if s = ((z.1, z.2.1), z.2.2) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, Tensor.directSum, Prod.ext_iff]
    split_ifs <;> aesop

def flatten (source : Tensor F X Y Z) (I J : Type) [Fintype I] [Fintype J] :
    LocalMap (Tensor.directSum (fun _ : I => Tensor.directSum (fun _ : J => source)))
      (Tensor.directSum (fun _ : I × J => source)) where
  x := fun x s => if s = (x.1.1, (x.1.2, x.2)) then 1 else 0
  y := fun y s => if s = (y.1.1, (y.1.2, y.2)) then 1 else 0
  z := fun z s => if s = (z.1.1, (z.1.2, z.2)) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, Tensor.directSum, Prod.ext_iff]
    split_ifs <;> aesop

def replicationProduct {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (active : Tensor F X Y Z) (finished : Tensor F U V W)
    (R : Type) [Fintype R] :
    LocalMap (Tensor.directSum (fun _ : R => Tensor.product active finished))
      (Tensor.product (Tensor.directSum (fun _ : R => active)) finished) where
  x := fun x s => if s = (x.1.1, (x.1.2, x.2)) then 1 else 0
  y := fun y s => if s = (y.1.1, (y.1.2, y.2)) then 1 else 0
  z := fun z s => if s = (z.1.1, (z.1.2, z.2)) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp [Tensor.pullback, Tensor.directSum, Tensor.product, ite_mul]

def extract (T : Tensor F X Y Z) {I : Type} [Fintype I]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent T assignment) :
    LocalMap T (Tensor.directSum (JointExtraction.branch T assignment)) where
  x := JointExtraction.assignmentMatrix assignment.x
  y := JointExtraction.assignmentMatrix assignment.y
  z := JointExtraction.assignmentMatrix assignment.z
  coefficient := JointExtraction.restrict_assignments_eq_directSum T assignment coherent

end LocalMap

structure Execution {SX SY SZ X Y Z : Type}
    [Fintype SX] [Fintype SY] [Fintype SZ]
    (source : Tensor F SX SY SZ) (target : Tensor F X Y Z) where
  Copies : Type
  [copies_finite : Fintype Copies]
  copies_positive : 0 < Fintype.card Copies
  map : LocalMap (Tensor.directSum (fun _ : Copies => source)) target

attribute [instance] Execution.copies_finite

namespace Execution

variable {SX SY SZ X Y Z X' Y' Z' : Type}
  [Fintype SX] [Fintype SY] [Fintype SZ]
  [Fintype X] [Fintype Y] [Fintype Z]
  {source : Tensor F SX SY SZ} {current : Tensor F X Y Z}

def initial (source : Tensor F SX SY SZ) : Execution source source where
  Copies := PUnit
  copies_positive := by simp
  map := {
    x := fun x s => if s = (PUnit.unit, x) then 1 else 0
    y := fun y s => if s = (PUnit.unit, y) then 1 else 0
    z := fun z s => if s = (PUnit.unit, z) then 1 else 0
    coefficient := by
      rw [← Tensor.pullback_eq_restrict]
      funext x y z
      simp [Tensor.pullback, Tensor.directSum]
  }

def restrict (E : Execution source current) (target : Tensor F X' Y' Z')
    (map : LocalMap current target) : Execution source target where
  Copies := E.Copies
  copies_positive := E.copies_positive
  map := E.map.comp map

def replicate (E : Execution source current) (R : Type) [Fintype R]
    (positive : 0 < Fintype.card R) :
    Execution source (Tensor.directSum (fun _ : R => current)) where
  Copies := R × E.Copies
  copies_positive := by simpa using Nat.mul_pos positive E.copies_positive
  map := ((LocalMap.unflatten source R E.Copies).comp (E.map.parallelCopies R)).withSource _
    (by funext x y z; simp only [Tensor.directSum])

def step (E : Execution source current) (R : Type) [Fintype R]
    (positive : 0 < Fintype.card R) (target : Tensor F X' Y' Z')
    (map : LocalMap (Tensor.directSum (fun _ : R => current)) target) :
    Execution source target :=
  (E.replicate R positive).restrict target map

def branchOperation {I J R : Type} [Fintype I] [Fintype J] [Fintype R]
    (current : Tensor F X Y Z) (next : Tensor F X' Y' Z')
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (E : Execution source (Tensor.directSum (fun _ : I => current)))
    (positive : 0 < Fintype.card R)
    (map : LocalMap (Tensor.directSum (fun _ : R => current))
      (Tensor.directSum (fun _ : J => next))) :
    Execution source (Tensor.directSum (fun _ : I × J => next)) :=
  E.step R positive _ ((LocalMap.ofExists
    (Replication.repair_branches (fun _ : I => current)
      (fun _ : I => Tensor.directSum (fun _ : J => next))
      (fun _ => map.x) (fun _ => map.y) (fun _ => map.z)
      (fun _ => map.coefficient))).comp (LocalMap.flatten next I J))

@[simp] theorem branchOperation_copies {I J R : Type}
    [Fintype I] [Fintype J] [Fintype R]
    (current : Tensor F X Y Z) (next : Tensor F X' Y' Z')
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (E : Execution source (Tensor.directSum (fun _ : I => current)))
    (positive : 0 < Fintype.card R)
    (map : LocalMap (Tensor.directSum (fun _ : R => current))
      (Tensor.directSum (fun _ : J => next))) :
    Fintype.card (branchOperation current next E positive map).Copies =
      Fintype.card R * Fintype.card E.Copies := by
  exact Fintype.card_prod R E.Copies

@[simp] theorem step_copies (E : Execution source current) (R : Type) [Fintype R]
    (positive : 0 < Fintype.card R) (target : Tensor F X' Y' Z')
    (map : LocalMap (Tensor.directSum (fun _ : R => current)) target) :
    Fintype.card (E.step R positive target map).Copies =
      Fintype.card R * Fintype.card E.Copies := by
  exact Fintype.card_prod R E.Copies

end Execution

section CWSource

variable {K N a b c L : ℕ}

abbrev cwSource (F : Type*) [Field F] (K N : ℕ) :=
  Tensor.power (FieldCW.tensor F 5) (8 * K * N)

def startCW (F : Type*) [Field F] (K N : ℕ) :
    Execution (cwSource F K N) (cwSource F K N) :=
  Execution.initial _

def Execution.toWitness
    (E : Execution (cwSource F K N) (AllFieldSource.matrixTarget F a b c L))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hL : 0 < L) : AllFieldWitness F :=
  AllFieldSource.ofRestriction E.map.x E.map.y E.map.z
    (fun x y z => congrFun (congrFun (congrFun E.map.coefficient x) y) z)
    E.copies_positive ha hb hc hL

@[simp] theorem Execution.toWitness_rankBound
    (E : Execution (cwSource F K N) (AllFieldSource.matrixTarget F a b c L))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hL : 0 < L) :
    (E.toWitness ha hb hc hL).rankBound =
      Fintype.card E.Copies * ((3 * (8 * K * N) + 1) ^ 2 * 7 ^ (8 * K * N)) := rfl

end CWSource

end MatrixMultiplication.AllFieldFiniteFamily

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialSource

open MatrixMultiplication.Foundation AllFieldFiniteFamily CommonDimensions
open scoped BigOperators Classical

abbrev Sites (K N : ℕ) := Fin K × (Fin N × Fin 8)
abbrev Words (K N : ℕ) := Fin K → Fin N → Fin 8 → Fin 7

def sitesEquiv (K N : ℕ) : Sites K N ≃ Fin (8 * K * N) :=
  Fintype.equivOfCardEq (by simp only [Sites, Fintype.card_prod, Fintype.card_fin] <;> ring)

def flatten (K N : ℕ) (w : Words K N) : AllFieldSource.Word K N :=
  fun i => let p := (sitesEquiv K N).symm i; w p.1 p.2.1 p.2.2

def groupedSource (F : Type*) [Field F] (K N : ℕ) :
    Tensor F (Words K N) (Words K N) (Words K N) :=
  fun x y z => ∏ p : Sites K N,
    FieldCW.tensor F 5 (x p.1 p.2.1 p.2.2) (y p.1 p.2.1 p.2.2) (z p.1 p.2.1 p.2.2)

theorem groupedSource_eq_lots (F : Type*) [Field F] (K N : ℕ) :
    groupedSource F K N =
      familyProduct (fun _ : Fin K => Tensor.power (Tensor.power (FieldCW.tensor F 5) 8) N) := by
  funext x y z
  simp only [groupedSource, Sites, familyProduct, Tensor.power, Fintype.prod_prod_type]

def groupingMap (F : Type*) [Field F] (K N : ℕ) :
    LocalMap (cwSource F K N) (groupedSource F K N) where
  x := fun x s => if s = flatten K N x then 1 else 0
  y := fun y s => if s = flatten K N y then 1 else 0
  z := fun z s => if s = flatten K N z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, cwSource, Tensor.power, groupedSource, flatten]
    apply Fintype.prod_equiv (sitesEquiv K N).symm
    intro i
    rfl

def initialExecution (F : Type*) [Field F] (K N : ℕ) :
    Execution (cwSource F K N) (groupedSource F K N) :=
  (startCW F K N).restrict _ (groupingMap F K N)

@[simp] theorem initialExecution_copies (F : Type*) [Field F] (K N : ℕ) :
    Fintype.card (initialExecution F K N).Copies = 1 := rfl

end MatrixMultiplication.AllFieldInitialSource

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCanonicalInitial

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open InheritedMasks CWStrands
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ)

abbrev Word := Fin 8 → Fin 7
abbrev RawWords := ∀ h, Positions counts h → Word
abbrev CanonicalWords := ∀ c : ClassKey (H := H), ClassPositions counts c → Word

def wholeEquiv (e : Target counts) : RawWords counts ≃ CanonicalWords counts where
  toFun w := fun c j => w c.1 ((positionEquiv counts e c.1).symm ⟨c.2, j⟩)
  invFun w := fun h i => w (h, (e h).val i) (positionEquiv counts e h i).2
  left_inv w := by
    funext h i
    change w h ((positionEquiv counts e h).symm (positionEquiv counts e h i)) = w h i
    simp
  right_inv w := by
    funext c j
    exact congrArg (fun p : Σ u, Fin (counts c.1 u) => w (c.1, p.1) p.2)
      ((positionEquiv counts e c.1).apply_symm_apply ⟨c.2, j⟩)

def rawSource : Tensor F (RawWords counts) (RawWords counts) (RawWords counts) :=
  classProduct (fun _ : H => strand (Fin 8))

def coarseWord (w : RawWords counts) : Position counts → Fin 17 :=
  fun i => CWCoarseIndices.coarseIndex (by simp) (w i.1 i.2)

def ideal (e : Target counts) : Tensor F (RawWords counts) (RawWords counts)
    (RawWords counts) :=
  JointIdealBranches.ideal (rawSource counts) (coarseWord counts) (coarseWord counts)
    (coarseWord counts) (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)
    (triple counts e)

def canonical : Tensor F (CanonicalWords counts) (CanonicalWords counts)
    (CanonicalWords counts) :=
  classProduct (fun c : ClassKey (H := H) => shapeTensor (Fin 8) (shapeNat c.2))

omit [DecidableEq H] in
theorem canonical_pack (e : Target counts) (x y z : RawWords counts) :
    canonical counts (wholeEquiv counts e x) (wholeEquiv counts e y)
      (wholeEquiv counts e z) =
      ∏ h, ∏ i, shapeTensor (F := F) (Fin 8) (shapeNat ((e h).val i))
        (x h i) (y h i) (z h i) := by
  unfold canonical classProduct
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h _
  rw [← Fintype.prod_sigma']
  apply Fintype.prod_equiv (positionEquiv counts e h).symm
  intro i
  simp only [wholeEquiv, Equiv.coe_fn_mk, positionEquiv_symm_shape]

omit [DecidableEq H] in
theorem ideal_eq_canonical (e : Target counts) (x y z : RawWords counts) :
    ideal (F := F) counts e x y z = canonical counts (wholeEquiv counts e x)
      (wholeEquiv counts e y) (wholeEquiv counts e z) := by
  rw [canonical_pack]
  simp only [ideal, JointIdealBranches.ideal, ExactRecovery.delete, and_true,
    rawSource, classProduct, shapeTensor, Fintype.prod_ite_zero, forall_and]
  congr 1
  simp [coarseWord, triple, shapeNat, shapeSide, CWCoarseIndices.coarseIndex,
    funext_iff, Fin.ext_iff, Sigma.forall]

def coordinateMatrix (e : Target counts) : CanonicalWords counts → RawWords counts → F :=
  fun x v => if v = (wholeEquiv counts e).symm x then 1 else 0

theorem ideal_restrict (e : Target counts) :
    Tensor.restrict (coordinateMatrix (F := F) counts e) (coordinateMatrix counts e)
      (coordinateMatrix counts e) (ideal counts e) = canonical counts := by
  funext x y z
  simp only [Tensor.restrict, coordinateMatrix]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [ideal_eq_canonical]
  simp

omit [DecidableEq H] in
theorem coarse_support (x y z : RawWords counts)
    (hT : rawSource (F := F) counts x y z ≠ 0) (i : Position counts) :
    (coarseWord counts x i).val + (coarseWord counts y i).val +
      (coarseWord counts z i).val = 16 := by
  have hh : strand (F := F) (Fin 8) (x i.1 i.2) (y i.1 i.2) (z i.1 i.2) ≠ 0 := by
    intro hz
    apply hT
    unfold rawSource classProduct
    apply Finset.prod_eq_zero (Finset.mem_univ i.1)
    exact Finset.prod_eq_zero (Finset.mem_univ i.2) hz
  simpa [coarseWord] using
    CWCoarseIndices.strand_coarse_support (F := F) (by simp)
      (x i.1 i.2) (y i.1 i.2) (z i.1 i.2) hh

def sideMask (s : Fin 3) (w : RawWords counts) : Prop :=
  ∀ h a, wordPopulation (fun i => coarseWord counts w ⟨h, i⟩) a =
    wordPopulation (sideWord counts s (triple counts (canonicalTarget counts)) h) a

def maskedSource : Tensor F (RawWords counts) (RawWords counts) (RawWords counts) :=
  ExactRecovery.delete (rawSource counts) (sideMask counts 0) (sideMask counts 1)
    (sideMask counts 2)

omit [Fintype H] [DecidableEq H] in
theorem sideMask_of_target (s : Fin 3) (e : Target counts) (w : RawWords counts)
    (he : coarseWord counts w =
      fun i => sideWord counts s (triple counts e) i.1 i.2) :
    sideMask counts s w := by
  intro h a
  rw [he]
  exact marginal_population_eq counts e (canonicalTarget counts) h s a

theorem maskedSource_support (x y z : RawWords counts)
    (hT : maskedSource (F := F) counts x y z ≠ 0) :
    (coarseWord counts x, coarseWord counts y, coarseWord counts z) ∈
      ambientSet counts (fun _ => 16) := by
  have hm : sideMask counts 0 x ∧ sideMask counts 1 y ∧ sideMask counts 2 z := by
    by_contra hn
    simp [maskedSource, ExactRecovery.delete, hn] at hT
  have hr : rawSource (F := F) counts x y z ≠ 0 := by
    simpa [maskedSource, ExactRecovery.delete, hm] using hT
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i
    exact coarse_support counts x y z hr i
  · intro h s a
    fin_cases s
    · exact hm.1 h a
    · exact hm.2.1 h a
    · exact hm.2.2 h a

omit [DecidableEq H] in
theorem ideal_support_masks (e : Target counts) (x y z : RawWords counts)
    (hT : ideal (F := F) counts e x y z ≠ 0) :
    sideMask counts 0 x ∧ sideMask counts 1 y ∧ sideMask counts 2 z := by
  have hc : coarseWord counts x = (triple counts e).1 ∧
      coarseWord counts y = (triple counts e).2.1 ∧
      coarseWord counts z = (triple counts e).2.2 := by
    by_contra hn
    simp [ideal, JointIdealBranches.ideal, ExactRecovery.delete, hn] at hT
  constructor
  · apply sideMask_of_target counts 0 e x
    simpa [sideWord, shapeSide] using hc.1
  constructor
  · apply sideMask_of_target counts 1 e y
    simpa [sideWord, shapeSide] using hc.2.1
  · apply sideMask_of_target counts 2 e z
    simpa [sideWord, shapeSide] using hc.2.2

end MatrixMultiplication.JointCanonicalInitial

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialStep

open MatrixMultiplication.Foundation AllFieldFiniteFamily AllFieldInitialSource
open JointPopulation
open scoped BigOperators Classical

variable {F : Type*} [Field F] {K N : ℕ}
  (counts : Fin K → Shape → ℕ) (total : ∀ h, ∑ u, counts h u = N)

def toLots (w : JointCanonicalInitial.RawWords counts) : Words K N :=
  fun h i => w h ((finCongr (total h)).symm i)

def positionMap :
    LocalMap (groupedSource F K N) (JointCanonicalInitial.rawSource counts) where
  x := fun x s => if s = toLots counts total x then 1 else 0
  y := fun y s => if s = toLots counts total y then 1 else 0
  z := fun z s => if s = toLots counts total z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict, groupedSource_eq_lots]
    funext x y z
    change (∏ h : Fin K, ∏ i : Fin N, CWStrands.strand (F := F) (Fin 8)
      (x h ((finCongr (total h)).symm i))
      (y h ((finCongr (total h)).symm i))
      (z h ((finCongr (total h)).symm i))) =
      ∏ h : Fin K, ∏ i : Positions counts h, CWStrands.strand (F := F) (Fin 8)
        (x h i) (y h i) (z h i)
    apply Finset.prod_congr rfl
    intro h _
    apply Fintype.prod_equiv (finCongr (total h)).symm
    intro i
    rfl

def initialExecution :
    Execution (cwSource F K N) (JointCanonicalInitial.rawSource counts) :=
  (AllFieldInitialSource.initialExecution F K N).restrict _ (positionMap counts total)

@[simp] theorem initialExecution_copies :
    Fintype.card (initialExecution (F := F) counts total).Copies = 1 := rfl

def maskedInitialExecution :
    Execution (cwSource F K N) (JointCanonicalInitial.maskedSource counts) :=
  (initialExecution counts total).restrict _
    (LocalMap.delete (JointCanonicalInitial.rawSource counts)
      (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
      (JointCanonicalInitial.sideMask counts 2))

abbrev CoarseWord := Position counts → Fin 17

def ordinaryAssignments (hx hy hz : CoarseWord counts → Prop) :
    JointExtraction.Assignment (JointCanonicalInitial.RawWords counts)
      (JointCanonicalInitial.RawWords counts) (JointCanonicalInitial.RawWords counts)
      (JointCoarseHashing.Triple (Position counts)) :=
  JointCoarseAssignment.assignments (ambientSet counts (fun _ => 16)) (targetSet counts)
    hx hy hz (JointCanonicalInitial.coarseWord counts) (JointCanonicalInitial.coarseWord counts)
    (JointCanonicalInitial.coarseWord counts) (fun _ _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)

theorem ordinaryAssignments_coherent (hx hy hz : CoarseWord counts → Prop) :
    JointExtraction.Coherent (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) := by
  apply JointCoarseAssignment.assignments_coherent
  · exact JointCanonicalInitial.maskedSource_support counts
  · intro _ _ _ _ _ _ _
    trivial
  · intro _ _ _ _ _ _ _ _
    trivial

def initialCanonicalMap (e : Target counts) :
    LocalMap (JointCanonicalInitial.ideal (F := F) counts e)
      (JointCanonicalInitial.canonical counts) where
  x := JointCanonicalInitial.coordinateMatrix counts e
  y := JointCanonicalInitial.coordinateMatrix counts e
  z := JointCanonicalInitial.coordinateMatrix counts e
  coefficient := JointCanonicalInitial.ideal_restrict counts e

def canonicalize {I : Type} [Fintype I] (target : I → Target counts)
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i)))) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical counts)) :=
  E.restrict _ (LocalMap.directSum _ _ (fun i => initialCanonicalMap counts (target i)))

@[simp] theorem canonicalize_copies {I : Type} [Fintype I] (target : I → Target counts)
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i)))) :
    Fintype.card (canonicalize counts target E).Copies = Fintype.card E.Copies := rfl

end MatrixMultiplication.AllFieldInitialStep

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialExact

open MatrixMultiplication.Foundation AllFieldFiniteFamily AllFieldInitialStep
open JointPopulation JointCoarseAssignment JointExtraction JointAssignmentLoss
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

def assignedDeletion {F X Y Z A B C : Type*} [CommSemiring F]
    (T : Tensor F X Y Z) (a : Assignment X Y Z (Triple A B C)) (e : Triple A B C)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop) : Tensor F X Y Z :=
  ExactRecovery.delete T (fun x => a.x x = some e ∧ px x)
    (fun y => a.y y = some e ∧ py y) (fun z => a.z z = some e ∧ pz z)

theorem assignedDeletion_eq_self_of_support {F X Y Z A B C : Type*}
    [CommSemiring F] (T : Tensor F X Y Z)
    (a : Assignment X Y Z (Triple A B C)) (e : Triple A B C)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    (support : ∀ x y z, T x y z ≠ 0 →
      (a.x x = some e ∧ px x) ∧ (a.y y = some e ∧ py y) ∧ (a.z z = some e ∧ pz z)) :
    assignedDeletion T a e px py pz = T := by
  funext x y z
  unfold assignedDeletion ExactRecovery.delete
  by_cases ht : T x y z = 0
  · simp only [ht, ite_self]
  · exact ite_eq_left (support x y z ht)

variable {K N : ℕ}
  (counts : Fin K → Shape → ℕ)
  (hx hy hz : CoarseWord counts → Prop)

def Isolated (e : Target counts) : Prop :=
  survives hx hy hz (triple counts e) ∧
    ∀ f ∈ ambientSet counts (fun _ => 16), survives hx hy hz f →
      JointCoarseHashing.SharesSide (triple counts e) f → f = triple counts e

section Coefficients

variable {F : Type*} [CommRing F]

theorem assignments_on_ideal (e : Target counts)
    (ha : triple counts e ∈ ambientSet counts (fun _ => 16))
    (isolated : Isolated counts hx hy hz e)
    (x y z : JointCanonicalInitial.RawWords counts)
    (nonzero : JointCanonicalInitial.ideal (F := F) counts e x y z ≠ 0) :
    (ordinaryAssignments counts hx hy hz).x x = some (triple counts e) ∧
      (ordinaryAssignments counts hx hy hz).y y = some (triple counts e) ∧
      (ordinaryAssignments counts hx hy hz).z z = some (triple counts e) := by
  have hc : JointCanonicalInitial.coarseWord counts x = (triple counts e).1 ∧
      JointCanonicalInitial.coarseWord counts y = (triple counts e).2.1 ∧
      JointCanonicalInitial.coarseWord counts z = (triple counts e).2.2 := by
    by_contra hn
    simp [JointCanonicalInitial.ideal, JointIdealBranches.ideal, ExactRecovery.delete, hn]
      at nonzero
  have ht : triple counts e ∈ targetSet counts :=
    Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  have he : triple counts e ∈ eligible (ambientSet counts (fun _ => 16))
      (targetSet counts) hx hy hz := by
    apply (mem_eligible_iff _ _ _ _ _ _).2
    exact ⟨ha, ht, isolated.1, fun f hf hs hfx => isolated.2 f hf hs (Or.inl hfx)⟩
  constructor
  · apply assignUseful_of_unique _ _ _ _ _ he hc.1 trivial
    intro f hf hfx
    have hm := (mem_eligible_iff _ _ _ _ _ _).1 hf
    exact isolated.2 f hm.1 hm.2.2.1 (Or.inl (hfx.symm.trans hc.1))
  constructor
  · apply assignUseful_of_unique _ _ _ _ _ he ⟨hc.2.1, trivial⟩ trivial
    intro f hf hfy
    have hm := (mem_eligible_iff _ _ _ _ _ _).1 hf
    exact isolated.2 f hm.1 hm.2.2.1 (Or.inr (Or.inl (hfy.1.symm.trans hc.2.1)))
  · apply assignUseful_of_unique _ _ _ _ _ he ⟨hc.2.2, trivial⟩ trivial
    intro f hf hfz
    have hm := (mem_eligible_iff _ _ _ _ _ _).1 hf
    exact isolated.2 f hm.1 hm.2.2.1 (Or.inr (Or.inr (hfz.1.symm.trans hc.2.2)))

theorem branch_eq_masked_ideal (e : Target counts) :
    branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts e) =
      assignedDeletion (JointCanonicalInitial.ideal counts e)
        (ordinaryAssignments counts hx hy hz) (triple counts e)
        (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
        (JointCanonicalInitial.sideMask counts 2) :=
  JointIdealBranches.branch_masked_eq_delete_ideal
    (JointCanonicalInitial.rawSource (F := F) counts)
    (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
    (JointCanonicalInitial.sideMask counts 2) (ambientSet counts (fun _ => 16)) (targetSet counts)
    hx hy hz (JointCanonicalInitial.coarseWord counts) (JointCanonicalInitial.coarseWord counts)
    (JointCanonicalInitial.coarseWord counts) (fun _ _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) (triple counts e)

theorem branch_eq_ideal (e : Target counts)
    (ha : triple counts e ∈ ambientSet counts (fun _ => 16))
    (isolated : Isolated counts hx hy hz e) :
    branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts e) =
      JointCanonicalInitial.ideal counts e := by
  have hdelete : assignedDeletion (JointCanonicalInitial.ideal (F := F) counts e)
      (ordinaryAssignments counts hx hy hz) (triple counts e)
      (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
      (JointCanonicalInitial.sideMask counts 2) =
      JointCanonicalInitial.ideal counts e := by
    apply assignedDeletion_eq_self_of_support
    intro x y z hh
    have hm := JointCanonicalInitial.ideal_support_masks counts e x y z hh
    have ha := assignments_on_ideal counts hx hy hz e ha isolated x y z hh
    exact ⟨⟨ha.1, hm.1⟩, ⟨ha.2.1, hm.2.1⟩, ⟨ha.2.2, hm.2.2⟩⟩
  exact (branch_eq_masked_ideal counts hx hy hz e).trans hdelete

end Coefficients

section Execution

variable {F : Type*} [Field F]

def selectedExecution (total : ∀ h, ∑ u, counts h u = N)
    {I : Type} [Fintype I] (target : I → Target counts)
    (injective : Function.Injective target)
    (ambient : ∀ i, triple counts (target i) ∈ ambientSet counts (fun _ => 16))
    (isolated : ∀ i, Isolated counts hx hy hz (target i)) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical counts)) := by
  let input := maskedInitialExecution (F := F) counts total
  let extracted := input.restrict _
    (LocalMap.extract (JointCanonicalInitial.maskedSource counts)
      (ordinaryAssignments counts hx hy hz) (ordinaryAssignments_coherent counts hx hy hz))
  let selected := extracted.restrict _
    (LocalMap.selectBranches
      (branch (JointCanonicalInitial.maskedSource counts) (ordinaryAssignments counts hx hy hz))
      (fun i => triple counts (target i)) ((triple_injective counts).comp injective))
  have heq : Tensor.directSum (fun i => branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts (target i))) =
      Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i)) := by
    apply congrArg Tensor.directSum
    funext i
    exact branch_eq_ideal counts hx hy hz (target i) (ambient i) (isolated i)
  let idMap := LocalMap.identity (Tensor.directSum (fun i =>
    branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts (target i))))
  let sameCoordinates : LocalMap
      (Tensor.directSum (fun i => branch (JointCanonicalInitial.maskedSource (F := F) counts)
        (ordinaryAssignments counts hx hy hz) (triple counts (target i))))
      (Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i))) :=
    { x := idMap.x
      y := idMap.y
      z := idMap.z
      coefficient := idMap.coefficient.trans heq }
  exact AllFieldInitialStep.canonicalize counts target (selected.restrict _ sameCoordinates)

@[simp] theorem selectedExecution_copies (total : ∀ h, ∑ u, counts h u = N)
    {I : Type} [Fintype I] (target : I → Target counts)
    (injective : Function.Injective target)
    (ambient : ∀ i, triple counts (target i) ∈ ambientSet counts (fun _ => 16))
    (isolated : ∀ i, Isolated counts hx hy hz (target i)) :
    Fintype.card (selectedExecution (F := F) counts hx hy hz total target
      injective ambient isolated).Copies = 1 := rfl

end Execution

end MatrixMultiplication.AllFieldInitialExact

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialState

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters AllFieldFiniteFamily
open scoped BigOperators Classical

variable {K : ℕ} (allocation : Allocation) (dilation : ℕ)

abbrev CanonicalKey := JointCanonicalization.ClassKey (H := Fin K)

abbrev PlacementPositions (p : InitialPlacement K) :=
  Fin (population allocation dilation (.initial p.1, p.2))

def classPosition (c : CanonicalKey (K := K))
    (i : Fin (initialJointCounts allocation dilation c.1 c.2)) :
    Σ p : InitialPlacement K, PlacementPositions allocation dilation p :=
  let q := initialClassPositionEquiv allocation dilation c.1 c.2 i
  ⟨((c.1, q.1.val.1), q.1.val.2), q.2⟩

theorem classPosition_shape (c : CanonicalKey (K := K))
    (i : Fin (initialJointCounts allocation dilation c.1 c.2)) :
    JointCanonicalCW.shapeNat c.2 =
      physicalShape (classPosition allocation dilation c i).1.2
        (initialShape (classPosition allocation dilation c i).1.1) := by
  have h := congrArg decodeShape (initialClassPosition_shape allocation dilation c.1 c.2 i)
  change decodeShape c.2 = _
  simpa only [rootShape, decode_encodePhysicalShape, classPosition] using h.symm

theorem prod_classPosition {F : Type*} [CommMonoid F]
    (f : ∀ p : InitialPlacement K, PlacementPositions allocation dilation p → F) :
    (∏ c : CanonicalKey (K := K),
      ∏ i : Fin (initialJointCounts allocation dilation c.1 c.2),
        f (classPosition allocation dilation c i).1
          (classPosition allocation dilation c i).2) =
      ∏ p : InitialPlacement K, ∏ i : PlacementPositions allocation dilation p, f p i := by
  conv_lhs => rw [Fintype.prod_prod_type]
  conv_rhs =>
    rw [Fintype.prod_prod_type]
    rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  calc
    (∏ u : JointPopulation.Shape, ∏ i : Fin (initialJointCounts allocation dilation j u),
        f (classPosition allocation dilation (j, u) i).1
          (classPosition allocation dilation (j, u) i).2) =
        ∏ u : JointPopulation.Shape, ∏ p : InitialShapeFiber j u,
          ∏ i : Fin (population allocation dilation (.initial (j, p.val.1), p.val.2)),
            f ((j, p.val.1), p.val.2) i := by
      apply Finset.prod_congr rfl
      intro u _
      rw [← Fintype.prod_sigma']
      apply Fintype.prod_equiv (initialClassPositionEquiv allocation dilation j u)
      intro i
      rfl
    _ = ∏ p : Fin sortedInitial.length × Placement,
          ∏ i : Fin (population allocation dilation (.initial (j, p.1), p.2)),
            f ((j, p.1), p.2) i :=
      Fintype.prod_fiberwise (fun p : Fin sortedInitial.length × Placement =>
        rootShape (j, p.1) p.2)
        (fun p => ∏ i : Fin (population allocation dilation (.initial (j, p.1), p.2)),
          f ((j, p.1), p.2) i)
    _ = _ := by rw [Fintype.prod_prod_type]

abbrev StateWords := ∀ h : State K 0, HistoryWord allocation dilation h.val

def toCanonical (w : StateWords (K := K) allocation dilation) :
    JointCanonicalInitial.CanonicalWords (initialJointCounts (K := K) allocation dilation) :=
  fun c i =>
    let q := classPosition allocation dilation c i
    w ((initialStateEquiv K).symm q.1) q.2

theorem coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : StateWords (K := K) allocation dilation) :
    JointCanonicalInitial.canonical (F := F) (initialJointCounts allocation dilation)
      (toCanonical allocation dilation x) (toCanonical allocation dilation y)
      (toCanonical allocation dilation z) =
      stateTensor F allocation dilation ε 0 x y z := by
  let f : ∀ p : InitialPlacement K, PlacementPositions allocation dilation p → F :=
    fun p i => CWStrands.shapeTensor (Fin 8) (physicalShape p.2 (initialShape p.1))
      (x ((initialStateEquiv K).symm p) i)
      (y ((initialStateEquiv K).symm p) i)
      (z ((initialStateEquiv K).symm p) i)
  have hcanonical :
      JointCanonicalInitial.canonical (F := F) (initialJointCounts allocation dilation)
        (toCanonical allocation dilation x) (toCanonical allocation dilation y)
        (toCanonical allocation dilation z) =
      ∏ p : InitialPlacement K, ∏ i : PlacementPositions allocation dilation p, f p i := by
    rw [← prod_classPosition allocation dilation f]
    unfold JointCanonicalInitial.canonical InheritedMasks.classProduct
    apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro i _
    dsimp only [toCanonical, f]
    rw [classPosition_shape allocation dilation c i]
  have hstate : stateTensor F allocation dilation ε 0 x y z =
      ∏ p : InitialPlacement K, ∏ i : PlacementPositions allocation dilation p, f p i := by
    change (∏ h : State K 0, historyTensor F allocation dilation ε h.val (x h) (y h) (z h)) = _
    rw [← (initialStateEquiv K).symm.prod_comp
      (fun h : State K 0 => historyTensor F allocation dilation ε h.val (x h) (y h) (z h))]
    apply Finset.prod_congr rfl
    intro p _
    change historyTensor F allocation dilation ε (.initial p.1, p.2)
      (x ((initialStateEquiv K).symm p)) (y ((initialStateEquiv K).symm p))
      (z ((initialStateEquiv K).symm p)) = _
    rw [historyTensor_initial]
    rfl
  exact hcanonical.trans hstate.symm

def map (F : Type*) [Field F] (ε : ℝ) :
    LocalMap
      (JointCanonicalInitial.canonical (F := F) (initialJointCounts (K := K) allocation dilation))
      (stateTensor F (K := K) allocation dilation ε 0) where
  x := fun x s => if s = toCanonical allocation dilation x then 1 else 0
  y := fun y s => if s = toCanonical allocation dilation y then 1 else 0
  z := fun z s => if s = toCanonical allocation dilation z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    exact coefficient allocation dilation F ε x y z

def execution (F : Type*) [Field F] (ε : ℝ) {I : Type} [Fintype I] {N : ℕ}
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical
        (initialJointCounts (K := K) allocation dilation)))) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => stateTensor F (K := K) allocation dilation ε 0)) :=
  E.restrict _ ((map (K := K) allocation dilation F ε).parallelCopies I)

@[simp] theorem execution_copies (F : Type*) [Field F] (ε : ℝ)
    {I : Type} [Fintype I] {N : ℕ}
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical
        (initialJointCounts (K := K) allocation dilation)))) :
    Fintype.card (execution allocation dilation F ε E).Copies = Fintype.card E.Copies := rfl

end MatrixMultiplication.AllFieldInitialState

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistorySupport

open AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev ActiveRawPairs {K tick : ℕ} (allocation : Allocation) (m : ℕ) :=
  JointCanonicalization.RawPairs (activeCounts (K := K) (tick := tick) allocation m)
    (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength)

end MatrixMultiplication.AllFieldHistorySupport

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]
  {P X Y : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, DecidableEq (X c)]
  [∀ c, Fintype (Y c)] [∀ c, DecidableEq (Y c)]

abbrev PairOrbit (P X Y : C → Type*) :=
  MulAction.orbitRel.Quotient (HalfClassPermutations P) (CompleteWordPair P X Y)

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitCount

open AllFieldHistory AllFieldHistorySupport PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev GroupClasses (K tick : ℕ) (sigma : Placement) :=
  ActiveOrder K tick sigma × JointPopulation.Shape

abbrev GroupPositions {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    {sigma : Placement} (c : GroupClasses K tick sigma) :=
  Fin (activeCounts allocation m c.1.val c.2)

abbrev GroupLetters {K tick : ℕ} {sigma : Placement} (c : GroupClasses K tick sigma) :=
  Fin (activeHalfLength c.1.val) → Fin 7

abbrev GroupOrbit {K tick : ℕ} (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  PairOrbit (GroupPositions (K := K) (tick := tick) (sigma := sigma) allocation m)
    (GroupLetters (K := K) (tick := tick) (sigma := sigma))
    (GroupLetters (K := K) (tick := tick) (sigma := sigma))

end MatrixMultiplication.AllFieldGroupOrbitCount

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryRecoveryBudget
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section

namespace MatrixMultiplication.AllFieldHistoryMasks

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open JointCanonicalization InheritedMasks PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev SymbolChoice (K tick : ℕ) := ∀ h : Active K tick, Statistic h

def pairWidth (ε : ℝ) (h : Active K tick) : ℝ := ε / 16 ^ h.val.1.stage.val

def childWidth (ε : ℝ) (h : Active K tick) : ℝ := pairWidth ε h / 8

end MatrixMultiplication.AllFieldHistoryMasks






namespace MatrixMultiplication.AllFieldHistoryIncomingMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters
open AllFieldHistoryChildLaws AllFieldHistorySupport AllFieldHistoryMasks
open InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def defaultStatistic : (w : Work K) → w.Statistic
  | .stageA _ => (0, 0)
  | .stageB _ => (0 : Fin 6)
  | .stageC _ => PUnit.unit

def choiceAt (h : Active K tick) (a : Statistic h) : SymbolChoice K tick :=
  Function.update (fun g => defaultStatistic g.val.1) h a

@[simp] theorem choiceAt_self (h : Active K tick) (a : Statistic h) :
    choiceAt h a h = a := by simp [choiceAt]

@[simp] theorem fourStatistic_append (l r : Fin 2 → Fin 7) :
    CWCompleteStatistics.fourStatistic (Fin.append l r) =
      (CWCompleteStatistics.twoStatistic l, CWCompleteStatistics.twoStatistic r) := rfl

attribute [local irreducible] activeCounts population

end MatrixMultiplication.AllFieldHistoryIncomingMasks

end
end




section
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.EquivOrbitTransport

variable {G X Y : Type*} [Group G] [MulAction G Y]

@[instance_reducible] def action (e : X ≃ Y) : MulAction G X where
  smul g x := e.symm (g • e x)
  one_smul x := by
    change e.symm ((1 : G) • e x) = x
    simp
  mul_smul g h x := by
    change e.symm ((g * h) • e x) = e.symm (g • e (e.symm (h • e x)))
    simp [mul_smul]

@[simp] theorem equiv_smul (e : X ≃ Y) (g : G) (x : X) :
    letI : MulAction G X := action e
    e (g • x) = g • e x := by
  exact e.apply_symm_apply _

end MatrixMultiplication.EquivOrbitTransport

end




section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRecovery

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistoryChildLaws
open AllFieldHistorySupport JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem halfLength_le_eight (h : Active K tick) : activeHalfLength h ≤ 8 := by
  rcases h with ⟨⟨w, phi⟩, hh⟩
  cases w <;> norm_num [activeHalfLength, Work.halfLength]

abbrev Raw (allocation : Allocation) (m : ℕ) :=
  ActiveRawPairs (K := K) (tick := tick) allocation m

abbrev Targets (allocation : Allocation) (m : ℕ) :=
  Target (activeCounts (K := K) (tick := tick) allocation m)

abbrev Symmetries (allocation : Allocation) (m : ℕ) :=
  HalfClassPermutations (ClassPositions
    (activeCounts (K := K) (tick := tick) allocation m))

def coordinates (allocation : Allocation) (m : ℕ)
    (e : Targets (K := K) (tick := tick) allocation m) :=
  pairEquiv (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) e

@[instance_reducible] def rawAction (allocation : Allocation) (m : ℕ)
    (e : Targets (K := K) (tick := tick) allocation m) :
    MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  EquivOrbitTransport.action (coordinates allocation m e)

end MatrixMultiplication.AllFieldHistoryRecovery






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryGroupCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRegrouping

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)

abbrev StateWords (tick : ℕ) := ∀ h : State K tick, HistoryWord allocation m h.val
abbrev DueWords := ∀ h : DueState K tick, HistoryWord allocation m h.val.val
abbrev CarriedWords := ∀ h : Carried K tick, HistoryWord allocation m h.val.val
abbrev ActiveWords := ∀ h : Active K tick,
  HistoryWord allocation m (activeSourceEquiv h).val.val
abbrev ProducedWords := ∀ h : Produced K tick, HistoryWord allocation m h.val

instance dueWordsFintype : Fintype (DueWords (K := K) (tick := tick) allocation m) :=
  inferInstanceAs (Fintype (∀ h : DueState K tick, HistoryWord allocation m h.val.val))

instance carriedWordsFintype : Fintype (CarriedWords (K := K) (tick := tick) allocation m) :=
  inferInstanceAs (Fintype (∀ h : Carried K tick, HistoryWord allocation m h.val.val))

instance activeWordsFintype : Fintype (ActiveWords (K := K) (tick := tick) allocation m) :=
  inferInstanceAs (Fintype (∀ h : Active K tick,
    HistoryWord allocation m (activeSourceEquiv h).val.val))

instance producedWordsFintype : Fintype (ProducedWords (K := K) (tick := tick) allocation m) :=
  inferInstanceAs (Fintype (∀ h : Produced K tick, HistoryWord allocation m h.val))

def carriedTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (CarriedWords (K := K) (tick := tick) allocation m)
      (CarriedWords (K := K) (tick := tick) allocation m) (CarriedWords (K := K) (tick := tick) allocation m) :=
  CommonDimensions.familyProduct (fun h : Carried K tick =>
    historyTensor F allocation m ε h.val.val)

def activeTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (ActiveWords (K := K) (tick := tick) allocation m)
      (ActiveWords (K := K) (tick := tick) allocation m) (ActiveWords (K := K) (tick := tick) allocation m) :=
  CommonDimensions.familyProduct (fun h : Active K tick =>
    historyTensor F allocation m ε (activeSourceEquiv h).val.val)

def producedTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (ProducedWords (K := K) (tick := tick) allocation m)
      (ProducedWords (K := K) (tick := tick) allocation m) (ProducedWords (K := K) (tick := tick) allocation m) :=
  CommonDimensions.familyProduct (fun h : Produced K tick =>
    historyTensor F allocation m ε h.val)

def toState (x : DueWords (K := K) (tick := tick) allocation m ×
    CarriedWords (K := K) (tick := tick) allocation m) : StateWords (K := K) allocation m tick :=
  fun h => if hd : due tick h.val.1 then x.1 ⟨h, hd⟩ else x.2 ⟨h, hd⟩

@[simp] theorem toState_due
    (x : DueWords (K := K) (tick := tick) allocation m × CarriedWords (K := K) (tick := tick) allocation m)
    (h : DueState K tick) : toState (K := K) (tick := tick) allocation m x h.val = x.1 h := by
  simp only [toState, dite_eq_left h.property]

@[simp] theorem toState_carried
    (x : DueWords (K := K) (tick := tick) allocation m × CarriedWords (K := K) (tick := tick) allocation m)
    (h : Carried K tick) : toState (K := K) (tick := tick) allocation m x h.val = x.2 h := by
  simp only [toState, dite_eq_right h.property]

def dueTensorAt (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (DueWords (K := K) (tick := tick) allocation m)
      (DueWords (K := K) (tick := tick) allocation m) (DueWords (K := K) (tick := tick) allocation m) :=
  CommonDimensions.familyProduct (fun h : DueState K tick =>
    historyTensor F allocation m ε h.val.val)

theorem split_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : DueWords (K := K) (tick := tick) allocation m × CarriedWords (K := K) (tick := tick) allocation m) :
    stateTensor F (K := K) allocation m ε tick (toState (K := K) (tick := tick) allocation m x)
      (toState (K := K) (tick := tick) allocation m y) (toState (K := K) (tick := tick) allocation m z) =
    Tensor.product (dueTensorAt (K := K) (tick := tick) allocation m F ε) (carriedTensor (K := K) (tick := tick) allocation m F ε) x y z := by
  change (∏ h : State K tick, historyTensor F allocation m ε h.val
    (toState (K := K) (tick := tick) allocation m x h) (toState (K := K) (tick := tick) allocation m y h) (toState (K := K) (tick := tick) allocation m z h)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun h : State K tick => due tick h.val.1)]
  simp only [toState_due, toState_carried]
  rfl

def splitMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (stateTensor F (K := K) allocation m ε tick)
      (Tensor.product (dueTensorAt (K := K) (tick := tick) allocation m F ε)
        (carriedTensor (K := K) (tick := tick) allocation m F ε)) where
  x := fun x s => if s = toState (K := K) (tick := tick) allocation m x then 1 else 0
  y := fun y s => if s = toState (K := K) (tick := tick) allocation m y then 1 else 0
  z := fun z s => if s = toState (K := K) (tick := tick) allocation m z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    exact split_coefficient allocation m F ε x y z

def toDue (x : ActiveWords (K := K) (tick := tick) allocation m) :
    DueWords (K := K) (tick := tick) allocation m :=
  Equiv.piCongrLeft (fun h : DueState K tick => HistoryWord allocation m h.val.val)
    activeSourceEquiv x

theorem active_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : ActiveWords (K := K) (tick := tick) allocation m) :
    dueTensorAt (K := K) (tick := tick) allocation m F ε (toDue (K := K) (tick := tick) allocation m x) (toDue (K := K) (tick := tick) allocation m y)
      (toDue (K := K) (tick := tick) allocation m z) = activeTensor (K := K) (tick := tick) allocation m F ε x y z := by
  change (∏ h : DueState K tick, historyTensor F allocation m ε h.val.val
    (toDue (K := K) (tick := tick) allocation m x h) (toDue (K := K) (tick := tick) allocation m y h) (toDue (K := K) (tick := tick) allocation m z h)) = _
  rw [← activeSourceEquiv.prod_comp]
  unfold toDue
  simp only [Equiv.piCongrLeft_apply_apply]
  rfl

def activeMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (dueTensorAt (K := K) (tick := tick) allocation m F ε)
      (activeTensor (K := K) (tick := tick) allocation m F ε) where
  x := fun x s => if s = toDue (K := K) (tick := tick) allocation m x then 1 else 0
  y := fun y s => if s = toDue (K := K) (tick := tick) allocation m y then 1 else 0
  z := fun z s => if s = toDue (K := K) (tick := tick) allocation m z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    exact active_coefficient allocation m F ε x y z

def activeCarriedMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (stateTensor F (K := K) allocation m ε tick)
      (Tensor.product (activeTensor (K := K) (tick := tick) allocation m F ε)
        (carriedTensor (K := K) (tick := tick) allocation m F ε)) :=
  (splitMap (K := K) (tick := tick) allocation m F ε).comp
    ((activeMap (K := K) (tick := tick) allocation m F ε).product
      (LocalMap.identity (carriedTensor (K := K) (tick := tick) allocation m F ε)))

def fromNext (x : StateWords (K := K) allocation m (tick + 1)) :
    ProducedWords (K := K) (tick := tick) allocation m × CarriedWords (K := K) (tick := tick) allocation m :=
  (fun h => x (stateTransition.symm (.inr h)),
    fun h => x (stateTransition.symm (.inl h)))

theorem next_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : StateWords (K := K) allocation m (tick + 1)) :
    Tensor.product (producedTensor (K := K) (tick := tick) allocation m F ε)
      (carriedTensor (K := K) (tick := tick) allocation m F ε) (fromNext (K := K) (tick := tick) allocation m x)
      (fromNext (K := K) (tick := tick) allocation m y) (fromNext (K := K) (tick := tick) allocation m z) =
    stateTensor F (K := K) allocation m ε (tick + 1) x y z := by
  change _ = ∏ h : State K (tick + 1), historyTensor F allocation m ε h.val
    (x h) (y h) (z h)
  rw [← stateTransition.symm.prod_comp]
  rw [Fintype.prod_sum_type]
  exact mul_comm _ _

def nextMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (Tensor.product (producedTensor (K := K) (tick := tick) allocation m F ε)
      (carriedTensor (K := K) (tick := tick) allocation m F ε))
      (stateTensor F (K := K) allocation m ε (tick + 1)) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (fromNext (K := K) (tick := tick) allocation m)
    (fromNext (K := K) (tick := tick) allocation m)
    (fromNext (K := K) (tick := tick) allocation m) _).symm.trans ?_⟩
  funext x y z
  exact next_coefficient allocation m F ε x y z

end MatrixMultiplication.AllFieldHistoryRegrouping

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryTickCarry

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldHistoryRegrouping
open scoped Classical
attribute [local instance] Classical.propDecidable Classical.decEq

section Distribution

variable {F : Type*} [Field F]

def distributeProduct
    {X Y Z U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (active : Tensor F X Y Z) (carried : Tensor F U V W)
    (J : Type) [Fintype J] :
    LocalMap (Tensor.product (Tensor.directSum (fun _ : J => active)) carried)
      (Tensor.directSum (fun _ : J => Tensor.product active carried)) where
  x := fun x s => if s = ((x.1, x.2.1), x.2.2) then 1 else 0
  y := fun y s => if s = ((y.1, y.2.1), y.2.2) then 1 else 0
  z := fun z s => if s = ((z.1, z.2.1), z.2.2) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp [Tensor.pullback, Tensor.directSum, Tensor.product, ite_mul]

end Distribution

variable {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (F : Type*) [Field F] (ε : ℝ) {J : Type} [Fintype J]

def liftExecution
    (E : Execution
      (activeTensor (K := K) (tick := tick) allocation m F ε)
      (Tensor.directSum (fun _ : J =>
        producedTensor (K := K) (tick := tick) allocation m F ε))) :
    Execution (stateTensor F (K := K) allocation m ε tick)
      (Tensor.directSum (fun _ : J =>
        stateTensor F (K := K) allocation m ε (tick + 1))) where
  Copies := E.Copies
  copies_positive := E.copies_positive
  map :=
    ((activeCarriedMap (K := K) (tick := tick) allocation m F ε).parallelCopies E.Copies).comp
      ((LocalMap.replicationProduct
        (activeTensor (K := K) (tick := tick) allocation m F ε)
        (carriedTensor (K := K) (tick := tick) allocation m F ε) E.Copies).comp
      ((E.map.product
        (LocalMap.identity (carriedTensor (K := K) (tick := tick) allocation m F ε))).comp
      ((distributeProduct
        (producedTensor (K := K) (tick := tick) allocation m F ε)
        (carriedTensor (K := K) (tick := tick) allocation m F ε) J).comp
        ((nextMap (K := K) (tick := tick) allocation m F ε).parallelCopies J))))

@[simp] theorem liftExecution_copies
    (E : Execution
      (activeTensor (K := K) (tick := tick) allocation m F ε)
      (Tensor.directSum (fun _ : J =>
        producedTensor (K := K) (tick := tick) allocation m F ε))) :
    (liftExecution allocation m F ε E).Copies = E.Copies := rfl

@[simp] theorem liftExecution_card_copies
    (E : Execution
      (activeTensor (K := K) (tick := tick) allocation m F ε)
      (Tensor.directSum (fun _ : J =>
        producedTensor (K := K) (tick := tick) allocation m F ε))) :
    Fintype.card (liftExecution allocation m F ε E).Copies = Fintype.card E.Copies := rfl

end MatrixMultiplication.AllFieldHistoryTickCarry

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open MatrixMultiplication.Foundation
attribute [local instance] Classical.propDecidable Classical.decEq

def activeWordsEquivOrders {K tick : ℕ} (W : Active K tick → Type*) :
    (∀ h, W h) ≃ (∀ sigma : Placement, ∀ h : ActiveOrder K tick sigma, W h.val) where
  toFun x _ h := x h.val
  invFun x h := x h.val.physicalOrder ⟨h, rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext sigma h
    rcases h with ⟨h, hh⟩
    cases hh
    rfl

variable {K tick : ℕ}

def joinGroupTargets (counts : Active K tick → JointPopulation.Shape → ℕ)
    (e : ∀ sigma : Placement,
      JointPopulation.Target (fun h : ActiveOrder K tick sigma => counts h.val)) :
    JointPopulation.Target counts :=
  (activeWordsEquivOrders (fun h => MatrixMultiplication.Foundation.ExactWords (counts h))).symm e

@[simp] theorem joinGroupTargets_apply (counts : Active K tick → JointPopulation.Shape → ℕ)
    (e : ∀ sigma : Placement,
      JointPopulation.Target (fun h : ActiveOrder K tick sigma => counts h.val))
    (h : Active K tick) :
    joinGroupTargets counts e h = e h.val.physicalOrder ⟨h, rfl⟩ := rfl

@[simp] theorem joinGroupTargets_on_group
    (counts : Active K tick → JointPopulation.Shape → ℕ)
    (e : ∀ sigma : Placement,
      JointPopulation.Target (fun h : ActiveOrder K tick sigma => counts h.val))
    (sigma : Placement) (h : ActiveOrder K tick sigma) :
    joinGroupTargets counts e h.val = e sigma h := by
  rcases h with ⟨h, hh⟩
  cases hh
  rfl

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryMasks AllFieldHistoryIncomingMasks
open JointPopulation JointCanonicalization JointCanonicalCW InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def groupCounts (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) : JointPopulation.Shape → ℕ :=
  activeCounts allocation m h.val

abbrev GroupRaw (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  RawPairs (groupCounts (K := K) (tick := tick) allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)

end MatrixMultiplication.AllFieldHistoryGroupMasks

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupedRecovery

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev GroupTarget (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Target (groupCounts (K := K) (tick := tick) allocation m sigma)

def groupCoordinates (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : GroupTarget (K := K) (tick := tick) allocation m sigma) :=
  pairEquiv (groupCounts allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7) e

def groupCoarse {sigma : Placement} (side : Fin 3) (h : ActiveOrder K tick sigma)
    (w : (Fin (activeHalfLength h.val) → Fin 7) × (Fin (activeHalfLength h.val) → Fin 7)) :=
  coarse activeHalfLength activeHalfLength AllFieldHistoryRecovery.halfLength_le_eight
    side h.val w

def groupIdealSide (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (sigma : Placement) (e : GroupTarget (K := K) (tick := tick) allocation m sigma)
    (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Prop :=
  coarseMask (groupCounts allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7) groupCoarse side e w ∧
    rawWindows (SL := fun h : ActiveOrder K tick sigma => Statistic h.val)
      (SR := fun h : ActiveOrder K tick sigma => Statistic h.val)
      (groupCounts allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun c => statistic c.1.val) (fun c => statistic c.1.val)
      (fun c => leftLaw c.1.val c.2 side) (fun c => rightLaw c.1.val c.2 side)
      (fun c => AllFieldHistoryMasks.childWidth ε c.1.val)
      (fun c => AllFieldHistoryMasks.childWidth ε c.1.val) e w

end MatrixMultiplication.AllFieldHistoryGroupedRecovery

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistorySourceAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.GroupOrbitProjection

open PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

def transportedOrbit {G RX CX : Type*} [Group G] [Fintype G] [MulAction G CX]
    (ex : RX ≃ CX) (x : RX) : Finset RX :=
  @OrbitCounting.orbitSet G RX _ (EquivOrbitTransport.action ex) _ _ x

section RawHistories

open JointPopulation JointCanonicalization

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ) (L R : H → Type*)

def rawOrbit (e : Target counts) (w : RawPairs counts L R) :
    Finset (RawPairs counts L R) :=
  transportedOrbit (G := HalfClassPermutations (ClassPositions counts))
    (pairEquiv counts L R e) w

end RawHistories

end MatrixMultiplication.GroupOrbitProjection

end
end




section





noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupedRecovery

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def localOrbit (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : GroupTarget (K := K) (tick := tick) allocation m sigma)
    (w : GroupRaw (K := K) (tick := tick) allocation m sigma) : Finset (GroupRaw (K := K) (tick := tick) allocation m sigma) :=
  GroupOrbitProjection.rawOrbit (groupCounts allocation m sigma)
    (fun h => Fin (activeHalfLength h.val) → Fin 7)
    (fun h => Fin (activeHalfLength h.val) → Fin 7) e w

end MatrixMultiplication.AllFieldHistoryGroupedRecovery






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_InitialLeafRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

def binaryEntropyRate (d : ℚ) : ℝ :=
  entropyTerm (1 - (d : ℝ)) + entropyTerm (d : ℝ) + (d : ℝ) * Real.log 2

end

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_ComplexRationalTypes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.Foundation

open scoped BigOperators

structure RationalLaw (A : Type*) [Fintype A] where
  mass : A → ℚ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace RationalLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def toFiniteLaw (p : RationalLaw A) : FiniteLaw A where
  mass a := p.mass a
  nonneg a := by exact_mod_cast p.nonneg a
  total := by exact_mod_cast p.total

@[simp] theorem toFiniteLaw_mass (p : RationalLaw A) (a : A) :
    p.toFiniteLaw.mass a = (p.mass a : ℝ) := rfl

end RationalLaw

end MatrixMultiplication.Foundation

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointTypeCounts
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointTypeCounts

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

section FixedClasses

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (P A : C → Type*)
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

abbrev FixedClassWords (counts : ∀ c, A c → ℕ) :=
  ∀ c, {w : P c → A c // ∀ a, wordPopulation w a = counts c a}

end FixedClasses

section CoarseFibers

variable {I A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

abbrev FixedCoarseWords (counts : A → ℕ) (f : A → B) (k : I → B) :=
  {w : I → A // (∀ a, wordPopulation w a = counts a) ∧ ∀ i, f (w i) = k i}

def fixedCoarseWordsEquiv (counts : A → ℕ) (f : A → B) (k : I → B) :
    FixedCoarseWords counts f k ≃
      ConditionalWords k (fun b a => if f a = b then counts a else 0) := by
  classical
  apply Equiv.subtypeEquivRight
  intro w
  constructor
  · rintro ⟨hw, hk⟩ b a
    change Fintype.card {i : I // k i = b ∧ w i = a} =
      if f a = b then counts a else 0
    by_cases hab : f a = b
    · rw [ite_eq_left hab, ← hw a]
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro i
      constructor
      · exact And.right
      · intro hwa
        exact ⟨by rw [← hk i, hwa, hab], hwa⟩
    · rw [ite_eq_right hab]
      have : IsEmpty {i : I // k i = b ∧ w i = a} := ⟨fun i => by
        apply hab
        rw [← i.property.2, hk i.val, i.property.1]⟩
      exact Fintype.card_of_isEmpty
  · intro hw
    constructor
    · intro a
      calc
        wordPopulation w a =
            ∑ b, wordPopulation (fun i : {i // w i = a} => k i.val) b :=
          (wordPopulation_sum _).symm
        _ = ∑ b, Fintype.card {i : I // k i = b ∧ w i = a} := by
          apply Finset.sum_congr rfl
          intro b _
          rw [wordPopulation_fiber]
          exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)
        _ = counts a := by simp only [hw] <;> simp
    · intro i
      by_cases h : f (w i) = k i
      · exact h
      exfalso
      have hzero := hw (k i) (w i)
      simp only [h, ite_false, if_false] at hzero
      have hpos : 0 < Fintype.card {j : I // k j = k i ∧ w j = w i} :=
        Fintype.card_pos_iff.mpr ⟨⟨i, rfl, rfl⟩⟩
      exact (Nat.ne_of_gt hpos) hzero

end CoarseFibers

end MatrixMultiplication.JointTypeCounts

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityIncidence

open MatrixMultiplication.Foundation JointTypeCounts
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Actions

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

abbrev ClassPerm := ∀ c, Equiv.Perm (Pos c)

def permuteFixedWords (counts : ∀ c, A c → ℕ)
    (g : ClassPerm Pos) (w : FixedClassWords Pos A counts) :
    FixedClassWords Pos A counts :=
  fun c => ⟨(w c).val ∘ ((g c)⁻¹ : Equiv.Perm (Pos c)), fun a =>
    (wordPopulation_reindex (w c).val (g c)⁻¹ a).trans ((w c).property a)⟩

@[instance_reducible]
def fixedWordsMulAction (counts : ∀ c, A c → ℕ) :
    MulAction (ClassPerm Pos) (FixedClassWords Pos A counts) where
  smul := permuteFixedWords Pos A counts
  one_smul w := by
    funext c
    apply Subtype.ext
    funext i
    rfl
  mul_smul g h w := by
    funext c
    apply Subtype.ext
    funext i
    change (w c).val (((g * h) c)⁻¹ i) =
      (w c).val ((h c)⁻¹ ((g c)⁻¹ i))
    simp only [Pi.mul_apply, mul_inv_rev, Equiv.Perm.mul_apply]

attribute [local instance] fixedWordsMulAction

end Actions

attribute [local instance] fixedWordsMulAction

end MatrixMultiplication.JointCompatibilityIncidence

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointPopulationMixedCompatibility
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.initialExecution_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationCompatibility

open MatrixMultiplication.Foundation JointPopulation JointTypeCounts InheritedMasks
open JointCompatibilityIncidence
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ)

abbrev ClassKey := H × Fin 17

abbrev ClassPos (b : Position counts → Fin 17) (c : ClassKey (H := H)) :=
  {i : Positions counts c.1 // b ⟨c.1, i⟩ = c.2}

def classCounts (s : Fin 3) (c : ClassKey (H := H)) (u : Shape) : ℕ :=
  if shapeSide s u = c.2 then counts c.1 u else 0

abbrev FixedSideTargets (s : Fin 3) (b : Position counts → Fin 17) :=
  {e : Target counts // ∀ h i, shapeSide s ((e h).val i) = b ⟨h, i⟩}

def candidateEquiv (s : Fin 3) (b : Position counts → Fin 17) :
    FixedSideTargets counts s b ≃
      FixedClassWords (ClassPos counts b) (fun _ => Shape) (classCounts counts s) := by
  let split : FixedSideTargets counts s b ≃
      (∀ h, FixedCoarseWords (counts h) (shapeSide s) (fun i => b ⟨h, i⟩)) :=
    { toFun := fun e h => ⟨(e.val h).val, (e.val h).property, e.property h⟩
      invFun := fun v =>
        ⟨fun h => ⟨(v h).val, (v h).property.1⟩, fun h => (v h).property.2⟩
      left_inv := by
        intro e
        apply Subtype.ext
        funext h
        apply Subtype.ext
        rfl
      right_inv := by
        intro v
        funext h
        apply Subtype.ext
        rfl }
  let perHistory (h : H) :=
    (fixedCoarseWordsEquiv (counts h) (shapeSide s) (fun i => b ⟨h, i⟩)).trans
      (conditionalWordsEquiv (fun i : Positions counts h => b ⟨h, i⟩)
        (fun a u => if shapeSide s u = a then counts h u else 0))
  refine split.trans ((Equiv.piCongrRight perHistory).trans ?_)
  exact
    { toFun := fun v c => v c.1 c.2
      invFun := fun v h a => v (h, a)
      left_inv := by intro v; rfl
      right_inv := by
        intro v
        funext c
        rcases c with ⟨h, a⟩
        rfl }

omit [Fintype H] [DecidableEq H] in
@[simp] theorem candidateEquiv_apply (s : Fin 3) (b : Position counts → Fin 17)
    (e : FixedSideTargets counts s b) (c : ClassKey (H := H)) (i : ClassPos counts b c) :
    ((candidateEquiv counts s b e) c).val i = (e.val c.1).val i.val := rfl

def shapeStatisticCount {A : Type*} [Fintype A] [DecidableEq A]
    (e : Target counts) (h : H) (u : Shape) (f : Positions counts h → A) (a : A) : ℕ :=
  wordPopulation (fun i : Class counts e h u => f i.val) a

end MatrixMultiplication.JointPopulationCompatibility






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitData

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitCount JointPopulation JointCanonicalization
open JointCoarseHashing PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ} {sigma : Placement}

abbrev Counts (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  groupCounts (K := K) (tick := tick) allocation m sigma
abbrev Targets (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Target (Counts (K := K) (tick := tick) allocation m sigma)
abbrev Pos (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Position (Counts (K := K) (tick := tick) allocation m sigma)
abbrev Raw (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  GroupRaw (K := K) (tick := tick) allocation m sigma
abbrev Orbit (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Fin 3 × GroupOrbit (K := K) (tick := tick) allocation m sigma
abbrev Variable (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Fin 3 × Raw (K := K) (tick := tick) allocation m sigma

def tripleSide {P : Type*} (s : Fin 3) (t : Triple P) : Word P :=
  (Matrix.vecCons (t.1) (Matrix.vecCons (t.2.1) (Matrix.vecCons (t.2.2) Matrix.vecEmpty))) s

def reorder {P : Type*} (sigma : Placement) (t : Triple P) : Triple P :=
  (tripleSide (sigma 0) t, tripleSide (sigma 1) t, tripleSide (sigma 2) t)

@[simp] theorem tripleSide_reorder {P : Type*} (sigma : Placement)
    (t : Triple P) (s : Fin 3) :
    tripleSide s (reorder sigma t) = tripleSide (sigma s) t :=
  JointCoarseReorder.tripleSide_reorder sigma t s

theorem reorder_injective {P : Type*} (sigma : Placement) :
    Function.Injective (reorder (P := P) sigma) :=
  JointCoarseReorder.reorder_injective sigma

def coarse (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) : Triple (Pos (K := K) (tick := tick) allocation m sigma) :=
  reorder sigma (triple (Counts (K := K) (tick := tick) allocation m sigma) e)

theorem coarse_injective (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Function.Injective (coarse (K := K) (tick := tick) allocation m sigma) :=
  (reorder_injective sigma).comp (triple_injective (Counts (K := K) (tick := tick) allocation m sigma))

def sharing (h : ActiveOrder K tick sigma) : Bool :=
  match h.val.val.1 with
  | .stageA _ => true
  | .stageB _ => true
  | .stageC _ => false

def workComplement (w : Work K) : w.Statistic ≃ w.Statistic :=
  match w with
  | .stageA _ => CWCompleteStatistics.orderedComplementStatistic
  | .stageB _ => CWCompleteStatistics.complementStatistic
  | .stageC _ => Equiv.refl _

def complement (h : ActiveOrder K tick sigma) : Statistic h.val ≃ Statistic h.val :=
  workComplement h.val.val.1

def compatibilityLaw (right : Bool) (side : Fin 3) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) : Statistic h.val → ℝ :=
  let weight : Fin 3 → ℕ := fun i =>
    if right then activeParentShape h.val (sigma i) - (shapeSide (sigma i) u).val
    else (shapeSide (sigma i) u).val
  let source : Fin 3 := if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0
  (if right then rightLaw h.val u source else leftLaw h.val u source) ∘
    (complement h).symm

def designated (right : Bool) (side : Fin 3) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) : Prop :=
  sharing h = true ∧
    let weight : Fin 3 → ℕ := fun i =>
      if right then activeParentShape h.val (sigma i) - (shapeSide (sigma i) u).val
      else (shapeSide (sigma i) u).val
    if side = 1 then weight 2 = 0
    else if side = 2 then weight 0 * weight 1 = 0 else False

def fineCompatible (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ (right : Bool) h u, designated right side sigma h u → ∀ a : Statistic h.val,
    |(JointPopulationCompatibility.shapeStatisticCount (Counts (K := K) (tick := tick) allocation m sigma) e h u
        (fun i => statistic h.val (if right then (w h i).2 else (w h i).1)) a : ℝ) -
      (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) * compatibilityLaw right side sigma h u a| ≤
        (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) * AllFieldHistoryMasks.childWidth ε h.val

def ownWord (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Word (Pos (K := K) (tick := tick) allocation m sigma) :=
  fun p => groupCoarse 0 p.1 (w p.1 p.2)

def Compatible (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Prop :=
  tripleSide side (coarse allocation m sigma e) = ownWord allocation m sigma w ∧
    fineCompatible allocation m ε sigma side e w

def orbitOf (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : GroupOrbit (K := K) (tick := tick) allocation m sigma :=
  Quotient.mk'' (groupCoordinates allocation m sigma e w)

def full (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma) :
    Finset (Variable (K := K) (tick := tick) allocation m sigma) :=
  Finset.univ.filter fun v => v.1 = o.1 ∧ orbitOf allocation m sigma e v.2 = o.2

def actualCompatible (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (v : Variable (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∃ f, coarse allocation m sigma f = t ∧ Compatible allocation m ε sigma v.1 f v.2

def actualUseful (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (v : Variable (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∃ f, coarse allocation m sigma f = t ∧
    groupIdealSide allocation m ε (sigma v.1) sigma f v.2

@[simp] theorem actualCompatible_coarse (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (v : Variable (K := K) (tick := tick) allocation m sigma) :
    actualCompatible allocation m ε sigma (coarse allocation m sigma e) v ↔
      Compatible allocation m ε sigma v.1 e v.2 := by
  constructor
  · rintro ⟨f, hf, hv⟩
    exact (coarse_injective allocation m sigma hf) ▸ hv
  · exact fun hv => ⟨e, rfl, hv⟩

@[simp] theorem actualUseful_coarse (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (v : Variable (K := K) (tick := tick) allocation m sigma) :
    actualUseful allocation m ε sigma (coarse allocation m sigma e) v ↔
      groupIdealSide allocation m ε (sigma v.1) sigma e v.2 := by
  constructor
  · rintro ⟨f, hf, hv⟩
    exact (coarse_injective allocation m sigma hf) ▸ hv
  · exact fun hv => ⟨e, rfl, hv⟩

end MatrixMultiplication.AllFieldGroupOrbitData

end




namespace MatrixMultiplication.JointOrbitFibers

attribute [local instance] Classical.propDecidable

variable {G X Y : Type*} [Group G] [MulAction G X] [Fintype X]

noncomputable def fullFiber (q : MulAction.orbitRel.Quotient G X) : Finset X :=
  Finset.univ.filter fun x => (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) = q

@[simp] theorem mem_fullFiber {q : MulAction.orbitRel.Quotient G X} {x : X} :
    x ∈ fullFiber q ↔ (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) = q := by
  simp only [fullFiber, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_fullFiber_mk {x y : X} :
    y ∈ fullFiber (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) ↔
      ∃ g : G, g • x = y := by
  rw [mem_fullFiber]
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

noncomputable def transportedFiber (e : Y ≃ X)
    (q : MulAction.orbitRel.Quotient G X) : Finset Y :=
  (fullFiber q).map e.symm.toEmbedding

@[simp] theorem mem_transportedFiber (e : Y ≃ X)
    {q : MulAction.orbitRel.Quotient G X} {y : Y} :
    y ∈ transportedFiber e q ↔
      (Quotient.mk'' (e y) : MulAction.orbitRel.Quotient G X) = q := by
  constructor
  · intro h
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp h
    have he : e y = x := by
      rw [← hxy]
      exact e.apply_symm_apply x
    rw [he]
    exact mem_fullFiber.mp hx
  · intro h
    exact Finset.mem_map.mpr ⟨e y, mem_fullFiber.mpr h, e.symm_apply_apply y⟩

@[simp] theorem transportedFiber_card (e : Y ≃ X)
    (q : MulAction.orbitRel.Quotient G X) :
    (transportedFiber e q).card = (fullFiber q).card :=
  Finset.card_map _

theorem transportedFiber_mk [Fintype G] [DecidableEq X] [DecidableEq Y]
    (e : Y ≃ X) (y : Y) :
    letI : MulAction G Y := EquivOrbitTransport.action e
    transportedFiber e
        (Quotient.mk'' (e y) : MulAction.orbitRel.Quotient G X) =
      OrbitCounting.orbitSet (G := G) y := by
  let : MulAction G Y := EquivOrbitTransport.action e
  ext z
  rw [mem_transportedFiber]
  constructor
  · intro h
    have hz : e z ∈ fullFiber
        (Quotient.mk'' (e y) : MulAction.orbitRel.Quotient G X) :=
      mem_fullFiber.mpr h
    obtain ⟨g, hg⟩ := mem_fullFiber_mk.mp hz
    apply Finset.mem_image.mpr
    refine ⟨g, Finset.mem_univ _, ?_⟩
    change e.symm (g • e y) = z
    rw [hg, e.symm_apply_apply]
  · intro h
    obtain ⟨g, _, hg⟩ := Finset.mem_image.mp h
    apply Quotient.sound
    change ∃ g : G, g • e y = e z
    refine ⟨g, ?_⟩
    have he := congrArg e hg
    change e (e.symm (g • e y)) = e z at he
    simpa only [e.apply_symm_apply] using he

end MatrixMultiplication.JointOrbitFibers





noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitData

open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitCount JointCoarseHashing PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

local instance canonicalGroupAction_r90b57f_1 (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    MulAction
      (HalfClassPermutations (GroupPositions (K := K) (tick := tick) (sigma := sigma) allocation m))
      (JointCanonicalization.CanonicalPairs (groupCounts (K := K) (tick := tick) allocation m sigma)
        (fun h => Fin (activeHalfLength h.val) → Fin 7)
        (fun h => Fin (activeHalfLength h.val) → Fin 7)) :=
  completeWordPairMulAction
local instance canonicalGroupFintype (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Fintype
      (JointCanonicalization.CanonicalPairs (groupCounts (K := K) (tick := tick) allocation m sigma)
        (fun h => Fin (activeHalfLength h.val) → Fin 7)
        (fun h => Fin (activeHalfLength h.val) → Fin 7)) := by
  letI : ∀ c : GroupClasses K tick sigma,
      Fintype (GroupPositions allocation m c) := fun _ => Fin.fintype _
  letI : ∀ c : GroupClasses K tick sigma,
      DecidableEq (GroupPositions allocation m c) := fun _ => Classical.decEq _
  letI : ∀ c : GroupClasses K tick sigma,
      Fintype (GroupLetters c) := fun _ => Pi.instFintype
  exact HistorySymmetry.completeWordPairFintype

def tag (allocation : Allocation) (m : ℕ) (sigma : Placement) (side : Fin 3) :
    Raw (K := K) (tick := tick) allocation m sigma ↪ Variable (K := K) (tick := tick) allocation m sigma where
  toFun w := (side, w)
  inj' := by intro w v h; exact congrArg Prod.snd h

theorem full_eq_tagged_fiber (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma) :
    full allocation m sigma e o =
      (JointOrbitFibers.transportedFiber (groupCoordinates allocation m sigma e) o.2).map
        (tag allocation m sigma o.1) := by
  ext v
  constructor
  · intro hv
    have hh := (Finset.mem_filter.mp hv).2
    apply Finset.mem_map.mpr
    refine ⟨v.2, ?_, ?_⟩
    · exact (JointOrbitFibers.mem_transportedFiber (groupCoordinates allocation m sigma e)).mpr hh.2
    · exact Prod.ext hh.1.symm rfl
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl,
      (JointOrbitFibers.mem_transportedFiber (groupCoordinates allocation m sigma e)).mp hw⟩

theorem full_eq_tagged_localOrbit (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    full allocation m sigma e (side, orbitOf allocation m sigma e w) =
      (localOrbit allocation m sigma e w).map (tag allocation m sigma side) := by
  rw [full_eq_tagged_fiber]
  dsimp only [orbitOf]
  apply congrArg (fun t : Finset (Raw (K := K) (tick := tick) allocation m sigma) =>
    t.map (tag allocation m sigma side))
  refine (JointOrbitFibers.transportedFiber_mk
    (G := HalfClassPermutations (GroupPositions (sigma := sigma) allocation m))
    (groupCoordinates allocation m sigma e) w).trans ?_
  ext v
  simp only [localOrbit, GroupOrbitProjection.rawOrbit, GroupOrbitProjection.transportedOrbit,
    OrbitCounting.orbitSet,
    Finset.mem_image, Finset.mem_univ, true_and]
  rfl

@[simp] theorem full_card_localOrbit (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    (full allocation m sigma e (side, orbitOf allocation m sigma e w)).card =
      (localOrbit allocation m sigma e w).card := by
  rw [full_eq_tagged_localOrbit, Finset.card_map]

end MatrixMultiplication.AllFieldGroupOrbitData

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_NativeCapacity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.half_unhalfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.unhalf_halfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldNativeCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A : Type*} [Fintype A]

def marginal (support : List Shape) (p : Shape → ℝ) (side : Fin 3)
    (k : Fin 17) : ℝ :=
  (support.map fun u => if u side = k.val then p u else 0).sum

def pairLaw (support : List Shape) (s : Shape) (p : Shape → ℝ)
    (q : Shape → A → ℝ) (ij : A × A) : ℝ :=
  (support.map fun u => p u * q u ij.1 * q (complement s u) ij.2).sum

def designated (priority : Placement) (position : Fin 3) (u : Shape) : Prop :=
  if position = 1 then u (priority 2) = 0
  else u (priority 0) = 0 ∨ u (priority 1) = 0

def singletonEntropy (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ) : ℝ :=
  (support.map fun u => if designated priority position u then
    p u * homogeneousEntropy (q u) else 0).sum

def residualLaw (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (k : Fin 17) (a : A) : ℝ :=
  (support.map fun u =>
    if ¬ designated priority position u ∧ u (priority position) = k.val
    then p u * q u a else 0).sum

def groupedEntropy (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ) : ℝ :=
  singletonEntropy support p priority position q +
    ∑ k : Fin 17, homogeneousEntropy (residualLaw support p priority position q k)

def nativeCapacity (support : List Shape) (s : Shape) (p : Shape → ℝ)
    (priority : Placement) (q : Shape → Fin 3 → A → ℝ) : Staggering.Capacity :=
  fun i => if i = 0 then homogeneousEntropy (marginal support p (priority 0))
    else homogeneousEntropy (pairLaw support s p (fun u => q u (priority i))) -
      2 * groupedEntropy support p priority i (fun u => q u (priority i))

@[simp] theorem nativeCapacity_first (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (priority : Placement) (q : Shape → Fin 3 → A → ℝ) :
    nativeCapacity support s p priority q 0 =
      homogeneousEntropy (marginal support p (priority 0)) := by
  simp [nativeCapacity]

def stageACapacity (g : Shape) : Staggering.Capacity :=
  nativeCapacity (below g) g (fun u => (stageALaw g u : ℝ))
    (Equiv.refl (Fin 3)) (fun u w a => (halfLaw u w a : ℝ))

def stageBCapacity (t : Shape) : Staggering.Capacity :=
  nativeCapacity (below t) t (fun u => (stageBLaw t u : ℝ))
    (stageBPriority t) (fun u w a => (littleLaw t u w a : ℝ))

def stageCCapacity (t u : Shape) (part : Fin 3) : Staggering.Capacity :=
  fun i => if i = part then binaryEntropyRate (binaryParameter t u) else Real.log 2

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationRates

open MatrixMultiplication.Foundation Filter JointPopulation
open scoped BigOperators Topology

def sideMass (p : Shape → ℝ) (s : Fin 3) (a : Fin 17) : ℝ :=
  ∑ u, if shapeSide s u = a then p u else 0

end MatrixMultiplication.JointPopulationRates






namespace MatrixMultiplication.AllFieldActiveLaws

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

def branchProbability {K : ℕ} (w : Work K) (b : w.Branch) : ℚ :=
  match w with
  | .stageA h => stageALaw (initialShape h.val) (aSplit ⟨h, b, false⟩)
  | .stageB h => stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩)
  | .stageC h => stageCWeight (cParameterParent h) (cShapeParent h) b

theorem branchProbability_nonneg {K : ℕ} (w : Work K) (b : w.Branch) :
    0 ≤ branchProbability w b := by
  cases w with
  | stageA h => exact (stageALaw_positive _ _ (aSplit_mem ⟨h, b, false⟩)).le
  | stageB h => exact (stageBLaw_positive _ _ (bSplit_mem ⟨h, b, false⟩)).le
  | stageC h => exact stageCWeight_nonnegative _ _ b

theorem branchProbability_total {K : ℕ} (w : Work K) :
    ∑ b : w.Branch, branchProbability w b = 1 := by
  cases w with
  | stageA h =>
      change (∑ b : ASplit h,
        stageALaw (initialShape h.val) (below (initialShape h.val))[b.val]) = 1
      rw [Fin.sum_univ_fun_getElem]
      exact stageALaw_normalized _ h.property
  | stageB h =>
      change (∑ b : BSplit h,
        stageBLaw (aShape h.val) (below (aShape h.val))[b.val]) = 1
      rw [Fin.sum_univ_fun_getElem]
      exact stageBLaw_normalized _ h.property
  | stageC h => exact stageCWeight_normalized _ _

def branchLaw {K : ℕ} (w : Work K) : FiniteLaw w.Branch where
  mass b := (branchProbability w b : ℝ)
  nonneg b := by exact_mod_cast branchProbability_nonneg w b
  total := by exact_mod_cast branchProbability_total w

@[simp] theorem branchLaw_mass {K : ℕ} (w : Work K) (b : w.Branch) :
    (branchLaw w).mass b = (branchProbability w b : ℝ) := rfl

def placedLaw {K : ℕ} (w : PlacedWork K) : FiniteLaw JointPopulation.Shape :=
  (branchLaw w.1).map (branchShape w)

@[simp] theorem placedLaw_mass {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) :
    (placedLaw w).mass u =
      ∑ b : w.1.Branch, if branchShape w b = u then
        (branchProbability w.1 b : ℝ) else 0 := by
  simp only [placedLaw, FiniteLaw.map_mass, branchLaw_mass]

def orderLaw {K tick : ℕ} {sigma : Placement} (h : ActiveOrder K tick sigma) :
    FiniteLaw JointPopulation.Shape := placedLaw h.val.val

def orderMass {K tick : ℕ} {sigma : Placement} (allocation : Allocation)
    (h : ActiveOrder K tick sigma) : ℝ :=
  amount allocation (h.val.val.1.source, h.val.val.2)

def orderCounts {K tick : ℕ} {sigma : Placement} (allocation : Allocation)
    (dilation : ℕ) (h : ActiveOrder K tick sigma) : JointPopulation.Shape → ℕ :=
  activeCounts allocation dilation h.val

end MatrixMultiplication.AllFieldActiveLaws






namespace MatrixMultiplication.AllFieldGroupNativeLaws

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldActiveLaws
open AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def nativeSplitWeightCode {K : ℕ} (w : Work K) (side : Fin 3)
    (b : w.Branch) : Fin 17 :=
  ⟨w.splitShape b side, Nat.lt_succ_of_le ((w.splitShape_spec b).1 side)⟩

@[simp] theorem nativeSplitWeightCode_val {K : ℕ} (w : Work K) (side : Fin 3)
    (b : w.Branch) : (nativeSplitWeightCode w side b).val = w.splitShape b side := rfl

end MatrixMultiplication.AllFieldGroupNativeLaws






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointAmbientEntropy
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators Topology
open Filter MatrixMultiplication.Foundation
open MatrixMultiplication.JointPopulation

namespace MatrixMultiplication.JointAmbientEntropy

section Empirical

variable {I A B : Type*} [Fintype I]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def empiricalFiniteLaw (w : I → A) (hpos : 0 < Fintype.card I) : FiniteLaw A where
  mass a := (wordPopulation w a : ℝ) / Fintype.card I
  nonneg a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  total := by
    rw [← Finset.sum_div, ← Nat.cast_sum, wordPopulation_sum]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos))

@[simp] theorem empiricalFiniteLaw_mass (w : I → A) (hpos : 0 < Fintype.card I) (a : A) :
    (empiricalFiniteLaw w hpos).mass a =
      (wordPopulation w a : ℝ) / Fintype.card I := rfl

end Empirical

end MatrixMultiplication.JointAmbientEntropy

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointOrdinaryPopulationSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section

namespace MatrixMultiplication.JointOrdinaryPopulationSelection

open MatrixMultiplication.Foundation JointPopulation JointPopulationRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {Hist : Type*} [Fintype Hist] [DecidableEq Hist]

def sideDegreeRate (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) (s : Fin 3) : ℝ :=
  ∑ h, mass h * (finiteEntropy (p h).mass - finiteEntropy (sideMass (p h).mass s))

def degreeRate (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) : ℝ :=
  max (sideDegreeRate mass p 0) (max (sideDegreeRate mass p 1) (sideDegreeRate mass p 2))

def selectionHashRate (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) (ε : ℝ) : ℝ :=
  degreeRate mass p + ε / 2

end MatrixMultiplication.JointOrdinaryPopulationSelection

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_InitialEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropy

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation
open JointPopulationRates JointOrdinaryPopulationSelection
open scoped BigOperators

abbrev PlacedInitial := Fin sortedInitial.length × Placement

def initialShapeCode (p : PlacedInitial) : JointPopulation.Shape :=
  rootShape ((0 : Fin 1), p.1) p.2

@[simp] theorem initialShapeCode_side (p : PlacedInitial) (s : Fin 3) :
    (JointPopulation.shapeSide s (initialShapeCode p)).val =
      sortedInitial.get p.1 (p.2.symm s) := by
  simp only [initialShapeCode, rootShape, encodePhysicalShape_side, initialShape]

@[simp] theorem rootShape_eq_initialShapeCode {K : ℕ} (j : Fin K)
    (g : Fin sortedInitial.length) (phi : Placement) :
    rootShape (j, g) phi = initialShapeCode (g, phi) := rfl

def placedInitialLaw : FiniteLaw PlacedInitial where
  mass p := (initialLaw (sortedInitial.get p.1) : ℝ) / 6
  nonneg p := div_nonneg (by
    exact_mod_cast (initialLaw_positive _ (List.get_mem _ _)).le) (by norm_num)
  total := by
    have hsum : (∑ g : Fin sortedInitial.length,
        (initialLaw (sortedInitial.get g) : ℝ)) = 1 := by
      exact_mod_cast initial_amount_sum 1 (0 : Fin 1)
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ,
      PhysicalOrders.card_physical_orders, nsmul_eq_mul]
    calc
      _ = ∑ g : Fin sortedInitial.length,
          (initialLaw (sortedInitial.get g) : ℝ) := by
        apply Finset.sum_congr rfl
        intro g _
        ring
      _ = 1 := hsum

def orderedInitialLaw : FiniteLaw JointPopulation.Shape :=
  placedInitialLaw.map initialShapeCode

end MatrixMultiplication.AllFieldInitialEntropy

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Terminal1_1_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldNativeCapacity
open scoped BigOperators
def B1_1_6U0_0_4Leaf : Ball := ⟨0, 0⟩

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ActiveSums
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativeSplitWeightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.half_unhalfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.unhalf_halfPosition _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def aRelot {K L : ℕ} (lot : Fin L) (h : AfterA K) : AfterA L :=
  ⟨⟨(lot, h.1.val.2), h.1.property⟩, h.2⟩

def bRelot {K L : ℕ} (lot : Fin L) (h : AfterB K) : AfterB L :=
  ⟨⟨aRelot lot h.1.val, h.1.property⟩, h.2⟩

def partRelot {K L : ℕ} (lot : Fin L) (h : PartC K) : PartC L :=
  (⟨bRelot lot h.1.val, h.1.property⟩, h.2)

def workRelot {K L : ℕ} (lot : Fin L) : Work K → Work L
  | .stageA h => .stageA ⟨(lot, h.val.2), h.property⟩
  | .stageB h => .stageB ⟨aRelot lot h.val, h.property⟩
  | .stageC h => .stageC (partRelot lot h)

@[simp] theorem workRelot_lot {K L : ℕ} (lot : Fin L) (w : Work K) :
    (workRelot lot w).lot = lot := by cases w <;> rfl

@[simp] theorem workRelot_stage {K L : ℕ} (lot : Fin L) (w : Work K) :
    (workRelot lot w).stage = w.stage := by cases w <;> rfl

@[simp] theorem workRelot_self {K : ℕ} (w : Work K) : workRelot w.lot w = w := by
  cases w <;> rfl

@[simp] theorem workRelot_relot {K L M : ℕ} (first : Fin L) (last : Fin M)
    (w : Work K) : workRelot last (workRelot first w) = workRelot last w := by
  cases w <;> rfl

@[simp] theorem workAmount_relot {K L : ℕ} (allocation : Allocation)
    (lot : Fin L) (w : Work K) :
    workAmount allocation (workRelot lot w) = workAmount allocation w := by
  cases w <;> rfl

def workLotEquiv (K : ℕ) : Work K ≃ Fin K × Work 1 where
  toFun w := (w.lot, workRelot 0 w)
  invFun h := workRelot h.1 h.2
  left_inv w := by simp only [workRelot_relot, workRelot_self]
  right_inv h := by
    rcases h with ⟨lot, w⟩
    apply Prod.ext
    · exact workRelot_lot lot w
    · simp only [workRelot_relot]
      have hzero : (0 : Fin 1) = w.lot := Subsingleton.elim _ _
      rw [hzero, workRelot_self]

@[simp] theorem workLotEquiv_symm_apply (K : ℕ) (lot : Fin K) (w : Work 1) :
    (workLotEquiv K).symm (lot, w) = workRelot lot w := rfl

def shapeValue {K : ℕ} (fA fB : Shape → ℝ)
    (fC : Shape → Shape → Fin 3 → ℝ) : Work K → ℝ
  | .stageA h => fA (initialShape h.val)
  | .stageB h => fB (aShape h.val)
  | .stageC h => fC (cParameterParent h) (cShapeParent h) h.2

@[simp] theorem shapeValue_relot {K L : ℕ} (fA fB : Shape → ℝ)
    (fC : Shape → Shape → Fin 3 → ℝ) (lot : Fin L) (w : Work K) :
    shapeValue fA fB fC (workRelot lot w) = shapeValue fA fB fC w := by
  cases w <;> rfl

def shapeCapacity {K : ℕ} (fA fB : Shape → Staggering.Capacity)
    (fC : Shape → Shape → Fin 3 → Staggering.Capacity) (w : Work K) : Staggering.Capacity :=
  fun i => shapeValue (fun g => fA g i) (fun t => fB t i) (fun t u part => fC t u part i) w

end MatrixMultiplication.AllFieldHistory

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_InitialHash
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldInitialHash

open MatrixMultiplication.Foundation AllFieldFiniteFamily AllFieldInitialStep
open JointPopulation JointCoarseHashing
open scoped BigOperators Classical

variable {K : ℕ} (counts : Fin K → Shape → ℕ)

def xKeep (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Position counts) k) (w : CoarseWord counts) : Prop :=
  JointHashing.xHash s (castWord k w) ∈ U

def yKeep (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Position counts) k) (w : CoarseWord counts) : Prop :=
  JointHashing.yHash s (castWord k w) ∈ U

def zKeep (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Position counts) k) (w : CoarseWord counts) : Prop :=
  JointHashing.zHash (twoUnit k) s (fun _ => (16 : ZMod (37 ^ k))) (castWord k w) ∈ U

theorem ambient_support {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ) (f : Triple (Position counts))
    (hf : f ∈ ambientSet counts (fun _ => 16)) :
    HasSupportSum (fun _ => 16) f :=
  (Finset.mem_filter.mp hf).2.1

theorem target_mem_ambient
    (hsupport : ∀ h u, 0 < counts h u → u.1.val + u.2.1.val + u.2.2.val = 16)
    (e : Target counts) : triple counts e ∈ ambientSet counts (fun _ => 16) :=
  targetSet_subset_ambient counts (fun _ => 16) hsupport
    (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)

theorem side_survival_iff (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample (Position counts) k) (e : Triple (Position counts))
    (he : HasSupportSum (fun _ => 16) e) :
    JointCoarseAssignment.survives (xKeep counts k U s) (yKeep counts k U s)
      (zKeep counts k U s) e ↔ Survives k U e s :=
  full_survival_iff k U hAP (fun _ => 16) e he s

theorem isolated_of_good
    (hsupport : ∀ h u, 0 < counts h u → u.1.val + u.2.1.val + u.2.2.val = 16)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample (Position counts) k) (e : Target counts)
    (hgood : JointOrdinarySelection.Good k U (ambientSet counts (fun _ => 16))
      (triple counts e) s) :
    AllFieldInitialExact.Isolated counts (xKeep counts k U s) (yKeep counts k U s)
      (zKeep counts k U s) e := by
  constructor
  · exact (side_survival_iff counts k U hAP s (triple counts e)
      (triple_support counts (fun _ => 16) hsupport e)).mpr hgood.1
  · intro f hf hsurvives hshare
    by_contra hne
    have hs := (side_survival_iff counts k U hAP s f (ambient_support counts f hf)).mp
      hsurvives
    exact JointOrdinarySelection.good_excludes_neighbor k U
      (ambientSet counts (fun _ => 16)) (triple counts e) f s hgood hf hne hshare hs

abbrev SelectedTargets (G : Finset (Target counts)) := {e : Target counts // e ∈ G}

def toTarget (G : Finset (Target counts)) : SelectedTargets counts G → Target counts :=
  Subtype.val

theorem toTarget_injective (G : Finset (Target counts)) :
    Function.Injective (toTarget counts G) := Subtype.val_injective

@[simp] theorem selectedTargets_card (G : Finset (Target counts)) :
    Fintype.card (SelectedTargets counts G) = G.card := Fintype.card_coe G

variable {F : Type*} [Field F] {N : ℕ}

def selectedExecution (total : ∀ h, ∑ u, counts h u = N)
    (hsupport : ∀ h u, 0 < counts h u → u.1.val + u.2.1.val + u.2.2.val = 16)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample (Position counts) k) (G : Finset (Target counts))
    (hgood : ∀ e ∈ G, JointOrdinarySelection.Good k U
      (ambientSet counts (fun _ => 16)) (triple counts e) s) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : SelectedTargets counts G => JointCanonicalInitial.canonical counts)) :=
  AllFieldInitialExact.selectedExecution counts
    (xKeep counts k U s) (yKeep counts k U s) (zKeep counts k U s)
    total (toTarget counts G) (toTarget_injective counts G)
    (fun e => target_mem_ambient counts hsupport e.val)
    (fun e => isolated_of_good counts hsupport k U hAP s e.val (hgood e.val e.property))

@[simp] theorem selectedExecution_copies (total : ∀ h, ∑ u, counts h u = N)
    (hsupport : ∀ h u, 0 < counts h u → u.1.val + u.2.1.val + u.2.2.val = 16)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample (Position counts) k) (G : Finset (Target counts))
    (hgood : ∀ e ∈ G, JointOrdinarySelection.Good k U
      (ambientSet counts (fun _ => 16)) (triple counts e) s) :
    Fintype.card (selectedExecution (F := F) counts total hsupport k U hAP s G hgood).Copies = 1 :=
  rfl

end MatrixMultiplication.AllFieldInitialHash

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_InitialFamily
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldInitialFamily

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldFiniteFamily
open AllFieldInitialEntropy JointOrdinaryPopulationSelection Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {K : ℕ} (allocation : Allocation)

def grid : ℕ := populationLength (K := K) allocation 1

def hashRate (ε : ℝ) : ℝ :=
  selectionHashRate (fun _ : Fin K => (grid (K := K) allocation : ℝ))
    (fun _ => orderedInitialLaw) ((grid (K := K) allocation : ℝ) * ε)

abbrev Sample (ε : ℝ) (dilation : ℕ) :=
  JointCoarseHashing.Sample (JointPopulation.Position
    (initialJointCounts (K := K) allocation dilation))
    (JointOrdinarySelection.hashLevel (hashRate (K := K) allocation ε) dilation)

def Good (ε : ℝ) (dilation : ℕ)
    (s : Sample (K := K) allocation ε dilation)
    (e : JointPopulation.Target (initialJointCounts (K := K) allocation dilation)) : Prop :=
  JointOrdinarySelection.Good
    (JointOrdinarySelection.hashLevel (hashRate (K := K) allocation ε) dilation)
    (JointOrdinarySelection.hashSet (hashRate (K := K) allocation ε) dilation)
    (JointPopulation.ambientSet (initialJointCounts allocation dilation) (fun _ => 16))
    (JointPopulation.triple (initialJointCounts allocation dilation) e) s

def executionWithWidth (F : Type*) [Field F] (ε residentWidth : ℝ) (dilation : ℕ)
    (s : Sample (K := K) allocation ε dilation)
    (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation)))
    (hgood : ∀ e ∈ G, Good allocation ε dilation s e) :
    Execution (cwSource F K (populationLength (K := K) allocation dilation))
      (Tensor.directSum (fun _ : AllFieldInitialHash.SelectedTargets
          (initialJointCounts (K := K) allocation dilation) G =>
        stateTensor F (K := K) allocation dilation residentWidth 0)) :=
  AllFieldInitialState.execution allocation dilation F residentWidth
    (AllFieldInitialHash.selectedExecution (F := F)
      (initialJointCounts allocation dilation) (initialJointCounts_sum allocation dilation)
      (initialJointCounts_support allocation dilation)
      (JointOrdinarySelection.hashLevel (hashRate (K := K) allocation ε) dilation)
      (JointOrdinarySelection.hashSet (hashRate (K := K) allocation ε) dilation)
      (JointOrdinarySelection.hashSet_AP (hashRate (K := K) allocation ε) dilation)
      s G hgood)

@[simp] theorem executionWithWidth_copies (F : Type*) [Field F]
    (ε residentWidth : ℝ) (dilation : ℕ)
    (s : Sample (K := K) allocation ε dilation)
    (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation)))
    (hgood : ∀ e ∈ G, Good allocation ε dilation s e) :
    Fintype.card
      (executionWithWidth allocation F ε residentWidth dilation s G hgood).Copies = 1 := rfl

def execution (F : Type*) [Field F] (ε : ℝ) (dilation : ℕ)
    (s : Sample (K := K) allocation ε dilation)
    (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation)))
    (hgood : ∀ e ∈ G, Good allocation ε dilation s e) :
    Execution (cwSource F K (populationLength (K := K) allocation dilation))
      (Tensor.directSum (fun _ : AllFieldInitialHash.SelectedTargets
          (initialJointCounts (K := K) allocation dilation) G =>
        stateTensor F (K := K) allocation dilation ε 0)) :=
  executionWithWidth allocation F ε ε dilation s G hgood

@[simp] theorem execution_copies (F : Type*) [Field F] (ε : ℝ) (dilation : ℕ)
    (s : Sample (K := K) allocation ε dilation)
    (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation)))
    (hgood : ∀ e ∈ G, Good allocation ε dilation s e) :
    Fintype.card (execution allocation F ε dilation s G hgood).Copies = 1 := rfl

end MatrixMultiplication.AllFieldInitialFamily

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_ScheduledPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldScheduledYield

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldNativeCapacity
open Filter
open scoped BigOperators Topology

def workCapacity {K : ℕ} : Work K → Staggering.Capacity :=
  shapeCapacity stageACapacity stageBCapacity stageCCapacity

end MatrixMultiplication.AllFieldScheduledYield

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_GroupSelectionParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldActiveCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldNativeCapacity AllFieldActiveLaws AllFieldScheduledYield
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def canonicalSideMass {K : ℕ} (w : Work K) (s : Fin 3) (k : Fin 17) : ℝ :=
  ∑ b : w.Branch, if w.splitShape b s = k.val then (branchLaw w).mass b else 0

def orderEntropyRate {K tick : ℕ} (allocation : Allocation) (sigma : Placement) : ℝ :=
  ∑ h : ActiveOrder K tick sigma,
    ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (orderLaw h).mass

def orderNativeDegree {K tick : ℕ} (allocation : Allocation) (sigma : Placement)
    (i : Fin 3) : ℝ :=
  ∑ h : ActiveOrder K tick sigma,
    ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      (finiteEntropy (orderLaw h).mass - workCapacity h.val.val.1 i)

end MatrixMultiplication.AllFieldActiveCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupAmbientDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldActiveGibbs

open AllFieldParameters AllFieldHistory AllFieldActiveLaws MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def splitCoordinateWeight (parents : List Shape) (data : List ℤ)
    (s : Shape) (i : Fin 3) (k : ℕ) : ℝ :=
  (weight (assigned (splitKeys parents) data (s, i, min k (s i - k))) : ℝ)

def splitPotential (parents : List Shape) (data : List ℤ)
    (s : Shape) (i : Fin 3) (k : ℕ) : ℝ :=
  Real.log (splitCoordinateWeight parents data s i k)

def splitNormalizer (parents : List Shape) (data : List ℤ) (s : Shape) : ℝ :=
  (((below s).map (splitWeight parents data s)).sum : ℚ)

def splitLogNormalizer (parents : List Shape) (data : List ℤ) (s : Shape) : ℝ :=
  Real.log (splitNormalizer parents data s)

def physicalPotential (parents : List Shape) (data : List ℤ) (s : Shape)
    (phi : Placement) (i : Fin 3) (k : Fin 17) : ℝ :=
  splitPotential parents data s (phi.symm i) k.val

end MatrixMultiplication.AllFieldActiveGibbs

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_TerminalStatisticLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldTerminalStatisticLaws

open AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev AZero (K : ℕ) :=
  {h : AfterA K // aShape h ∉ positiveSecond} × Placement

abbrev BZero (K : ℕ) :=
  {h : AfterB K // positive (bShape h) ≠ true} × Placement

abbrev TerminalZero (K : ℕ) := AZero K ⊕ BZero K

variable {K : ℕ}

def bParent (h : BZero K) : Shape := aShape h.1.val.1.val

theorem bParent_mem_positiveSecond (h : BZero K) : bParent h ∈ positiveSecond :=
  h.1.val.1.property

theorem bShape_mem_below (h : BZero K) : bShape h.1.val ∈ below (bParent h) :=
  bShape_mem h.1.val

end MatrixMultiplication.AllFieldTerminalStatisticLaws

end
end

end MatrixAllFields

end OAI
end


