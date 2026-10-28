-- Prove2me | Definitions.Def_OAIB3Kr012
-- name    : OAIB3Kr012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T17:03:25.726276+00:00
-- url     : https://prove2.me/theorems/b9905210-7c56-4235-a417-f5b046b0d440
-- title:
--   Definitions bundle OAIB3Kr012 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 148 declarations of OpenAI's Lean: 40 definitions, 2 inductive types or structures, 8 instances and 98 theorems. The definitions and types are `OAI.KirchbergRordam.GenericRW.FlipPath.e`, `OAI.KirchbergRordam.GenericRW.FullRankWeighted.Row`, `OAI.KirchbergRordam.GenericRW.FullRankWeighted.instPartialOrderCarrierPowerPack`, `OAI.KirchbergRordam.GenericRW.FullRankWeighted.reindex`, `OAI.KirchbergRordam.GenericRW.HereditaryTransport.leftLinear`, `OAI.KirchbergRordam.GenericRW.IntervalCalculus.hom`, `OAI.KirchbergRordam.GenericRW.IntervalCalculus.spectralPoint`, `OAI.KirchbergRordam.GenericRW.MaxTensor.instPartialOrderCarrierPowerPack`, `OAI.KirchbergRordam.GenericRW.OrderZero.Pair`, `OAI.KirchbergRordam.GenericRW.OrderZero.Pair.eval`, `OAI.KirchbergRordam.GenericRW.OrderZero.Pair.field`, `OAI.KirchbergRordam.GenericRW.OrderZero.Pair.weight`, `OAI.KirchbergRordam.GenericRW.OrderZero.WeightedUnits.cutoffRescale`, `OAI.KirchbergRordam.GenericRW.OrderZero.WeightedUnits.map`, `OAI.KirchbergRordam.GenericRW.OrderZero.WeightedUnits.rescale`, `OAI.KirchbergRordam.GenericRW.OrderZero.WeightedUnits.toWeightedMatrix`, `OAI.KirchbergRordam.GenericRW.OrderZero.gram`, `OAI.KirchbergRordam.GenericRW.Spatial.left`, `OAI.KirchbergRordam.GenericRW.Spatial.right`, `OAI.KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix`, `OAI.KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix.ConeMatrix`, `OAI.KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix.coeff`, `OAI.KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix.coeffAux`, `OAI.KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix.eval`, `OAI.KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix.matrixCoeffs`, `OAI.KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix.matrixHom`, `OAI.KirchbergRordam.GenericRW.TripleTensor.Algebra`, `OAI.KirchbergRordam.GenericRW.TripleTensor.first`, `OAI.KirchbergRordam.GenericRW.TripleTensor.second`, `OAI.KirchbergRordam.GenericRW.TripleTensor.third`, `OAI.KirchbergRordam.MatrixTensor.kroneckerInverse`, `OAI.KirchbergRordam.MatrixTensor.kroneckerRaw`, `OAI.KirchbergRordam.MatrixTensor.unit`, `OAI.KirchbergRordam.MultiplicativeChannel.centralize`, `OAI.KirchbergRordam.MultiplicativeChannel.normalized`, `OAI.KirchbergRordam.MultiplicativeChannel.postcompose`, `OAI.KirchbergRordam.MultiplicativeChannel.sequence`, `OAI.KirchbergRordam.NormUltrapower.map`, `OAI.KirchbergRordam.NormUltrapower.sequenceMap`, `OAI.KirchbergRordam.PrimeDimensionDrop.scalar` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CharacterCriterion_BalancedChannels`, `CharacterCriterion_BalancedLimit`, `CharacterCriterion_ConeModel`, `CharacterCriterion_FieldCalculus`, `CharacterCriterion_FiniteDrop`, `CharacterCriterion_FlipPath`, `CharacterCriterion_FullComparison`, `CharacterCriterion_FunctionalCalculus`, `CharacterCriterion_HereditaryTransport`, `CharacterCriterion_InductiveLimit`, `CharacterCriterion_MaxTensor`, `CharacterCriterion_MinTensor`, `CharacterCriterion_MultiplicativeChannels`, `CharacterCriterion_OrderZero`, `CharacterCriterion_OrderZeroPair`, `CharacterCriterion_PrimePresentation`, `CharacterCriterion_PrimeSpectrum`, `CharacterCriterion_RepresentedLabels`, `CharacterCriterion_SeparableReduction`, `CharacterCriterion_SpatialTensor`, `CharacterCriterion_SquareZeroCone`, `CharacterCriterion_UltrapowerSaturation`, `CharacterCriterion_WeightedUnits`.
--
--   **Imports.** It imports the published bundle `Def_CharacterCriterion`; the bundles `OAIB3Kr004`, `OAIB3Kr007`, `OAIB3Kr008` and `OAIB3Kr009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIB3Kr013` and `OAIB3Kr014`; the statements `OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage`, `OAI.KirchbergRordam.PrimeDropPresentation.central_no_character` and `OAI.KirchbergRordam.quotient_isomorphism_of_ultrapower_split_and_conjugacy`; the proofs of `OAI.KirchbergRordam.MatrixTensor.representation_bound`, `OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound` and `OAI.KirchbergRordam.quotient_isomorphism_of_ultrapower_split_and_conjugacy`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr004
import Definitions.Def_OAIB3Kr007
import Definitions.Def_OAIB3Kr008
import Definitions.Def_OAIB3Kr009

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MaxTensor
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.DetectingSpace.quotientNormedRing _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.MaxTensor.instCStarRingAlgebra _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped TensorProduct

namespace KirchbergRordam.GenericRW
namespace StarCompletion

open UniformSpace
variable (R : Type*) [SeminormedRing R] [StarRing R] [NormedStarGroup R]

instance completionNormedStarGroup : NormedStarGroup (Completion R) where
  norm_star_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simp only [star_coe, Completion.norm_coe, norm_star, le_refl]

end StarCompletion

namespace MaxTensor


open scoped CStarAlgebra


universe u


attribute [instance] CStarPack.inst

end MaxTensor
end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_RepresentedLabels
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PureStates.locallyConvexReal _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology


namespace KirchbergRordam.GenericRW.TripleTensor
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor
abbrev Algebra (A B C : Type*) [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C] :=
  MaxTensor.Algebra A (MaxTensor.Algebra B C)
def first : A →⋆ₐ[ℂ] Algebra A B C := includeLeft
def second : B →⋆ₐ[ℂ] Algebra A B C := includeRight.comp includeLeft
def third : C →⋆ₐ[ℂ] Algebra A B C := includeRight.comp includeRight
end KirchbergRordam.GenericRW.TripleTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SpatialTensor
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace


open scoped TensorProduct InnerProductSpace
open UniformSpace
namespace KirchbergRordam.GenericRW.Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable [CompleteSpace H] [CompleteSpace K]

lemma map_inner_algebraic (T : H →L[ℂ] H) (S : K →L[ℂ] K)
    (x y : H ⊗[ℂ] K) :
    ⟪TensorProduct.mapL (star T) (star S) x, y⟫_ℂ =
      ⟪x, TensorProduct.mapL T S y⟫_ℂ := by
  induction x using OAI.tensorInductionOn with
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
  | tmul a b =>
    induction y using OAI.tensorInductionOn with
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
    | tmul c d =>
      simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

lemma map_inner (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x y : Hilbert H K) :
    ⟪map (star T) (star S) x, y⟫_ℂ = ⟪x, map T S y⟫_ℂ := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y => simpa using map_inner_algebraic T S x y

lemma map_star (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (star T) (star S) = star (map T S) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [map_inner, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]


def left : (H →L[ℂ] H) →⋆ₐ[ℂ] (Hilbert H K →L[ℂ] Hilbert H K) where
  toFun T := map T 1
  map_zero' := by ext x; simp [map]
  map_one' := map_one
  map_add' T U := map_add_left T U 1
  map_mul' T U := by simpa using map_mul T U (1 : K →L[ℂ] K) 1
  commutes' z := by
    change map (z • 1) 1 = z • 1
    rw [map_smul_left, map_one]
  map_star' T := by simpa using map_star T (1 : K →L[ℂ] K)

def right : (K →L[ℂ] K) →⋆ₐ[ℂ] (Hilbert H K →L[ℂ] Hilbert H K) where
  toFun S := map 1 S
  map_zero' := by ext x; simp [map]
  map_one' := map_one
  map_add' T U := map_add_right 1 T U
  map_mul' T U := by simpa using map_mul (1 : H →L[ℂ] H) 1 T U
  commutes' z := by
    change map 1 (z • 1) = z • 1
    rw [map_smul_right, map_one]
  map_star' S := by simpa using map_star (1 : H →L[ℂ] H) S

end KirchbergRordam.GenericRW.Spatial

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SquareZeroCone
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.ConeModel.coneClosed _root_.OAI.KirchbergRordam.GenericRW.ConeModel.coneSubringClass _root_.OAI.KirchbergRordam.GenericRW.ConeModel.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone _root_.OAI.KirchbergRordam.GenericRW.ConeModel.instFiniteDimensionalComplexM2 _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace


variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

namespace KirchbergRordam.GenericRW
namespace Intertwining
variable {A : Type*} [CStarAlgebra A]


omit instSize in
lemma cfc.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {v a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (h : v * a = b * v) (f : ℝ → ℝ) (hf : Continuous f) :
    v * cfc f a = cfc f b * v := by
  let : ContinuousFunctionalCalculus ℝ (A × A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hm : (a, b) ∈ algebra v := by
    refine ⟨h, ?_⟩
    simpa only [star_mul, ha.star_eq, hb.star_eq] using (congrArg star h).symm
  have hh := cfc_mem (p := IsSelfAdjoint) (s := algebra v) f hm
  rw [cfc_map_prod (S := ℂ) (pab := IsSelfAdjoint) f a b (hf.continuousOn)
    (show IsSelfAdjoint (a, b) from Prod.ext ha hb) ha hb] at hh
  exact hh.1

variable [PartialOrder A] [StarOrderedRing A]
lemma sqrt {v a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : v * a = b * v) :
    v * CFC.sqrt a = CFC.sqrt b * v := by
  rw [CFC.sqrt_eq_real_sqrt a ha, CFC.sqrt_eq_real_sqrt b hb,
    cfcₙ_eq_cfc (f := Real.sqrt) (a := a) (hf0 := Real.sqrt_zero),
    cfcₙ_eq_cfc (f := Real.sqrt) (a := b) (hf0 := Real.sqrt_zero)]
  exact cfc (IsSelfAdjoint.of_nonneg ha) (IsSelfAdjoint.of_nonneg hb) h _ Real.continuous_sqrt

lemma mul_sqrt_eq_zero {v a : A} (ha : 0 ≤ a) (h : v * a = 0) :
    v * CFC.sqrt a = 0 := by
  simpa only [CFC.sqrt_zero, zero_mul] using sqrt ha (le_refl (0 : A)) (v := v) (by simpa)

lemma sqrt_mul_eq_zero {v a : A} (ha : 0 ≤ a) (h : a * v = 0) :
    CFC.sqrt a * v = 0 := by
  have hh : star v * a = 0 := by
    simpa only [star_mul, IsSelfAdjoint.of_nonneg ha |>.star_eq, star_zero] using congrArg star h
  have he := congrArg star (mul_sqrt_eq_zero ha hh)
  simpa only [star_mul, IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a) |>.star_eq,
    star_star, star_zero] using he
end Intertwining

namespace SquareZeroCone
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


structure WeightedMatrix (A : Type*) [CStarAlgebra A] [PartialOrder A] where
  h : A
  x : Fin rankNum → Fin rankNum → A
  h_nonneg : 0 ≤ h
  norm_h_le : ‖h‖ ≤ 1
  star_x : ∀ i j, star (x i j) = x j i
  mul_x : ∀ i j k l, x i j * x k l = if j = k then h * x i l else 0
  diagonal : ∑ i, x i i = h

namespace WeightedMatrix
variable (W : WeightedMatrix A)
omit [StarOrderedRing A] in
lemma commute_h (i j : Fin rankNum) : Commute (W.x i j) W.h := by
  change W.x i j * W.h = W.h * W.x i j
  conv_lhs => rw [← W.diagonal, Finset.mul_sum]
  simp only [W.mul_x]
  simp

lemma column_sum (i : Fin rankNum) : ∑ j, star (W.x i j) * W.x i j = star W.h * W.h := by
  simp only [W.star_x, W.mul_x, ite_true, ← Finset.mul_sum, W.diagonal,
    (IsSelfAdjoint.of_nonneg W.h_nonneg).star_eq]

lemma norm_mul_le (i j : Fin rankNum) (z : A) : ‖W.x i j * z‖ ≤ ‖W.h * z‖ := by
  have he : ∑ k, star (W.x i k * z) * (W.x i k * z) = star (W.h * z) * (W.h * z) := by
    simp only [star_mul]
    calc
      _ = star z * (∑ k, star (W.x i k) * W.x i k) * z := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        noncomm_ring
      _ = _ := by rw [W.column_sum]; noncomm_ring
  have hl : star (W.x i j * z) * (W.x i j * z) ≤ star (W.h * z) * (W.h * z) := by
    rw [← he]
    exact Finset.single_le_sum (fun k _ => star_mul_self_nonneg (W.x i k * z)) (Finset.mem_univ j)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hl (star_mul_self_nonneg _)
  simp only [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (W.x i j * z), norm_nonneg (W.h * z)]

end WeightedMatrix

end SquareZeroCone

namespace IntervalCalculus
open scoped ComplexOrder


variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

omit instSize in
lemma spectrum_mem_interval.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [Nontrivial A]
    [PartialOrder A]
    [StarOrderedRing A]
    {h : A} (hh : 0 ≤ h) (hn : ‖h‖ ≤ 1)
    {z : ℂ} (hz : z ∈ spectrum ℂ h) : z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 := by
  obtain ⟨r, hr, rfl⟩ := (IsSelfAdjoint.of_nonneg hh).spectrumRestricts.algebraMap_image ▸ hz
  have hr0 := spectrum_nonneg_of_nonneg hh hr
  have hr1 := spectrum.norm_le_norm_of_mem hr
  change 0 = 0 ∧ 0 ≤ r ∧ r ≤ 1
  exact ⟨rfl, hr0, (le_abs_self r).trans (hr1.trans hn)⟩


def spectralPoint {h : A} (hh : 0 ≤ h) (hn : ‖h‖ ≤ 1) : C(spectrum ℂ h, unitInterval) :=
  ⟨fun z => ⟨z.1.re, (spectrum_mem_interval hh hn z.2).2⟩, by fun_prop⟩

def hom {h : A} (hh : 0 ≤ h) (hn : ‖h‖ ≤ 1) : C(unitInterval, ℂ) →⋆ₐ[ℂ] A :=
  (cfcHom (IsSelfAdjoint.of_nonneg hh).isStarNormal).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ (spectralPoint hh hn))

lemma hom_coord {h : A} (hh : 0 ≤ h) (hn : ‖h‖ ≤ 1) : hom hh hn coord = h := by
  change cfcHom (IsSelfAdjoint.of_nonneg hh).isStarNormal
    (coord.comp (spectralPoint hh hn)) = h
  have he : coord.comp (spectralPoint hh hn) = (ContinuousMap.restrict (spectrum ℂ h) (ContinuousMap.id ℂ)) := by
    ext z
    apply Complex.ext
    · rfl
    · exact (spectrum_mem_interval hh hn z.property).1.symm
  rw [he, cfcHom_id]

lemma norm_hom_le {h : A} (hh : 0 ≤ h) (hn : ‖h‖ ≤ 1) (f : C(unitInterval, ℂ)) :
    ‖hom hh hn f‖ ≤ ‖f‖ := NonUnitalStarAlgHom.norm_apply_le (hom hh hn) f

end IntervalCalculus
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.IntervalCalculus
open scoped ContinuousMapZero

omit instSize in
lemma coordMul_dense
    [KirchbergRordam.GenericRW.Size]
    : DenseRange coordMul := by
  let I : Ideal C(unitInterval, ℂ) := Ideal.span {coord}
  have hs : ContinuousMap.setOfIdeal I = ({0} : Set unitInterval)ᶜ := by
    ext t
    rw [ContinuousMap.mem_setOfIdeal]
    constructor
    · rintro ⟨f, hf, hne⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro ht
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      apply hne
      simp [ht, coord]
    · intro ht
      refine ⟨coord, Ideal.subset_span (Set.mem_singleton _), ?_⟩
      intro he
      apply ht
      apply Subtype.ext
      change ((t : ℝ) : ℂ) = 0 at he
      exact_mod_cast he
  have hi : (fun f : C(unitInterval, ℂ)₀ => f.toContinuousMap) '' Set.range coordMul = I := by
    ext f
    constructor
    · rintro ⟨g, ⟨v, rfl⟩, rfl⟩
      exact Ideal.mul_mem_right _ I (Ideal.subset_span (Set.mem_singleton _))
    · intro hf
      obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hf
      refine ⟨coordMul g, ⟨g, rfl⟩, ?_⟩
      change coord * g = f
      rw [mul_comm, hg]
  apply (ContinuousMapZero.isometry_toContinuousMap.isEmbedding.isInducing.dense_iff).mpr
  intro f
  rw [hi, ← Ideal.coe_closure, ← ContinuousMap.idealOfSet_ofIdeal_eq_closure, hs]
  intro t ht
  have ht0 : t = 0 := by simpa only [compl_compl, Set.mem_singleton_iff] using ht
  rw [ht0]
  exact map_zero f

end KirchbergRordam.GenericRW.IntervalCalculus

namespace KirchbergRordam.GenericRW
namespace SquareZeroCone
namespace WeightedMatrix
open scoped ContinuousMapZero
open IntervalCalculus
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedMatrix A)

abbrev eval : C(unitInterval, ℂ) →⋆ₐ[ℂ] A := hom W.h_nonneg W.norm_h_le

lemma commute_eval (i j : Fin rankNum) (f : C(unitInterval, ℂ)) : Commute (W.x i j) (W.eval f) := by
  exact ((IsSelfAdjoint.of_nonneg W.h_nonneg).commute_cfcHom
    (IsSelfAdjoint.of_nonneg W.h_nonneg).isStarNormal (W.commute_h i j).symm _).symm

def coeffAux (i j : Fin rankNum) : C(unitInterval, ℂ) →ₗ[ℂ] A where
  toFun f := W.x i j * W.eval f
  map_add' f g := by simp [mul_add]
  map_smul' c f := by simp

lemma coeffAux_bound (i j : Fin rankNum) (f : C(unitInterval, ℂ)) :
    ‖W.coeffAux i j f‖ ≤ ‖coordMul f‖ := by
  change ‖W.x i j * W.eval f‖ ≤ ‖coord * f‖
  calc
    _ ≤ ‖W.h * W.eval f‖ := W.norm_mul_le i j _
    _ = ‖W.eval (coord * f)‖ := by rw [map_mul, hom_coord]
    _ ≤ ‖coord * f‖ := norm_hom_le _ _ _


def coeff (i j : Fin rankNum) : C(unitInterval, ℂ)₀ →L[ℂ] A :=
  (W.coeffAux i j).extendOfNorm coordMul

lemma coeff_coordMul (i j : Fin rankNum) (f : C(unitInterval, ℂ)) :
    W.coeff i j (coordMul f) = W.x i j * W.eval f := by
  exact LinearMap.extendOfNorm_eq coordMul_dense
    ⟨1, fun f => by simpa using W.coeffAux_bound i j f⟩ f

omit instSize in
lemma coordMul_star
    [KirchbergRordam.GenericRW.Size]
    (f : C(unitInterval, ℂ)) : star (coordMul f) = coordMul (star f) := by
  ext t
  simp [coordMul_apply]

omit instSize in
lemma coordMul_mul
    [KirchbergRordam.GenericRW.Size]
    (f g : C(unitInterval, ℂ)) :
    coordMul f * coordMul g = coordMul (coord * f * g) := by
  ext t
  change (coord t * f t) * (coord t * g t) = coord t * (coord t * f t * g t)
  ring

lemma star_coeff (i j : Fin rankNum) (f : C(unitInterval, ℂ)₀) :
    star (W.coeff i j f) = W.coeff j i (star f) := by
  refine coordMul_dense.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [coordMul_star, W.coeff_coordMul, W.coeff_coordMul, star_mul, W.star_x, map_star]
  simpa only [map_star] using (W.commute_eval j i (star g)).symm.eq

lemma mul_coeff (i j k l : Fin rankNum) (f g : C(unitInterval, ℂ)₀) :
    W.coeff i j f * W.coeff k l g = if j = k then W.coeff i l (f * g) else 0 := by
  classical
  refine coordMul_dense.induction_on₂ (p := fun f g =>
    W.coeff i j f * W.coeff k l g = if j = k then W.coeff i l (f * g) else 0)
    (isClosed_eq (by fun_prop) (by by_cases hjk : j = k <;> simp only [hjk, ↓reduceIte] <;> fun_prop)) ?_ f g
  intro f g
  rw [coordMul_mul, W.coeff_coordMul, W.coeff_coordMul, W.coeff_coordMul]
  have he : W.x i j * W.eval f * (W.x k l * W.eval g) =
      (W.x i j * W.x k l) * (W.eval f * W.eval g) := by
    rw [mul_assoc (W.x i j), ← mul_assoc (W.eval f), (W.commute_eval k l f).symm.eq]
    noncomm_ring
  rw [he, W.mul_x]
  split_ifs with hjk
  · rw [map_mul, map_mul, hom_coord]
    have hc := W.commute_h i l
    rw [← hc.eq]
    noncomm_ring
  · simp
end WeightedMatrix
end SquareZeroCone
end KirchbergRordam.GenericRW
namespace KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix
open scoped ContinuousMapZero BigOperators
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedMatrix A)

abbrev ConeMatrix := Matrix (Fin rankNum) (Fin rankNum) C(unitInterval, ℂ)₀

def matrixCoeffs (m : ConeMatrix) : A := ∑ i, ∑ j, W.coeff i j (m i j)

lemma matrixCoeffs_add (m n : ConeMatrix) :
    W.matrixCoeffs (m + n) = W.matrixCoeffs m + W.matrixCoeffs n := by
  simp [matrixCoeffs, map_add, Finset.sum_add_distrib]

lemma matrixCoeffs_smul (c : ℂ) (m : ConeMatrix) :
    W.matrixCoeffs (c • m) = c • W.matrixCoeffs m := by
  simp [matrixCoeffs, map_smul, Finset.smul_sum]

lemma matrixCoeffs_single (i j : Fin rankNum) (f : C(unitInterval, ℂ)₀) :
    W.matrixCoeffs (Matrix.single i j f) = W.coeff i j f := by
  simp [matrixCoeffs, Matrix.single, ite_and, apply_ite]

lemma matrixCoeffs_zero : W.matrixCoeffs 0 = 0 := by simp [matrixCoeffs]

lemma matrixCoeffs_mul (m n : ConeMatrix) :
    W.matrixCoeffs (m * n) = W.matrixCoeffs m * W.matrixCoeffs n := by
  induction m using Matrix.induction_on' with
  | h_zero => simp [W.matrixCoeffs_zero]
  | h_add m m' hm hm' => simp only [add_mul, W.matrixCoeffs_add, hm, hm']
  | h_std_basis i j f =>
    induction n using Matrix.induction_on' with
    | h_zero => simp [W.matrixCoeffs_zero]
    | h_add n n' hn hn' => simp only [mul_add, W.matrixCoeffs_add, hn, hn']
    | h_std_basis k l g =>
      by_cases h : j = k
      · subst k
        rw [Matrix.single_mul_single_same, W.matrixCoeffs_single,
          W.matrixCoeffs_single, W.matrixCoeffs_single, W.mul_coeff, ite_eq_left rfl]
      · rw [Matrix.single_mul_single_of_ne (h := h), W.matrixCoeffs_single,
          W.matrixCoeffs_single, W.mul_coeff, ite_eq_right h, W.matrixCoeffs_zero]

lemma matrixCoeffs_star (m : ConeMatrix) : W.matrixCoeffs (star m) = star (W.matrixCoeffs m) := by
  simp only [matrixCoeffs, star_sum, W.star_coeff]
  exact Finset.sum_comm


def matrixHom : ConeMatrix →⋆ₙₐ[ℂ] A where
  toFun := W.matrixCoeffs
  map_zero' := by simp [matrixCoeffs]
  map_add' := W.matrixCoeffs_add
  map_smul' := W.matrixCoeffs_smul
  map_mul' := W.matrixCoeffs_mul
  map_star' := W.matrixCoeffs_star

end KirchbergRordam.GenericRW.SquareZeroCone.WeightedMatrix
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_HereditaryTransport
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.ConeModel.coneSubringClass _root_.OAI.KirchbergRordam.GenericRW.ConeModel.instCStarAlgebraSubtypeContinuousMapElemRealUnitIntervalM2MemStarSubalgebraComplexCone _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW

open scoped ContinuousMapZero BigOperators ComplexOrder

namespace SquareZeroCone.WeightedMatrix
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedMatrix A)

lemma matrixHom_single (i j : Fin rankNum) (f : C(unitInterval, ℂ)₀) :
    W.matrixHom (Matrix.single i j f) = W.coeff i j f := by
  change (∑ k, ∑ l, W.coeff k l (Matrix.single i j f k l)) = _
  simp [Matrix.single, ite_and, apply_ite]

end SquareZeroCone.WeightedMatrix
end KirchbergRordam.GenericRW


namespace KirchbergRordam.GenericRW.HereditaryTransport
open ClosedRightRange
variable {A : Type*} [CStarAlgebra A]


variable {a v : A} (ha : IsSelfAdjoint a) (hv : star a*a=star v*v)


lemma continuous_left : Continuous (left (v := v) ha) := by
  exact (transport a v).continuous.comp (continuous_subtype_val.subtype_mk _)

end KirchbergRordam.GenericRW.HereditaryTransport

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_ConeModel
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]

namespace KirchbergRordam.GenericRW.IntervalCalculus
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]


omit instSize in
lemma ext_coord.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (φ ψ : C(unitInterval,ℂ) →⋆ₐ[ℂ] A) (h : φ coord=ψ coord) : φ=ψ := by
  let S : StarSubalgebra ℂ C(unitInterval,ℂ) := StarAlgHom.equalizer φ ψ
  have hc : IsClosed (S : Set C(unitInterval,ℂ)) := isClosed_eq (map_continuous φ) (map_continuous ψ)
  have hs : S.SeparatesPoints := by
    intro x y hxy
    refine ⟨coord,⟨coord,h,rfl⟩,?_⟩
    intro he
    apply hxy
    apply Subtype.ext
    change ((x:ℝ):ℂ)=((y:ℝ):ℂ) at he
    exact_mod_cast he
  have ht : S=⊤ := by
    rw [← le_antisymm (StarSubalgebra.topologicalClosure_minimal le_rfl hc) S.le_topologicalClosure]
    exact ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hs
  apply StarAlgHom.ext
  intro f
  exact show f∈S from ht ▸ trivial
end KirchbergRordam.GenericRW.IntervalCalculus

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FlipPath
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]

namespace KirchbergRordam.GenericRW.RWFunctions

omit instSize in
lemma g_nonneg
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : 0≤realG t := le_min (by norm_num) (mul_nonneg (by norm_num) (sub_nonneg.mpr t.property.2))
omit instSize in
lemma g_le_one
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : realG t≤1 := min_le_left _ _

omit instSize in
lemma g_low
    [KirchbergRordam.GenericRW.Size]
    {t : unitInterval} (ht : (t:ℝ)≤2/3) : g t=1 := by
  have h : realG t=1 := min_eq_left (by linarith)
  simp [g,h]

lemma g_norm : ‖g‖≤1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  change ‖(realG t : ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (g_nonneg t)]
  exact g_le_one t

omit instSize in
lemma q_star
    [KirchbergRordam.GenericRW.Size]
    : star q=q := by ext t; exact Complex.conj_ofReal _
omit instSize in
lemma j_star
    [KirchbergRordam.GenericRW.Size]
    : star j=j := by ext t; exact Complex.conj_ofReal _
lemma q_sq : q*q=g := by
  ext t
  change ((Real.sqrt (realG t):ℝ):ℂ)*((Real.sqrt (realG t):ℝ):ℂ)=(realG t:ℂ)
  rw [← Complex.ofReal_mul,Real.mul_self_sqrt (g_nonneg t)]


lemma residual_inverse (t : unitInterval) :
    (1-g t)*j t*((t:ℝ):ℂ)=1-g t := by
  by_cases ht : (t:ℝ)≤2/3
  · rw [g_low ht]; simp
  · have hp : (0:ℝ)<t := lt_trans (by norm_num) (lt_of_not_ge ht)
    have he : realJ t=(t:ℝ)⁻¹ := max_eq_left (le_of_lt (lt_of_not_ge ht)) ▸ rfl
    change (1-g t)*(realJ t : ℂ)*((t:ℝ):ℂ)=_
    rw [he,mul_assoc,← Complex.ofReal_mul,inv_mul_cancel₀ (ne_of_gt hp),Complex.ofReal_one,mul_one]


end KirchbergRordam.GenericRW.RWFunctions
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_OrderZero
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW.OrderZero
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


namespace WeightedUnits
variable (W : WeightedUnits ι A)
omit [StarOrderedRing A] in
omit instSize in
lemma commute_h.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    (W : KirchbergRordam.GenericRW.OrderZero.WeightedUnits ι A)
    (i j : ι) : Commute (W.x i j) W.h := by
  change W.x i j * W.h = W.h * W.x i j
  conv_lhs => rw [← W.diagonal, Finset.mul_sum]
  simp only [W.mul_x]
  simp

omit instSize in
lemma column_sum.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    (W : KirchbergRordam.GenericRW.OrderZero.WeightedUnits ι A)
    (i : ι) : ∑ j, star (W.x i j) * W.x i j = star W.h * W.h := by
  simp only [W.star_x, W.mul_x, ite_true, ← Finset.mul_sum, W.diagonal,
    (IsSelfAdjoint.of_nonneg W.nonneg).star_eq]

lemma norm_mul_le (i j : ι) (z : A) : ‖W.x i j * z‖ ≤ ‖W.h * z‖ := by
  have he : ∑ k, star (W.x i k * z) * (W.x i k * z) = star (W.h * z) * (W.h * z) := by
    simp only [star_mul]
    calc
      _ = star z * (∑ k, star (W.x i k) * W.x i k) * z := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        noncomm_ring
      _ = _ := by rw [W.column_sum]; noncomm_ring
  have hl : star (W.x i j * z) * (W.x i j * z) ≤ star (W.h * z) * (W.h * z) := by
    rw [← he]
    exact Finset.single_le_sum (fun k _ => star_mul_self_nonneg (W.x i k * z)) (Finset.mem_univ j)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hl (star_mul_self_nonneg _)
  simp only [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (W.x i j * z), norm_nonneg (W.h * z)]


omit [StarOrderedRing A] in
omit instSize in
lemma linear_one.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    (W : KirchbergRordam.GenericRW.OrderZero.WeightedUnits ι A)
    : W.linear 1 = W.h := by
  simpa [linear, Matrix.one_apply] using W.diagonal

omit [StarOrderedRing A] in
omit instSize in
lemma linear_star.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    (W : KirchbergRordam.GenericRW.OrderZero.WeightedUnits ι A)
    (m : Matrix ι ι ℂ) : W.linear (star m) = star (W.linear m) := by
  simp only [linear, LinearMap.coe_mk, AddHom.coe_mk, star_sum, star_smul, W.star_x]
  exact Finset.sum_comm

omit [StarOrderedRing A] in
lemma linear_mul (m n : Matrix ι ι ℂ) :
    W.linear m * W.linear n = W.h * W.linear (m*n) := by
  induction m using Matrix.induction_on' with
  | h_zero => simp
  | h_add m m' hm hm' => simp only [add_mul,map_add,mul_add,hm,hm']
  | h_std_basis i j z =>
    induction n using Matrix.induction_on' with
    | h_zero => simp
    | h_add n n' hn hn' => simp only [mul_add,map_add,hn,hn']
    | h_std_basis k l w =>
      by_cases hjk : j=k
      · subst k
        rw [Matrix.single_mul_single_same,W.linear_single,W.linear_single,W.linear_single]
        simp [smul_smul,W.mul_x,mul_comm]
      · rw [Matrix.single_mul_single_of_ne (h := hjk)]
        simp [hjk,W.mul_x]

end WeightedUnits
end KirchbergRordam.GenericRW.OrderZero

namespace KirchbergRordam.GenericRW.HereditaryTransport
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)

omit [Fintype ι] in
omit hs in
omit instSize in
lemma copy_norm.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {ι : Type contextLevel2}
    [DecidableEq ι]
    {a : A}
    (s : ι → A)
    (hs : ∀ (i j : ι), Star.star (s i) * s j = if i = j then Star.star a * a else 0)
    (i : ι) : star a*a=star (s i)*s i := by rw [hs]; simp

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.HereditaryTransport
open ClosedRightRange
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [DecidableEq ι]
variable {a : A} (ha : IsSelfAdjoint a) (s : ι → A)
variable (hs : ∀ i j, star (s i)*s j=if i=j then star a*a else 0)


def leftLinear (i : ι) : corner a ha →ₗ[ℂ] A where
  toFun := left (v := s i) ha
  map_add' x y := by
    change transport a (s i) ((⟨(x:A),in_space x.property⟩ : space a)+(⟨(y:A),in_space y.property⟩ : space a)) = transport a (s i) _ + transport a (s i) _
    exact map_add (transport a (s i)) _ _
  map_smul' c x := by
    change transport a (s i) (c • (⟨(x:A),in_space x.property⟩ : space a)) = c • transport a (s i) _
    exact map_smul (transport a (s i)) c _

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.HereditaryTransport
section
variable {A : Type*} [CStarAlgebra A] {a v : A}
variable (ha : IsSelfAdjoint a) (hv : star a*a=star v*v)
include hv in
lemma left_mul_of_eq (x z : corner a ha) (y : A) (he : (z:A)=(x:A)*y) :
    left (v := v) ha z=left (v := v) ha x*y := by
  unfold left
  rw [show (⟨(z:A),in_space z.property⟩ : ClosedRightRange.space a)=
    ⟨(x:A)*y,ClosedRightRange.mul_right_mem (in_space x.property) y⟩ from Subtype.ext he]
  exact ClosedRightRange.transport_right hv ⟨(x:A),in_space x.property⟩ y
end

open scoped BigOperators

end KirchbergRordam.GenericRW.HereditaryTransport

namespace KirchbergRordam.GenericRW.OrderZero
open scoped BigOperators ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def gram (s : ι → A) (h : A)
    (hs : ∀ i j, s i*star (s j)=if i=j then h else 0)
    (hn : ‖∑ i,star (s i)*s i‖ ≤ 1) : WeightedUnits ι A where
  h := ∑ i,star (s i)*s i
  x i j := star (s i)*s j
  nonneg := Finset.sum_nonneg fun i _ => star_mul_self_nonneg (s i)
  norm_le := hn
  star_x i j := by simp only [star_mul,star_star]
  mul_x i j k l := by
    have hd : (∑ r,star (s r)*s r)*(star (s i)*s l)=star (s i)*h*s l := by
      rw [Finset.sum_mul]
      calc
        _=∑ r,star (s r)*(s r*star (s i))*s l := by apply Finset.sum_congr rfl; intro r _; noncomm_ring
        _=star (s i)*h*s l := by simp [hs]
    rw [hd]
    calc
      _=star (s i)*(s j*star (s k))*s l := by noncomm_ring
      _=_ := by by_cases hjk : j=k <;> simp [hs,hjk]
  diagonal := rfl

namespace WeightedUnits

def toWeightedMatrix (W : WeightedUnits (Fin rankNum) A) : SquareZeroCone.WeightedMatrix A where
  h := W.h
  x := W.x
  h_nonneg := W.nonneg
  norm_h_le := W.norm_le
  star_x := W.star_x
  mul_x := W.mul_x
  diagonal := W.diagonal

end WeightedUnits
end KirchbergRordam.GenericRW.OrderZero

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_WeightedUnits
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A) {v : A}
variable (hv : star v*v=1-W.h)

omit [StarOrderedRing A] in
lemma commute_defect (i j : Fin rankNum) : Commute (W.x i j) (1-W.h) :=
  (Commute.one_right _).sub_right (W.commute_h i j)

include hv in
lemma defect_nonneg : 0≤1-W.h := hv ▸ star_mul_self_nonneg v

lemma defect_selfAdjoint : IsSelfAdjoint (1-W.h) :=
  (IsSelfAdjoint.one A).sub (IsSelfAdjoint.of_nonneg W.nonneg)


end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A] [PartialOrder A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rescale (W : WeightedUnits ι A) (r l : A) (hr : IsSelfAdjoint r)
    (hc : ∀ i j,Commute r (W.x i j)) (he : r*W.h=l)
    (hp : 0≤l) (hn : ‖l‖≤1) : WeightedUnits ι A where
  h := l
  x i j := r*W.x i j
  nonneg := hp
  norm_le := hn
  star_x i j := by rw [star_mul,W.star_x,hr.star_eq,(hc j i).eq]
  mul_x i j k n := by
    calc
      _=r*r*(W.x i j*W.x k n) := by rw [mul_assoc,← mul_assoc (W.x i j),← (hc i j).eq]; noncomm_ring
      _=if j=k then l*(r*W.x i n) else 0 := by
        rw [W.mul_x]
        split_ifs
        · have ch : Commute r W.h := by
            rw [← W.diagonal]; exact Commute.sum_right Finset.univ (fun t => W.x t t) r fun t _ => hc t t
          rw [← he]
          calc
            _=r*(r*W.h)*W.x i n := by noncomm_ring
            _=r*(W.h*r)*W.x i n := by rw [ch.eq]
            _=_ := by noncomm_ring
        · simp
  diagonal := by rw [← Finset.mul_sum,W.diagonal,he]

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.FlipPath
open ConeModel RWFunctions
open scoped BigOperators

def e (i j : Fin rankNum) : ConeModel.M2 := CStarMatrix.ofMatrix (Matrix.single i j 1)

lemma e_star (i j : Fin rankNum) : star (e i j)=e j i := by
  ext a b
  simp [e,CStarMatrix.star_apply,Matrix.single,and_comm]

lemma e_mul (i r j k : Fin rankNum) : e i r*e j k=if r=j then e i k else 0 := by
  change CStarMatrix.ofMatrix (Matrix.single i r 1 * Matrix.single j k 1)=_
  by_cases hrj : r=j
  · subst j; simp [Matrix.single_mul_single_same,e]
  · rw [Matrix.single_mul_single_of_ne 1 i r j hrj 1,ite_eq_right hrj]; rfl

lemma scalar_weight (z : ℂ) (x : ConeModel.M2) :
    algebraMap ℂ ConeModel.M2 z*x-algebraMap ℂ ConeModel.M2 z*(algebraMap ℂ ConeModel.M2 z*x)=
      (z-z*z) • x := by
  simp only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,smul_smul,sub_smul]

end KirchbergRordam.GenericRW.FlipPath
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FieldCalculus
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]

namespace KirchbergRordam.GenericRW.FieldCalculus
open scoped BigOperators
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [CStarAlgebra A]


namespace Data
variable (D : Data X ι A)

omit instSize in
lemma multiplier_star.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {X : Type contextLevel1}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    {A : Type contextLevel3}
    [CStarAlgebra A]
    (D : KirchbergRordam.GenericRW.FieldCalculus.Data X ι A)
    (f : C(X,ℂ)) :
    star (Vanish.multiplier D.p f) = Vanish.multiplier D.p (star f) := by
  apply Subtype.ext
  change star (D.p*f)=D.p*star f
  rw [star_mul,D.selfAdjoint_p.star_eq,mul_comm]

omit instSize in
lemma multiplier_product.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {X : Type contextLevel1}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    {ι : Type contextLevel2}
    [Fintype ι]
    [DecidableEq ι]
    {A : Type contextLevel3}
    [CStarAlgebra A]
    (D : KirchbergRordam.GenericRW.FieldCalculus.Data X ι A)
    (f g : C(X,ℂ)) :
    Vanish.multiplier D.p f * Vanish.multiplier D.p g =
      Vanish.multiplier D.p (D.p*f*g) := by
  apply Subtype.ext
  change (D.p*f)*(D.p*g)=D.p*(D.p*f*g)
  ring

end Data
end KirchbergRordam.GenericRW.FieldCalculus
namespace KirchbergRordam.GenericRW.OrderZero
open scoped BigOperators
open IntervalCalculus
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]


structure Pair (ι κ A : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [CStarAlgebra A] [PartialOrder A] where
  left : WeightedUnits ι A
  right : WeightedUnits κ A
  commute : ∀ i j k l, Commute (left.x i j) (right.x k l)
  sum_one : left.h+right.h=1

namespace Pair
variable (P : Pair ι κ A)
omit [Nontrivial A] [StarOrderedRing A] in
omit instSize in
lemma left_h.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {ι : Type contextLevel1}
    {κ : Type contextLevel2}
    {A : Type contextLevel3}
    [Fintype ι]
    [DecidableEq ι]
    [Fintype κ]
    [DecidableEq κ]
    [CStarAlgebra A]
    [PartialOrder A]
    (P : KirchbergRordam.GenericRW.OrderZero.Pair ι κ A)
    : P.left.h=1-P.right.h := (eq_sub_iff_add_eq).mpr P.sum_one

omit [Nontrivial A] [StarOrderedRing A] in
omit instSize in
lemma left_commute_right_h.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {ι : Type contextLevel1}
    {κ : Type contextLevel2}
    {A : Type contextLevel3}
    [Fintype ι]
    [DecidableEq ι]
    [Fintype κ]
    [DecidableEq κ]
    [CStarAlgebra A]
    [PartialOrder A]
    (P : KirchbergRordam.GenericRW.OrderZero.Pair ι κ A)
    (i j : ι) : Commute (P.left.x i j) P.right.h := by
  change P.left.x i j*P.right.h=P.right.h*P.left.x i j
  rw [← P.right.diagonal,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => (P.commute i j k k).eq

omit [Nontrivial A] [StarOrderedRing A] in
lemma right_commute_left_h (i j : κ) : Commute (P.right.x i j) P.left.h := by
  rw [P.left_h]
  exact (Commute.one_right _).sub_right (P.right.commute_h i j)

abbrev eval : C(unitInterval,ℂ) →⋆ₐ[ℂ] A := IntervalCalculus.hom P.right.nonneg P.right.norm_le

lemma commute_eval {x : A} (hc : Commute x P.right.h) (f : C(unitInterval,ℂ)) :
    Commute x (P.eval f) := by
  exact ((IsSelfAdjoint.of_nonneg P.right.nonneg).commute_cfcHom
    (IsSelfAdjoint.of_nonneg P.right.nonneg).isStarNormal hc.symm _).symm

def weight (_P : Pair ι κ A) : C(unitInterval,ℂ) := (1-coord)*coord

omit [Nontrivial A] [StarOrderedRing A] in
omit instSize in
lemma selfAdjoint_weight.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    {ι : Type contextLevel1}
    {κ : Type contextLevel2}
    {A : Type contextLevel3}
    [Fintype ι]
    [DecidableEq ι]
    [Fintype κ]
    [DecidableEq κ]
    [CStarAlgebra A]
    [PartialOrder A]
    (P : KirchbergRordam.GenericRW.OrderZero.Pair ι κ A)
    : IsSelfAdjoint P.weight := by
  ext t
  simp [weight,coord]

lemma eval_weight : P.eval P.weight = P.left.h*P.right.h := by
  rw [weight,map_mul,map_sub,map_one,hom_coord,P.left_h]

lemma norm_product (i j : ι) (k l : κ) (f : C(unitInterval,ℂ)) :
    ‖(P.left.x i j*P.right.x k l)*P.eval f‖ ≤ ‖P.weight*f‖ := by
  calc
    _ ≤ ‖P.left.h*(P.right.x k l*P.eval f)‖ := by
      rw [mul_assoc]
      exact P.left.norm_mul_le i j _
    _ = ‖P.right.x k l*(P.left.h*P.eval f)‖ := by
      rw [← mul_assoc,(P.right_commute_left_h k l).symm.eq,mul_assoc]
    _ ≤ ‖P.right.h*(P.left.h*P.eval f)‖ := P.right.norm_mul_le k l _
    _ = ‖P.eval (P.weight*f)‖ := by
      rw [map_mul,P.eval_weight,P.left_h]
      congr 1
      noncomm_ring
    _ ≤ ‖P.weight*f‖ := norm_hom_le _ _ _


def field : FieldCalculus.Data unitInterval (ι × κ) A where
  p := P.weight
  selfAdjoint_p := P.selfAdjoint_weight
  eval := P.eval
  x u v := P.left.x u.1 v.1*P.right.x u.2 v.2
  star_x u v := by
    rw [star_mul,P.left.star_x,P.right.star_x]
    exact (P.commute v.1 u.1 v.2 u.2).symm.eq
  mul_x u v w z := by
    have he : (P.left.x u.1 v.1*P.right.x u.2 v.2)*(P.left.x w.1 z.1*P.right.x w.2 z.2) =
        (P.left.x u.1 v.1*P.left.x w.1 z.1)*(P.right.x u.2 v.2*P.right.x w.2 z.2) := by
      rw [mul_assoc (P.left.x u.1 v.1),← mul_assoc (P.right.x u.2 v.2),
        (P.commute w.1 z.1 u.2 v.2).symm.eq]
      noncomm_ring
    rw [he,P.left.mul_x,P.right.mul_x,P.eval_weight]
    by_cases h1 : v.1=w.1 <;> by_cases h2 : v.2=w.2
    · have h : v=w := Prod.ext h1 h2
      simp only [h,↓reduceIte]
      rw [mul_assoc P.left.h,← mul_assoc (P.left.x u.1 z.1),
        (P.left_commute_right_h u.1 z.1).eq]
      noncomm_ring
    · have h : v ≠ w := fun he => h2 (congrArg Prod.snd he)
      simp [h1,h2,h]
    · have h : v ≠ w := fun he => h1 (congrArg Prod.fst he)
      simp [h1,h2,h]
    · have h : v ≠ w := fun he => h1 (congrArg Prod.fst he)
      simp [h1,h2,h]
  commute_eval u v f := P.commute_eval
    ((P.left_commute_right_h u.1 v.1).mul_left (P.right.commute_h u.2 v.2)) f
  bound u v f := P.norm_product _ _ _ _ f

lemma left_x_field (i j : ι) (u v : ι × κ) :
    P.left.x i j * P.field.x u v =
      if j=u.1 then P.left.h*P.field.x (i,u.2) v else 0 := by
  change _*(P.left.x u.1 v.1*P.right.x u.2 v.2) = _
  rw [← mul_assoc,P.left.mul_x]
  by_cases h : j=u.1 <;> simp [h,field,mul_assoc]

lemma right_x_field (i j : κ) (u v : ι × κ) :
    P.right.x i j * P.field.x u v =
      if j=u.2 then P.right.h*P.field.x (u.1,i) v else 0 := by
  change _*(P.left.x u.1 v.1*P.right.x u.2 v.2) = _
  rw [← mul_assoc,(P.commute u.1 v.1 i j).symm.eq,mul_assoc,P.right.mul_x]
  by_cases h : j=u.2
  · simp only [h,↓reduceIte]
    change P.left.x u.1 v.1*(P.right.h*P.right.x i v.2) =
      P.right.h*(P.left.x u.1 v.1*P.right.x i v.2)
    rw [← mul_assoc, (P.left_commute_right_h u.1 v.1).eq,mul_assoc]
  · simp [h]

end Pair
end KirchbergRordam.GenericRW.OrderZero
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_OrderZeroPair
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped BigOperators CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W : WeightedUnits ι A)

lemma mul_eq_zero_of_total {z : A} (hz : W.h*z=0) (i j : ι) : W.x i j*z=0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hz,norm_zero] using W.norm_mul_le i j z


lemma commute_of_total_commutator (y : A) (hy : Commute y W.h) (i j : ι)
    (hz : W.h*(y*W.x i j-W.x i j*y)=0) : Commute y (W.x i j) := by
  let z := y*W.x i j-W.x i j*y
  have hy' : Commute (star y) W.h := by
    simpa only [(IsSelfAdjoint.of_nonneg W.nonneg).star_eq] using hy.star_star
  have h₁ : W.x j i*z=0 := W.mul_eq_zero_of_total hz j i
  have h₂ : W.x j i*(star y*z)=0 := by
    apply W.mul_eq_zero_of_total
    rw [← mul_assoc,hy'.symm.eq,mul_assoc,hz,mul_zero]
  have he : star z*z=0 := by
    dsimp only [z] at h₁ h₂ ⊢
    rw [star_sub,star_mul,star_mul,W.star_x,sub_mul,mul_assoc (W.x j i),h₂,
      mul_assoc (star y),h₁,mul_zero,sub_self]
  have hn : ‖z‖*‖z‖=0 := by rw [← CStarRing.norm_star_mul_self,he,norm_zero]
  have zz : z=0 := norm_eq_zero.mp (mul_self_eq_zero.mp hn)
  exact sub_eq_zero.mp zz


lemma commute_of_spokes (r : ι) (hd : ∀ i,0≤W.x i i) (y : A)
    (hy : ∀ i,Commute y (W.x i r)) (hy' : ∀ i,Commute y (W.x r i)) :
    ∀ i j,Commute y (W.x i j) := by
  have hc (i : ι) : Commute y (W.x i i) := by
    have he : W.x i r*W.x r i=W.x i i*W.x i i := by simp only [W.mul_x,ite_true]
    have ht := ((hy i).mul_right (hy' i)).symm.cfcₙ_nnreal NNReal.sqrt
    change Commute (CFC.sqrt (W.x i r*W.x r i)) y at ht
    rw [he,CFC.sqrt_mul_self _ (hd i)] at ht
    exact ht.symm
  have htotal : Commute y W.h := by
    rw [← W.diagonal]
    exact Commute.sum_right Finset.univ (fun i => W.x i i) y fun i _ => hc i
  intro i j
  apply W.commute_of_total_commutator y htotal
  have hh := (hy i).mul_right (hy' j)
  rw [W.mul_x,ite_eq_left rfl] at hh
  change y*(W.h*W.x i j)=(W.h*W.x i j)*y at hh
  calc
    _=y*(W.h*W.x i j)-(W.h*W.x i j)*y := by
      rw [mul_sub,← mul_assoc,htotal.symm.eq]; noncomm_ring
    _=0 := sub_eq_zero.mpr hh

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FunctionalCalculus
attribute [-instance] _root_.OAI.KirchbergRordam.GenericRW.PauliPower.instFiniteDimensionalComplexCMat _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowDecidableEq _root_.OAI.KirchbergRordam.GenericRW.PauliPower.rowFintype _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


namespace KirchbergRordam.GenericRW

namespace ExactCut
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


omit instSize in
lemma cut_nonneg.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    (a : A) (δ : ℝ) : 0 ≤ cut a δ := CFC.posPart_nonneg _

lemma cut_lower (a : A) (ha : IsSelfAdjoint a) (δ : ℝ) :
    δ • cut a δ ≤ CFC.sqrt (cut a δ) * a * CFC.sqrt (cut a δ) := by
  let d := a - algebraMap ℝ A δ
  let p := cut a δ
  let q := d⁻
  let s := CFC.sqrt p
  have hd : IsSelfAdjoint d := ha.sub (IsSelfAdjoint.algebraMap A (IsSelfAdjoint.all δ))
  have hp : 0 ≤ p := cut_nonneg a δ
  have hs : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)
  have hss : s*s = p := CFC.sqrt_mul_sqrt_self p hp
  have hqs : q*s=0 := Intertwining.mul_sqrt_eq_zero hp (CFC.negPart_mul_posPart d)
  have hdq : d = p-q := (CFC.posPart_sub_negPart d hd).symm
  have hnonneg : 0 ≤ s*d*s := by
    have hh := star_left_conjugate_nonneg hp s
    rw [hs.star_eq] at hh
    rw [hdq, mul_sub, sub_mul, mul_assoc s q s, hqs, mul_zero, sub_zero]
    exact hh
  have heq : s*d*s = s*a*s - δ • p := by
    dsimp only [d]
    rw [mul_sub, sub_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, hss]
  rw [heq, sub_nonneg] at hnonneg
  exact hnonneg

omit instSize in
lemma close_lower.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {η : ℝ} (h : ‖a-b‖ ≤ η) : a ≤ b + algebraMap ℝ A η := by
  have hh := (ha.sub hb).le_algebraMap_norm_self
  have hs : algebraMap ℝ A ‖a-b‖ ≤ algebraMap ℝ A η := by
    simpa only [Algebra.algebraMap_eq_smul_one] using smul_le_smul_of_nonneg_right h (zero_le_one : (0:A) ≤ 1)
  have ht := hh.trans hs
  exact sub_le_iff_le_add.mp ht |>.trans_eq (add_comm _ _)

lemma cut_dominated {a b x : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {δ : ℝ} (hδ : 0 < δ) (hclose : ‖a-star x*b*x‖ < δ/2) :
    cut a δ ≤ (2/δ) • (star (CFC.sqrt b*x*CFC.sqrt (cut a δ)) *
      (CFC.sqrt b*x*CFC.sqrt (cut a δ))) := by
  let e := cut a δ
  let s := CFC.sqrt e
  let y := CFC.sqrt b*x*s
  have hs : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hss : s*s=e := CFC.sqrt_mul_sqrt_self _ (cut_nonneg _ _)
  have hbroot : IsSelfAdjoint (CFC.sqrt b) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have ht : star y*y = s*(star x*b*x)*s := by
    dsimp only [y]
    rw [star_mul, star_mul, hs.star_eq, hbroot.star_eq]
    calc
      _ = s * star x * (CFC.sqrt b * CFC.sqrt b) * x * s := by noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self b hb]; noncomm_ring
  have hc := close_lower (IsSelfAdjoint.of_nonneg ha)
    (IsSelfAdjoint.of_nonneg (star_left_conjugate_nonneg hb x)) hclose.le
  have hc' := star_left_conjugate_le_conjugate hc s
  rw [hs.star_eq, mul_add, add_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, hss, ← ht] at hc'
  have hl := (cut_lower a (IsSelfAdjoint.of_nonneg ha) δ).trans hc'
  have hl' : (δ/2) • e ≤ star y*y := by
    have h : δ • e - (δ/2) • e ≤ star y*y := (sub_le_iff_le_add).mpr hl
    convert h using 1
    rw [← sub_smul]
    congr 1
    ring
  have hC : 0 ≤ 2/δ := le_of_lt (div_pos (by norm_num) hδ)
  have hf := smul_le_smul_of_nonneg_left hl' hC
  rw [smul_smul] at hf
  have hscalar : (2/δ)*(δ/2) = (1:ℝ) := by field_simp
  rw [hscalar, one_smul] at hf
  exact hf


end ExactCut
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.RWCut
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

omit instSize in
lemma j_cont
    [KirchbergRordam.GenericRW.Size]
    : Continuous j := Continuous.inv₀ (by fun_prop)
  (fun t => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (le_max_right t _)))
lemma f_cont : Continuous f := j_cont.mul continuous_id
omit instSize in
lemma f_nonneg
    [KirchbergRordam.GenericRW.Size]
    {t : ℝ} (ht : 0≤t) : 0≤f t :=
  mul_nonneg (inv_nonneg.mpr (le_trans (by norm_num) (le_max_right t (1/2)))) ht
omit instSize in
lemma f_le_one
    [KirchbergRordam.GenericRW.Size]
    {t : ℝ} : f t≤1 := by
  unfold f j
  have hp : 0 < max t (1/2:ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  rw [mul_comm,← div_eq_mul_inv,div_le_one hp]
  exact le_max_left _ _
omit instSize in
lemma f_high
    [KirchbergRordam.GenericRW.Size]
    {t : ℝ} (ht : 1/2≤t) : f t=1 := by
  have hp : 0<t := lt_of_lt_of_le (by norm_num) ht
  unfold f j
  rw [max_eq_left ht,inv_mul_cancel₀ (ne_of_gt hp)]
omit instSize in
lemma f_low
    [KirchbergRordam.GenericRW.Size]
    {t : ℝ} (ht : t≤1/2) : f t=2*t := by
  norm_num [f,j,max_eq_right ht]
lemma defect {t : ℝ} : 1-f t=2*max ((1-t)-1/2) 0 := by
  by_cases h : t≤1/2
  · rw [f_low h,max_eq_left (by linarith)]; ring
  · rw [f_high (le_of_lt (lt_of_not_ge h)),max_eq_right (by linarith)]; ring

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
omit instSize in
lemma cut_cfc.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a : A} (ha : IsSelfAdjoint a) (δ : ℝ) :
    ExactCut.cut a δ=cfc (fun t : ℝ => max (t-δ) 0) a := by
  rw [ExactCut.cut,CFC.posPart_def,cfcₙ_eq_cfc]
  have hd : cfc (fun t : ℝ => t-δ) a=a-algebraMap ℝ A δ := by
    rw [cfc_sub ..]
    change cfc id a-cfc (fun _ : ℝ=>δ) a=_
    rw [cfc_id ℝ a ha,cfc_const _ _ ha]
  rw [← hd,← cfc_comp (fun t : ℝ=>t⁺) (fun t : ℝ=>t-δ) a ha]
  rfl

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
lemma function_mul (a : A) (ha : IsSelfAdjoint a) : cfc j a*a=cfc f a := by
  calc
    _=cfc j a*cfc id a := by rw [cfc_id ℝ a ha]
    _=_ := (cfc_mul j id a j_cont.continuousOn continuous_id.continuousOn).symm

omit [Nontrivial A] in
lemma rescaled_nonneg {a : A} (ha : 0≤a) : 0≤cfc f a :=
  cfc_nonneg fun _ ht => f_nonneg (spectrum_nonneg_of_nonneg ha ht)
omit [Nontrivial A] in
lemma rescaled_norm {a : A} (ha : 0≤a) : ‖cfc f a‖≤1 := by
  apply norm_cfc_le (by norm_num)
  intro t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (f_nonneg (spectrum_nonneg_of_nonneg ha ht))]
  exact f_le_one

omit [Nontrivial A] in
lemma rescaled_defect {a : A} (ha : 0≤a) : 1-cfc f a=(2:ℝ) • ExactCut.cut (1-a) (1/2) := by
  have hs := IsSelfAdjoint.of_nonneg ha
  have hd : cfc (fun t : ℝ=>1-t) a=1-a := by
    rw [cfc_sub ..,cfc_const_one ℝ a hs]
    change 1-cfc id a=1-a
    rw [cfc_id ℝ a hs]
  rw [cut_cfc ((IsSelfAdjoint.one A).sub hs),← hd,
    ← cfc_comp (fun t : ℝ=>max (t-1/2) 0) (fun t : ℝ=>1-t) a hs]
  have he : cfc (fun t : ℝ=>1-f t) a=cfc (fun t : ℝ=>2*max ((1-t)-1/2) 0) a :=
    cfc_congr fun _ _ => defect
  rw [cfc_sub _ _ a continuous_const.continuousOn f_cont.continuousOn,cfc_const_one ℝ a hs] at he
  rw [he,cfc_const_mul ..]
  rfl

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
lemma fixes_cut {a : A} (ha : IsSelfAdjoint a) :
    cfc f a*ExactCut.cut a (1/2)=ExactCut.cut a (1/2) := by
  rw [cut_cfc ha,← cfc_mul f _ a f_cont.continuousOn (by fun_prop)]
  apply cfc_congr
  intro t _
  change f t*max (t-1/2) 0=max (t-1/2) 0
  by_cases ht : 1/2≤t
  · simp [f_high ht]
  · rw [max_eq_right (by linarith : t-1/2≤0),mul_zero]

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
omit instSize in
lemma fixes_hereditary.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a c z : A} (hc : c*a=a) (hz : z∈ClosedRightRange.hereditary a) : c*z=z := by
  have hs : IsClosed {z : A | c*z=z} := isClosed_eq (by fun_prop) continuous_id
  apply closure_minimal ?_ hs hz
  rintro _ ⟨x,rfl⟩
  change c*(a*x*a)=a*x*a
  rw [← mul_assoc,← mul_assoc,hc]

omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
omit instSize in
lemma fixes_of_mul_star.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a v : A} (h : a*(v*star v)=v*star v) : a*v=v := by
  have he : (a*v-v)*star (a*v-v)=0 := by
    have hh := congrArg star h
    simp only [star_mul,star_star] at hh
    calc
      _=a*(v*star v)*star a-a*(v*star v)-(v*star v)*star a+v*star v := by
        simp only [star_sub,star_mul]; noncomm_ring
      _=0 := by rw [h,show v*star v*star a=v*star v from hh]; noncomm_ring
  exact sub_eq_zero.mp ((CStarRing.mul_star_self_eq_zero_iff _).mp he)
end KirchbergRordam.GenericRW.RWCut

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
section
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)
def cutoffRescale : WeightedUnits (Fin rankNum) A :=
  W.rescale (cfc RWCut.j W.h) (cfc RWCut.f W.h) (cfc_predicate ..)
    (fun i j => (W.commute_h i j).symm.cfc_real _) (RWCut.function_mul _ (IsSelfAdjoint.of_nonneg W.nonneg))
    (RWCut.rescaled_nonneg W.nonneg) (RWCut.rescaled_norm W.nonneg)
end

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FullComparison
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.MaxTensor
open scoped CStarAlgebra BigOperators
variable {P : Type*} [CStarAlgebra P]
variable {I : Type*} [Fintype I]

local instance instPartialOrderCarrierPowerPack (n : ℕ) : PartialOrder (powerPack P n) := CStarAlgebra.spectralOrder _
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped BigOperators
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def map (W : WeightedUnits ι A) (φ : A →⋆ₐ[ℂ] B) : WeightedUnits ι B where
  h := φ W.h
  x i j := φ (W.x i j)
  nonneg := map_nonneg φ W.nonneg
  norm_le := (NonUnitalStarAlgHom.norm_apply_le φ _).trans W.norm_le
  star_x i j := by rw [← map_star,W.star_x]
  mul_x i j k l := by rw [← map_mul,W.mul_x]; split_ifs <;> simp [map_mul]
  diagonal := by rw [← map_sum,W.diagonal]
end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FiniteDrop
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor OrderZero Fullness
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def reindex (W : WeightedUnits I A) (e : I ≃ J) : WeightedUnits J A where
  h := W.h
  x i j := W.x (e.symm i) (e.symm j)
  nonneg := W.nonneg
  norm_le := W.norm_le
  star_x i j := W.star_x _ _
  mul_x i j k l := by simp only [W.mul_x,EmbeddingLike.apply_eq_iff_eq]
  diagonal := (Equiv.sum_comp e.symm (fun i=>W.x i i)).trans W.diagonal

end KirchbergRordam.GenericRW.FullRankWeighted

namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor OrderZero Fullness
universe u
variable {P : Type u} [CStarAlgebra P]
local instance instPartialOrderCarrierPowerPack (n : ℕ) : PartialOrder (powerPack P n) := CStarAlgebra.spectralOrder _
local instance instStarOrderedRingCarrierPowerPack (n : ℕ) : StarOrderedRing (powerPack P n) := CStarAlgebra.spectralOrderedRing _

abbrev Row := KirchbergRordam.PauliPower.Row

end KirchbergRordam.GenericRW.FullRankWeighted

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SeparableReduction
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


namespace KirchbergRordam.PrimeDimensionDrop
open MatrixTensor
open scoped Matrix Kronecker ComplexOrder CStarAlgebra


instance instNontrivialSubtypeContinuousMapElemRealUnitIntervalFiberMemStarSubalgebraComplexAlgebraOfNeZeroNat (p q : ℕ) [NeZero p] [NeZero q] : Nontrivial (Algebra p q) := inferInstance

instance instSeparableSpaceSubtypeContinuousMapElemRealUnitIntervalFiberMemStarSubalgebraComplexAlgebra (p q : ℕ) : TopologicalSpace.SeparableSpace (Algebra p q) := inferInstance

lemma mem_iff {p q : ℕ} (f : C(unitInterval, Fiber p q)) :
    f ∈ subalgebra p q ↔
      (∃ a : Mat (Fin p), leftMatrix a = f 0) ∧
      (∃ b : Mat (Fin q), rightMatrix b = f 1) := Iff.rfl


def scalar (p q : ℕ) : C(unitInterval, ℂ) →⋆ₐ[ℂ] Algebra p q where
  toFun f := ⟨⟨fun t => (f t) • (1 : Fiber p q), by fun_prop⟩, by
    constructor
    · exact ⟨(f 0) • 1, by simp⟩
    · exact ⟨(f 1) • 1, by simp⟩⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' f g := by ext; simp [add_smul]
  map_mul' f g := by ext; simp [mul_smul, mul_left_comm]
  commutes' z := by ext; simp [Algebra.algebraMap_eq_smul_one]
  map_star' f := by ext; simp


end KirchbergRordam.PrimeDimensionDrop

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_InductiveLimit
attribute [-instance] _root_.OAI.KirchbergRordam.MaxTensor.instCStarRingAlgebra _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


open scoped TensorProduct CStarAlgebra

namespace KirchbergRordam
namespace StarCompletion

open UniformSpace
variable (R : Type*) [SeminormedRing R] [StarRing R] [NormedStarGroup R]


instance completionNormedStarGroup : NormedStarGroup (Completion R) where
  norm_star_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simp only [star_coe, Completion.norm_coe, norm_star, le_refl]


end StarCompletion

end KirchbergRordam


namespace KirchbergRordam.CStarInductiveLimit
section
universe u


attribute [instance] System.cstar


end

universe u


attribute [instance] Chain.cstar


end KirchbergRordam.CStarInductiveLimit


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedLimit
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


namespace KirchbergRordam

open scoped Matrix Kronecker ComplexOrder

instance instFiniteDimensionalComplexM6 : FiniteDimensional ℂ M6 :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ))

end KirchbergRordam


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam
namespace MaxTensor


open scoped CStarAlgebra


universe u


attribute [instance] CStarPack.inst

end MaxTensor
end KirchbergRordam
namespace KirchbergRordam.MatrixTensor
open scoped TensorProduct Matrix Kronecker CStarAlgebra ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
def unit (i : ι) (j : ι) : Mat ι := CStarMatrix.ofMatrix (Matrix.single i j 1)

def kroneckerRaw : (Mat ι ⊗[ℂ] Mat κ) →⋆ₐ[ℂ] Mat (ι×κ) :=
  MaxTensor.liftRaw (MatrixTensor.leftMatrix (ι:=ι) (κ:=κ)) (MatrixTensor.rightMatrix (ι:=ι) (κ:=κ)) (fun a b => legs_commute a b)

def kroneckerInverse : Mat (ι×κ) →ₗ[ℂ] (Mat ι ⊗[ℂ] Mat κ) where
  toFun c := ∑ ij : ι×ι, ∑ kl : κ×κ,
    c (ij.1,kl.1) (ij.2,kl.2) • (unit ij.1 ij.2 ⊗ₜ[ℂ] unit kl.1 kl.2)
  map_add' a b := by simp [Finset.sum_add_distrib,add_smul]
  map_smul' z a := by simp [Finset.smul_sum,mul_smul]

end KirchbergRordam.MatrixTensor

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_UltrapowerSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.NormUltrapower
open Filter Topology BoundedContinuousFunction
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def sequenceMap (φ : A →⋆ₐ[ℂ] B) : BoundedSeq A →⋆ₐ[ℂ] BoundedSeq B where
  toFun x := ofNormedAddCommGroupDiscrete (fun n => φ (x n)) ‖x‖ (fun n =>
    (NonUnitalStarAlgHom.norm_apply_le φ (x n)).trans (x.norm_coe_le_norm n))
  map_zero' := by ext n; exact map_zero φ
  map_one' := by ext n; exact map_one φ
  map_add' x y := by ext n; exact map_add φ (x n) (y n)
  map_mul' x y := by ext n; exact map_mul φ (x n) (y n)
  commutes' r := by ext n; exact φ.commutes r
  map_star' x := by ext n; exact map_star φ (x n)
@[simp] lemma sequenceMap_apply (φ : A →⋆ₐ[ℂ] B) (x : BoundedSeq A) (n : ℕ) :
    sequenceMap φ x n = φ (x n) := rfl
lemma sequenceMap_null (φ : A →⋆ₐ[ℂ] B) (ω : Ultrafilter ℕ)
    {x : BoundedSeq A} (hx : x ∈ nullIdeal ω) : sequenceMap φ x ∈ nullIdeal ω := by
  apply (mem_nullIdeal ω _).mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => NonUnitalStarAlgHom.norm_apply_le φ (x n))
  exact (mem_nullIdeal ω x).mp hx

def map (φ : A →⋆ₐ[ℂ] B) (ω : Ultrafilter ℕ) : Algebra A ω →⋆ₐ[ℂ] Algebra B ω where
  __ := Ideal.Quotient.liftₐ (nullIdeal ω)
    ((quotientMap ω).comp (sequenceMap φ)).toAlgHom (fun x hx =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (sequenceMap_null φ ω hx))
  map_star' := by
    intro x
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
    change quotientMap ω (sequenceMap φ (star y))=star (quotientMap ω (sequenceMap φ y))
    rw [map_star,map_star]
@[simp] lemma map_mk (φ : A →⋆ₐ[ℂ] B) (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    map φ ω (quotientMap ω x)=quotientMap ω (sequenceMap φ x) := rfl
@[simp] lemma map_diagonal (φ : A →⋆ₐ[ℂ] B) (ω : Ultrafilter ℕ) (a : A) :
    map φ ω (NormUltrapower.diagonal ω a)=NormUltrapower.diagonal ω (φ a) := by
  change quotientMap ω (sequenceMap φ (constantSeq a))=quotientMap ω (constantSeq (φ a))
  congr 1

end KirchbergRordam.NormUltrapower

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MinTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u


attribute [instance] RepresentationPair.normH RepresentationPair.innerH
  RepresentationPair.completeH RepresentationPair.normK RepresentationPair.innerK
  RepresentationPair.completeK


end KirchbergRordam.MinTensor
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]

lemma bounded : BddAbove (Set.range (fun ρ : Option (RepresentationPair A B) =>
    (spatialIndex ρ).toSeminorm)) := by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨C,hC⟩ := MaxTensor.bounded_at x
  exact ⟨C,by rintro _ ⟨ρ,rfl⟩; exact hC _⟩
lemma seminorm_apply (x : A ⊗[ℂ] B) :
    seminorm x=⨆ ρ : Option (RepresentationPair A B), (spatialIndex ρ).toSeminorm x :=
  Seminorm.iSup_apply bounded
lemma le_seminorm (ρ : Option (RepresentationPair A B)) (x : A ⊗[ℂ] B) :
    (spatialIndex ρ).toSeminorm x ≤ seminorm x := by
  rw [seminorm_apply]
  apply le_ciSup _ ρ
  obtain ⟨C,hC⟩ := MaxTensor.bounded_at x
  exact ⟨C,by rintro _ ⟨ρ,rfl⟩; exact hC _⟩
lemma seminorm_le {x : A ⊗[ℂ] B} {C : ℝ}
    (h : ∀ ρ : Option (RepresentationPair A B), (spatialIndex ρ).toSeminorm x ≤ C) :
    seminorm x ≤ C := by
  rw [seminorm_apply]
  exact ciSup_le h
attribute [local instance] OAI.KirchbergRordam.MinTensor.instRingTensorProductComplex_solutions
lemma seminorm_mul_le (x y : A ⊗[ℂ] B) :
    @LE.le ℝ Real.instLE
      (seminorm (@Mul.mul (A ⊗[ℂ] B)
        (_root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)).toMul x y))
      (@Mul.mul ℝ Real.instMul (seminorm x) (seminorm y)) := by
  apply seminorm_le
  intro ρ
  exact ((spatialIndex ρ).mul_le x y).trans (mul_le_mul (le_seminorm ρ x)
    (le_seminorm ρ y) (apply_nonneg _ _) (apply_nonneg _ _))
lemma seminorm_star (x : A ⊗[ℂ] B) : seminorm (star x)=seminorm x := by
  rw [seminorm_apply,seminorm_apply]
  congr 1
  funext ρ
  exact (spatialIndex ρ).star_eq x
lemma seminorm_cstar (x : A ⊗[ℂ] B) :
    seminorm (star x*x)=seminorm x * seminorm x := by
  apply le_antisymm
  · calc
      seminorm (star x * x) ≤ seminorm (star x) * seminorm x := seminorm_mul_le (star x) x
      _ = seminorm x * seminorm x := by rw [seminorm_star]
  · have h : seminorm x ≤ Real.sqrt (seminorm (star x*x)) := by
      apply seminorm_le
      intro ρ
      apply (Real.le_sqrt (apply_nonneg _ _) (apply_nonneg _ _)).mpr
      simpa only [← (spatialIndex ρ).cstar_eq x,pow_two] using le_seminorm ρ (star x*x)
    have := mul_self_le_mul_self (apply_nonneg seminorm x) h
    rwa [Real.mul_self_sqrt (apply_nonneg seminorm _)] at this
end KirchbergRordam.MinTensor

namespace KirchbergRordam.MinTensor
open scoped TensorProduct CStarAlgebra
universe u
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]

variable {A B}
instance instNormedStarGroupRaw : NormedStarGroup (Raw A B) where
  norm_star_le x := (seminorm_star x).le


instance instCStarRingAlgebra : CStarRing (Algebra A B) where
  norm_mul_self_le x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      simp only [StarCompletion.star_coe, ← UniformSpace.Completion.coe_mul,
        UniformSpace.Completion.norm_coe, norm_raw]
      exact (seminorm_cstar x).ge
end KirchbergRordam.MinTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MultiplicativeChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.MultiplicativeChannel
open scoped CStarAlgebra ComplexOrder
variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


variable {A B}
variable {C : Type*} [CStarAlgebra C]
def postcompose (φ : Channel A B) (f : B →⋆ₐ[ℂ] C) : Channel A C where
  linear := f.toAlgHom.toLinearMap.comp φ.linear
  norm_le a := (NonUnitalStarAlgHom.norm_apply_le f _).trans (φ.norm_le a)
  mul_eq a b := by
    change f (φ a)*f (φ b)=f (φ 1)*f (φ (a*b))
    simpa only [_root_.map_mul] using congrArg f (φ.mul_eq a b)
def normalized (φ : Channel A B) (χ : B →⋆ₐ[ℂ] ℂ) (h : χ (φ 1)≠0) : A →+* ℂ where
  toFun a := (χ (φ 1))⁻¹ * χ (φ a)
  map_zero' := by simp
  map_one' := inv_mul_cancel₀ h
  map_add' a b := by simp [mul_add]
  map_mul' a b := by
    have hm := congrArg χ (φ.mul_eq a b)
    simp only [map_mul] at hm
    calc
      _ = (χ (φ 1))⁻¹ * ((χ (φ 1))⁻¹ * (χ (φ a)*χ (φ b))) := by rw [hm]; field_simp
      _ = _ := by ring
end KirchbergRordam.MultiplicativeChannel
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.MultiplicativeChannel
open Filter Topology TopologicalSpace
open scoped CStarAlgebra ComplexOrder
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
def sequence (φ : ℕ → Channel D A) : Channel D (NormUltrapower.BoundedSeq A) where
  linear := {
    toFun d := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun n => φ n d) ‖d‖ (fun n => (φ n).norm_le d)
    map_add' d e := by ext n; exact (φ n).linear.map_add d e
    map_smul' z d := by ext n; exact (φ n).linear.map_smul z d }
  norm_le d := (BoundedContinuousFunction.norm_le (norm_nonneg d)).mpr (fun n => (φ n).norm_le d)
  mul_eq d e := by ext n; exact (φ n).mul_eq d e

def centralize (ω : Ultrafilter ℕ) (φ : Channel D (NormUltrapower.Algebra A ω))
    (hφ : ∀ d, φ d∈NormUltrapower.centralSubalgebra ω) :
    Channel D (NormUltrapower.CentralAlgebra A ω) where
  linear := {
    toFun d := ⟨φ d,hφ d⟩
    map_add' d e := Subtype.ext (φ.linear.map_add d e)
    map_smul' z d := Subtype.ext (φ.linear.map_smul z d) }
  norm_le d := φ.norm_le d
  mul_eq d e := Subtype.ext (φ.mul_eq d e)

end KirchbergRordam.MultiplicativeChannel
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation
open scoped CStarAlgebra ComplexOrder
variable (S : PrimeDropPresentation)
def Algebra : Type := CStarInductiveLimit.Algebra S.system
instance instCStarAlgebraAlgebra : CStarAlgebra S.Algebra := inferInstanceAs (CStarAlgebra (CStarInductiveLimit.Algebra S.system))
def inclusion (n : ℕ) : S.Stage n →⋆ₐ[ℂ] S.Algebra := CStarInductiveLimit.of S.system n
end KirchbergRordam.PrimeDropPresentation
end

end OAI
end


