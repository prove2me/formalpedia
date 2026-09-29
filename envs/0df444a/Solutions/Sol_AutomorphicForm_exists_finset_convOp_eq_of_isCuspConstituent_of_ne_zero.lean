-- Prove2me | solution 1 for AutomorphicForm.exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b587a832-bdb7-545a-9827-6e5f438670e9

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Support
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Theorems.Thm_LocalGL2_localHeckeMul_comm
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
import Theorems.Thm_AutomorphicForm_exists_finset_sum_convOp_eq_self_of_isCuspConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace LevelPieces
namespace Components

section Local

variable (L : Type) [Field L] [NumberField L]

private def IsLocalLevelOne (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L))
    (m : Fin 2 → Fin 2 → w.adicCompletion L) : Prop :=
  (∀ i j, m i j ∈ w.adicCompletionIntegers L) ∧
    Valued.v (m 1 0) ≤ AdelicLevel.idealBound (𝓞 L) N w ∧
      Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound (𝓞 L) N w

variable {L}

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : AdelicLevel.idealBound (𝓞 L) N w = 1) {m : Fin 2 → Fin 2 → w.adicCompletion L}
    (hm : ∀ i j, m i j ∈ w.adicCompletionIntegers L) : IsLocalLevelOne L N w m := by
  refine ⟨hm, ?_, ?_⟩
  · rw [hb]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hm 1 0)
  · rw [hb]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (sub_mem (hm 1 1) (one_mem _))

private theorem isLevelOneMatrix_iff_forall {N : Ideal (𝓞 L)}
    (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    AdelicLevel.IsLevelOneMatrix (𝓞 L) L N M ↔
      ∀ w : HeightOneSpectrum (𝓞 L),
        IsLocalLevelOne L N w fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w (M i j) := by
  constructor
  · intro h w
    exact ⟨fun i j => h.integral i j w, h.lowerLeft w, h.lowerRight w⟩
  · intro h
    exact
      { integral := fun i j w => (h w).1 i j
        lowerLeft := fun w => (h w).2.1
        lowerRight := fun w => (h w).2.2 }

private theorem mem_finiteLevelOne_iff_forall {N : Ideal (𝓞 L)} (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    h ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N ↔
      ∀ w : HeightOneSpectrum (𝓞 L),
        (IsLocalLevelOne L N w fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w (h.val i j)) ∧
          IsLocalLevelOne L N w fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w ((h⁻¹).val i j) := by
  rw [AdelicLevel.mem_finiteLevelOne_iff, isLevelOneMatrix_iff_forall, isLevelOneMatrix_iff_forall]
  exact forall_and.symm

private def assembleAdele (x : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L)
    (hx : ∀ w, x w ∈ w.adicCompletionIntegers L) : FiniteAdeleRing (𝓞 L) L :=
  ⟨x, Filter.Eventually.of_forall hx⟩

private theorem assembleAdele_apply (x : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L)
    (hx : ∀ w, x w ∈ w.adicCompletionIntegers L) (w : HeightOneSpectrum (𝓞 L)) :
    AdelicLevel.finAdeleEval (𝓞 L) L w (assembleAdele x hx) = x w :=
  rfl

private def assembleMatrix (m : ∀ w : HeightOneSpectrum (𝓞 L), Matrix (Fin 2) (Fin 2) (w.adicCompletion L))
    (hm : ∀ w i j, m w i j ∈ w.adicCompletionIntegers L) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  fun i j => assembleAdele (fun w => m w i j) fun w => hm w i j

private theorem mapMatrix_assembleMatrix
    (m : ∀ w : HeightOneSpectrum (𝓞 L), Matrix (Fin 2) (Fin 2) (w.adicCompletion L))
    (hm : ∀ w i j, m w i j ∈ w.adicCompletionIntegers L) (w : HeightOneSpectrum (𝓞 L)) :
    (AdelicLevel.finAdeleEval (𝓞 L) L w).mapMatrix (assembleMatrix m hm) = m w :=
  Matrix.ext fun _ _ => rfl

private theorem matrix_ext_of_forall_mapMatrix {A B : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (h : ∀ w : HeightOneSpectrum (𝓞 L),
      (AdelicLevel.finAdeleEval (𝓞 L) L w).mapMatrix A = (AdelicLevel.finAdeleEval (𝓞 L) L w).mapMatrix B) :
    A = B := by
  ext i j w : 2
  have hw := congrFun (congrFun (h w) i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply] using hw

private theorem entries_mem_of_isLocalLevelOne {N : Ideal (𝓞 L)}
    {g : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L)}
    (hg : ∀ w, IsLocalLevelOne L N w (g w).val ∧ IsLocalLevelOne L N w ((g w)⁻¹).val) (w : HeightOneSpectrum (𝓞 L))
    (i j : Fin 2) : (g w).val i j ∈ w.adicCompletionIntegers L :=
  (hg w).1.1 i j

private theorem inv_entries_mem_of_isLocalLevelOne {N : Ideal (𝓞 L)}
    {g : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L)}
    (hg : ∀ w, IsLocalLevelOne L N w (g w).val ∧ IsLocalLevelOne L N w ((g w)⁻¹).val) (w : HeightOneSpectrum (𝓞 L))
    (i j : Fin 2) : ((g w)⁻¹).val i j ∈ w.adicCompletionIntegers L :=
  (hg w).2.1 i j

private def assembleGL {N : Ideal (𝓞 L)} (g : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L))
    (hg : ∀ w, IsLocalLevelOne L N w (g w).val ∧ IsLocalLevelOne L N w ((g w)⁻¹).val) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) where
  val := assembleMatrix (fun w => (g w).val) (entries_mem_of_isLocalLevelOne hg)
  inv := assembleMatrix (fun w => ((g w)⁻¹).val) (inv_entries_mem_of_isLocalLevelOne hg)
  val_inv := by
    refine matrix_ext_of_forall_mapMatrix fun w => ?_
    rw [map_mul, map_one, mapMatrix_assembleMatrix, mapMatrix_assembleMatrix]
    exact Units.mul_inv (g w)
  inv_val := by
    refine matrix_ext_of_forall_mapMatrix fun w => ?_
    rw [map_mul, map_one, mapMatrix_assembleMatrix, mapMatrix_assembleMatrix]
    exact Units.inv_mul (g w)

private theorem finComponent_assembleGL
    {N : Ideal (𝓞 L)} (g : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L))
    (hg : ∀ w, IsLocalLevelOne L N w (g w).val ∧ IsLocalLevelOne L N w ((g w)⁻¹).val) (w : HeightOneSpectrum (𝓞 L)) :
    AdelicLevel.finComponent (𝓞 L) L w (assembleGL g hg) = g w :=
  Units.ext (mapMatrix_assembleMatrix (fun w => (g w).val) (entries_mem_of_isLocalLevelOne hg) w)

private theorem finAdeleEval_assembleGL_val {N : Ideal (𝓞 L)}
    (g : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L))
    (hg : ∀ w, IsLocalLevelOne L N w (g w).val ∧ IsLocalLevelOne L N w ((g w)⁻¹).val) (w : HeightOneSpectrum (𝓞 L))
    (i j : Fin 2) : AdelicLevel.finAdeleEval (𝓞 L) L w ((assembleGL g hg).val i j) = (g w).val i j :=
  rfl

private theorem finAdeleEval_assembleGL_inv_val {N : Ideal (𝓞 L)}
    (g : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L))
    (hg : ∀ w, IsLocalLevelOne L N w (g w).val ∧ IsLocalLevelOne L N w ((g w)⁻¹).val) (w : HeightOneSpectrum (𝓞 L))
    (i j : Fin 2) : AdelicLevel.finAdeleEval (𝓞 L) L w (((assembleGL g hg)⁻¹).val i j) = ((g w)⁻¹).val i j :=
  rfl

private theorem assembleGL_mem_finiteLevelOne {N : Ideal (𝓞 L)}
    (g : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L))
    (hg : ∀ w, IsLocalLevelOne L N w (g w).val ∧ IsLocalLevelOne L N w ((g w)⁻¹).val) :
    assembleGL g hg ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N := by
  rw [mem_finiteLevelOne_iff_forall]
  intro w
  exact hg w

private theorem gl_ext_of_forall_finComponent {x y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (h : ∀ w : HeightOneSpectrum (𝓞 L), AdelicLevel.finComponent (𝓞 L) L w x = AdelicLevel.finComponent (𝓞 L) L w y) :
    x = y := by
  refine Units.ext (matrix_ext_of_forall_mapMatrix fun w => ?_)
  exact congrArg Units.val (h w)

end Local

end LevelPieces.Components

namespace LevelPieces

open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem isOpen_doubleCoset (U : Subgroup G) (hU : IsOpen (U : Set G)) (a : G) :
    IsOpen (DoubleCoset.doubleCoset a (U : Set G) U) :=
  hU.mul_left

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem eq_of_mem_doubleCoset (U : Subgroup G) {f : G → ℂ} (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g)
    (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) {a g : G} (hg : g ∈ DoubleCoset.doubleCoset a (U : Set G) U) :
    f g = f a := by
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
  rw [hr y hy, hl x hx]

private theorem exists_finset_eq_sum_smul_indicator_doubleCoset (U : Subgroup G) (hU : IsOpen (U : Set G))
    (f : G → ℂ) (hf : HasCompactSupport f) (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g)
    (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    ∃ s : Finset G,
      (∀ a ∈ s, ∀ b ∈ s, a ≠ b →
        Disjoint (DoubleCoset.doubleCoset a (U : Set G) U) (DoubleCoset.doubleCoset b (U : Set G) U)) ∧
      f = ∑ a ∈ s, f a • (DoubleCoset.doubleCoset a (U : Set G) U).indicator (fun _ => (1 : ℂ)) := by
  classical

  have hcov : tsupport f ⊆ ⋃ x ∈ tsupport f, DoubleCoset.doubleCoset x (U : Set G) U := fun x hx =>
    Set.mem_biUnion hx (DoubleCoset.mem_doubleCoset_self U U x)
  obtain ⟨t, -, htfin, htcov⟩ := IsCompact.elim_finite_subcover_image (s := tsupport f) hf
    (fun x _ => isOpen_doubleCoset U hU x) hcov

  let Q : Finset (DoubleCoset.Quotient (U : Set G) U) := htfin.toFinset.image (DoubleCoset.mk U U)
  refine ⟨Q.image fun q => q.out, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨qa, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨qb, -, rfl⟩ := Finset.mem_image.mp hb
    exact DoubleCoset.disjoint_out fun h => hab (by rw [h])
  · funext g
    rw [Finset.sum_apply]
    by_cases hg : ∃ a ∈ Q.image (fun q => q.out), g ∈ DoubleCoset.doubleCoset a (U : Set G) U
    · obtain ⟨a, ha, hga⟩ := hg
      rw [Finset.sum_eq_single_of_mem a ha]
      · simp only [Pi.smul_apply, Set.indicator_of_mem hga, smul_eq_mul, mul_one]
        exact eq_of_mem_doubleCoset U hl hr hga
      · intro b hb hba
        have hdis := (by
          obtain ⟨qa, -, rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨qb, -, rfl⟩ := Finset.mem_image.mp hb
          exact DoubleCoset.disjoint_out fun h => hba (by rw [h]) :
            Disjoint (DoubleCoset.doubleCoset b (U : Set G) U) (DoubleCoset.doubleCoset a (U : Set G) U))
        have hgb : g ∉ DoubleCoset.doubleCoset b (U : Set G) U := fun hgb =>
          Set.disjoint_left.mp hdis hgb hga
        simp only [Pi.smul_apply, Set.indicator_of_notMem hgb, smul_zero]
    · push Not at hg
      have hz : f g = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hgs => ?_
        obtain ⟨x, hxt, hgx⟩ := Set.mem_iUnion₂.mp (htcov hgs)
        have hxQ : DoubleCoset.mk U U x ∈ Q :=
          Finset.mem_image.mpr ⟨x, htfin.mem_toFinset.mpr hxt, rfl⟩
        have hout : (DoubleCoset.mk U U x).out ∈ DoubleCoset.doubleCoset x (U : Set G) U := by
          obtain ⟨h, k, hh, hk, heq⟩ := DoubleCoset.mk_out_eq_mul U U x
          rw [heq]
          exact DoubleCoset.mem_doubleCoset.mpr ⟨h, hh, k, hk, rfl⟩
        have hsame := DoubleCoset.doubleCoset_eq_of_mem (H := U) (K := U) hout
        refine hg _ (Finset.mem_image.mpr ⟨_, hxQ, rfl⟩) ?_
        rw [hsame]
        exact hgx
      rw [hz]
      refine (Finset.sum_eq_zero fun a ha => ?_).symm
      simp only [Pi.smul_apply, Set.indicator_of_notMem (hg a ha), smul_zero]

end LevelPieces

open AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace LevelPieces
namespace Pieces

open LevelPieces.Components

section LocalExtra

variable {L : Type} [Field L] [NumberField L]

private theorem isOpen_setOf_isLocalLevelOne {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) {X : Type} [TopologicalSpace X]
    {w : HeightOneSpectrum (𝓞 L)} (m : X → Fin 2 → Fin 2 → w.adicCompletion L)
    (hm : ∀ i j, Continuous fun x => m x i j) : IsOpen {x | IsLocalLevelOne L N w (m x)} := by
  have h1 : IsOpen {x | ∀ i j, m x i j ∈ w.adicCompletionIntegers L} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 L) L).out w).preimage (hm i j)
  have h2 : IsOpen {x | Valued.v (m x 1 0) ≤ AdelicLevel.idealBound (𝓞 L) N w} :=
    (AdelicLevel.isOpen_setOf_valued_le_idealBound (K := L) w hN).preimage (hm 1 0)
  have h3 : IsOpen {x | Valued.v (m x 1 1 - 1) ≤ AdelicLevel.idealBound (𝓞 L) N w} :=
    (AdelicLevel.isOpen_setOf_valued_le_idealBound (K := L) w hN).preimage
      ((hm 1 1).sub continuous_const)
  exact h1.inter (h2.inter h3)

private theorem isClosed_setOf_isLocalLevelOne (N : Ideal (𝓞 L)) {X : Type} [TopologicalSpace X]
    {w : HeightOneSpectrum (𝓞 L)} (m : X → Fin 2 → Fin 2 → w.adicCompletion L)
    (hm : ∀ i j, Continuous fun x => m x i j) : IsClosed {x | IsLocalLevelOne L N w (m x)} := by
  have h1 : IsClosed {x | ∀ i j, m x i j ∈ w.adicCompletionIntegers L} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      (AdelicLevel.isClosed_adicCompletionIntegers (K := L) w).preimage (hm i j)
  have h2 : IsClosed {x | Valued.v (m x 1 0) ≤ AdelicLevel.idealBound (𝓞 L) N w} :=
    (AdelicLevel.isClosed_setOf_valued_le_idealBound (K := L) w N).preimage (hm 1 0)
  have h3 : IsClosed {x | Valued.v (m x 1 1 - 1) ≤ AdelicLevel.idealBound (𝓞 L) N w} :=
    (AdelicLevel.isClosed_setOf_valued_le_idealBound (K := L) w N).preimage
      ((hm 1 1).sub continuous_const)
  exact h1.inter (h2.inter h3)

private theorem isOpen_setOf_forall_isLocalLevelOne {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) {X : Type} [TopologicalSpace X]
    {ι : Type} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (m m' : X → (i : ι) → Fin 2 → Fin 2 → (w i).adicCompletion L)
    (hm : ∀ i a b, Continuous fun x => m x i a b) (hm' : ∀ i a b, Continuous fun x => m' x i a b) :
    IsOpen {x | ∀ i, IsLocalLevelOne L N (w i) (m x i) ∧ IsLocalLevelOne L N (w i) (m' x i)} := by
  simp only [Set.setOf_forall, Set.setOf_and]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_setOf_isLocalLevelOne hN (fun x => m x i) (hm i)).inter
      (isOpen_setOf_isLocalLevelOne hN (fun x => m' x i) (hm' i))

private theorem isClosed_setOf_forall_isLocalLevelOne (N : Ideal (𝓞 L)) {X : Type} [TopologicalSpace X]
    {ι : Type} (w : ι → HeightOneSpectrum (𝓞 L))
    (m m' : X → (i : ι) → Fin 2 → Fin 2 → (w i).adicCompletion L)
    (hm : ∀ i a b, Continuous fun x => m x i a b) (hm' : ∀ i a b, Continuous fun x => m' x i a b) :
    IsClosed {x | ∀ i, IsLocalLevelOne L N (w i) (m x i) ∧ IsLocalLevelOne L N (w i) (m' x i)} := by
  simp only [Set.setOf_forall, Set.setOf_and]
  exact isClosed_iInter fun i =>
    (isClosed_setOf_isLocalLevelOne N (fun x => m x i) (hm i)).inter
      (isClosed_setOf_isLocalLevelOne N (fun x => m' x i) (hm' i))

private def levelIndicator (N : Ideal (𝓞 L)) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ :=
  (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))).indicator
    fun _ => 1

private theorem isFinTestFactor_levelIndicator {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) :
    IsFinTestFactor L (levelIndicator (L := L) N) :=
  ⟨isLocallyConstant_indicator_one (AdelicLevel.isOpen_finiteLevelOne (𝓞 L) L (N := N) hN)
      (AdelicLevel.isClosed_finiteLevelOne (𝓞 L) L N),
    HasCompactSupport.intro (AdelicLevel.isCompact_finiteLevelOne (𝓞 L) L N)
      fun _ hg => Set.indicator_of_notMem hg _⟩

end LocalExtra

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

private theorem semiLocalHomeomorph_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    semiLocalHomeomorph K L v (semiLocalEval K L v a) w = AdelicLevel.finAdeleEval (𝓞 L) L w.1 a := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w' : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w'.1 a)) w =
    AdelicLevel.finAdeleEval (𝓞 L) L w.1 a
  rw [AlgEquiv.apply_symm_apply]

private def componentEntries (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) (w : v.Extension (𝓞 L)) :
    Fin 2 → Fin 2 → w.1.adicCompletion L :=
  fun i j => semiLocalHomeomorph K L v (m i j) w

private theorem componentEntries_semiLocalComponent (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (w : v.Extension (𝓞 L)) :
    componentEntries K L v (semiLocalComponent K L v h).val w =
      fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w.1 (h.val i j) := by
  funext i j
  exact semiLocalHomeomorph_semiLocalEval K L v (h.val i j) w

private theorem continuous_componentEntries_val (w : v.Extension (𝓞 L)) (i j : Fin 2) :
    Continuous fun γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => componentEntries K L v γ.val w i j :=
  (continuous_apply w).comp
    ((semiLocalHomeomorph K L v).continuous.comp (Units.continuous_val.matrix_elem i j))

private theorem continuous_componentEntries_inv (w : v.Extension (𝓞 L)) (i j : Fin 2) :
    Continuous fun γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      componentEntries K L v (γ⁻¹).val w i j :=
  (continuous_apply w).comp
    ((semiLocalHomeomorph K L v).continuous.comp (Units.continuous_coe_inv.matrix_elem i j))

private def semiLocalLevelSet (N : Ideal (𝓞 L)) : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  {γ | ∀ w : v.Extension (𝓞 L),
    IsLocalLevelOne L N w.1 (componentEntries K L v γ.val w) ∧
      IsLocalLevelOne L N w.1 (componentEntries K L v (γ⁻¹).val w)}

private theorem semiLocalComponent_mem_semiLocalLevelSet_iff (N : Ideal (𝓞 L))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalComponent K L v h ∈ semiLocalLevelSet K L v N ↔
      ∀ w : v.Extension (𝓞 L),
        (IsLocalLevelOne L N w.1 fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w.1 (h.val i j)) ∧
          IsLocalLevelOne L N w.1 fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w.1 ((h⁻¹).val i j) := by
  rw [semiLocalLevelSet, Set.mem_setOf_eq, ← map_inv]
  refine forall_congr' fun w => ?_
  rw [componentEntries_semiLocalComponent, componentEntries_semiLocalComponent]

private theorem isOpen_semiLocalLevelSet {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) : IsOpen (semiLocalLevelSet K L v N) := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  exact isOpen_setOf_forall_isLocalLevelOne hN (fun w : v.Extension (𝓞 L) => w.1)
    (fun (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) w => componentEntries K L v γ.val w)
    (fun (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) w => componentEntries K L v (γ⁻¹).val w)
    (fun w => continuous_componentEntries_val K L v w) (fun w => continuous_componentEntries_inv K L v w)

private theorem isClosed_semiLocalLevelSet (N : Ideal (𝓞 L)) : IsClosed (semiLocalLevelSet K L v N) :=
  isClosed_setOf_forall_isLocalLevelOne N (fun w : v.Extension (𝓞 L) => w.1)
    (fun (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) w => componentEntries K L v γ.val w)
    (fun (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) w => componentEntries K L v (γ⁻¹).val w)
    (fun w => continuous_componentEntries_val K L v w) (fun w => continuous_componentEntries_inv K L v w)

private theorem mem_semiLocalIntegers_of_forall (t : L ⊗[K] v.adicCompletion K)
    (ht : ∀ w : v.Extension (𝓞 L), semiLocalHomeomorph K L v t w ∈ w.1.adicCompletionIntegers L) :
    t ∈ semiLocalIntegers K L v := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
  exact ht

private theorem forall_of_mem_semiLocalIntegers (t : L ⊗[K] v.adicCompletion K) (ht : t ∈ semiLocalIntegers K L v)
    (w : v.Extension (𝓞 L)) : semiLocalHomeomorph K L v t w ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi] at ht
  exact ht w

private theorem semiLocalLevelSet_subset (N : Ideal (𝓞 L)) :
    semiLocalLevelSet K L v N ⊆ semiLocalIntegralSet K L v := by
  intro γ hγ
  show γ ∈ integralUnitsSet (semiLocalIntegers K L v)
  refine mem_integralUnitsSet.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · exact mem_semiLocalIntegers_of_forall K L v _ fun w => (hγ w).1.1 i j
  · exact mem_semiLocalIntegers_of_forall K L v _ fun w => (hγ w).2.1 i j

private theorem isCompact_semiLocalLevelSet (N : Ideal (𝓞 L)) : IsCompact (semiLocalLevelSet K L v N) :=
  (isCompact_semiLocalIntegralSet K L v).of_isClosed_subset (isClosed_semiLocalLevelSet K L v N)
    (semiLocalLevelSet_subset K L v N)

private theorem isSemiLocalTestFn_indicator_semiLocalLevelSet {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) :
    IsSemiLocalTestFn K L v ((semiLocalLevelSet K L v N).indicator fun _ => (1 : ℂ)) := by
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI : R1Space (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := T2Space.r1Space
  exact ⟨isLocallyConstant_indicator_one (isOpen_semiLocalLevelSet K L v hN)
      (isClosed_semiLocalLevelSet K L v N),
    HasCompactSupport.intro (isCompact_semiLocalLevelSet K L v N) fun _ hg => Set.indicator_of_notMem hg _⟩

end SemiLocal

section Cosets

open scoped Pointwise

private theorem isClosed_doubleCoset_of_isOpen {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (a : G) : IsClosed (DoubleCoset.doubleCoset a (U : Set G) U) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro b hb
  refine ⟨DoubleCoset.doubleCoset b (U : Set G) U, fun x hx hxa => hb ?_, (hU.mul_left : IsOpen (_ * (U : Set G))),
    DoubleCoset.mem_doubleCoset_self U U b⟩
  have hdis : ¬ Disjoint (DoubleCoset.doubleCoset a (U : Set G) U) (DoubleCoset.doubleCoset b (U : Set G) U) :=
    Set.not_disjoint_iff.mpr ⟨x, hxa, hx⟩
  rw [DoubleCoset.eq_of_not_disjoint hdis]
  exact DoubleCoset.mem_doubleCoset_self U U b

variable (L : Type) [Field L] [NumberField L]

private theorem isFinTestFactor_indicator_doubleCoset {N : Ideal (𝓞 L)} (hN : N ≠ ⊥)
    (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    IsFinTestFactor L
      ((DoubleCoset.doubleCoset a (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
          (AdelicLevel.finiteLevelOne (𝓞 L) L N)).indicator fun _ => (1 : ℂ)) := by
  have hopen : IsOpen (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :=
    AdelicLevel.isOpen_finiteLevelOne (𝓞 L) L hN
  have hcpt : IsCompact (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :=
    AdelicLevel.isCompact_finiteLevelOne (𝓞 L) L N
  refine ⟨isLocallyConstant_indicator_one (hopen.mul_left) (isClosed_doubleCoset_of_isOpen _ hopen a), ?_⟩
  exact HasCompactSupport.intro ((hcpt.mul isCompact_singleton).mul hcpt) fun _ hg => Set.indicator_of_notMem hg _

variable (K : Type) [Field K] [NumberField K] [Algebra K L] (v : HeightOneSpectrum (𝓞 K))

private def semiLocalDoubleCoset (N : Ideal (𝓞 L)) (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  semiLocalLevelSet K L v N * {γ} * semiLocalLevelSet K L v N

private theorem isOpen_semiLocalDoubleCoset
    {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsOpen (semiLocalDoubleCoset L K v N γ) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI hcm : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    (isTopologicalGroup_tensorGL K L (v.adicCompletion K)).toContinuousMul
  haveI : ContinuousConstSMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    ⟨fun c => (hcm.continuous_mul.comp (Continuous.prodMk continuous_const continuous_id) :)⟩
  exact (isOpen_semiLocalLevelSet K L v hN).mul_left

private theorem isCompact_semiLocalDoubleCoset (N : Ideal (𝓞 L)) (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsCompact (semiLocalDoubleCoset L K v N γ) := by
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  exact ((isCompact_semiLocalLevelSet K L v N).mul isCompact_singleton).mul
    (isCompact_semiLocalLevelSet K L v N)

private theorem isClosed_semiLocalDoubleCoset (N : Ideal (𝓞 L)) (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsClosed (semiLocalDoubleCoset L K v N γ) := by
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  exact (isCompact_semiLocalDoubleCoset L K v N γ).isClosed

private theorem isSemiLocalTestFn_indicator_semiLocalDoubleCoset {N : Ideal (𝓞 L)} (hN : N ≠ ⊥)
    (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsSemiLocalTestFn K L v ((semiLocalDoubleCoset L K v N γ).indicator fun _ => (1 : ℂ)) := by
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI : R1Space (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := T2Space.r1Space
  exact
    ⟨isLocallyConstant_indicator_one (isOpen_semiLocalDoubleCoset L K v hN γ)
        (isClosed_semiLocalDoubleCoset L K v N γ),
    HasCompactSupport.intro (isCompact_semiLocalDoubleCoset L K v N γ) fun _ hg => Set.indicator_of_notMem hg _⟩

private theorem semiLocalComponent_mem_semiLocalLevelSet {N : Ideal (𝓞 L)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N) : semiLocalComponent K L v u ∈ semiLocalLevelSet K L v N :=
  (semiLocalComponent_mem_semiLocalLevelSet_iff K L v N u).mpr fun w => (mem_finiteLevelOne_iff_forall u).mp hu w.1

private theorem semiLocalComponent_mem_semiLocalDoubleCoset
    {N : Ideal (𝓞 L)} {a h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hh : h ∈ DoubleCoset.doubleCoset a
      (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
      (AdelicLevel.finiteLevelOne (𝓞 L) L N)) :
    semiLocalComponent K L v h ∈ semiLocalDoubleCoset L K v N (semiLocalComponent K L v a) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hh
  rw [map_mul, map_mul]
  exact Set.mul_mem_mul (Set.mul_mem_mul (semiLocalComponent_mem_semiLocalLevelSet L K v hx) rfl)
    (semiLocalComponent_mem_semiLocalLevelSet L K v hy)

private theorem mul_mem_semiLocalIntegers {s t : L ⊗[K] v.adicCompletion K} (hs : s ∈ semiLocalIntegers K L v)
    (ht : t ∈ semiLocalIntegers K L v) : s * t ∈ semiLocalIntegers K L v := by
  refine mem_semiLocalIntegers_of_forall K L v _ fun w => ?_
  have hmul : semiLocalHomeomorph K L v (s * t) w = semiLocalHomeomorph K L v s w * semiLocalHomeomorph K L v t w := by
    show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (s * t) w = _
    rw [map_mul]
    rfl
  rw [hmul]
  exact mul_mem (forall_of_mem_semiLocalIntegers K L v s hs w) (forall_of_mem_semiLocalIntegers K L v t ht w)

private theorem add_mem_semiLocalIntegers {s t : L ⊗[K] v.adicCompletion K} (hs : s ∈ semiLocalIntegers K L v)
    (ht : t ∈ semiLocalIntegers K L v) : s + t ∈ semiLocalIntegers K L v := by
  refine mem_semiLocalIntegers_of_forall K L v _ fun w => ?_
  have hadd : semiLocalHomeomorph K L v (s + t) w = semiLocalHomeomorph K L v s w + semiLocalHomeomorph K L v t w := by
    show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (s + t) w = _
    rw [map_add]
    rfl
  rw [hadd]
  exact add_mem (forall_of_mem_semiLocalIntegers K L v s hs w) (forall_of_mem_semiLocalIntegers K L v t ht w)

private theorem matrix_mul_entries_mem {A B : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hA : ∀ i j, A i j ∈ semiLocalIntegers K L v) (hB : ∀ i j, B i j ∈ semiLocalIntegers K L v) (i j : Fin 2) :
    (A * B) i j ∈ semiLocalIntegers K L v := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem_semiLocalIntegers L K v (mul_mem_semiLocalIntegers L K v (hA i 0) (hB 0 j))
    (mul_mem_semiLocalIntegers L K v (hA i 1) (hB 1 j))

private theorem mul_mem_semiLocalIntegralSet {γ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hγ : γ ∈ semiLocalIntegralSet K L v) (hδ : δ ∈ semiLocalIntegralSet K L v) :
    γ * δ ∈ semiLocalIntegralSet K L v := by
  have hγ' := mem_integralUnitsSet.mp hγ
  have hδ' := mem_integralUnitsSet.mp hδ
  refine mem_integralUnitsSet.mpr ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]
    exact matrix_mul_entries_mem L K v hγ'.1 hδ'.1 i j
  · rw [mul_inv_rev, Units.val_mul]
    exact matrix_mul_entries_mem L K v hδ'.2 hγ'.2 i j

private theorem semiLocalComponent_mem_semiLocalIntegralSet_of_mem_doubleCoset {N : Ideal (𝓞 L)}
    {a h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hh : h ∈ DoubleCoset.doubleCoset a
      (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
      (AdelicLevel.finiteLevelOne (𝓞 L) L N))
    (ha : semiLocalComponent K L v a ∈ semiLocalIntegralSet K L v) :
    semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v := by
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hh
  rw [map_mul, map_mul]
  exact mul_mem_semiLocalIntegralSet L K v
    (mul_mem_semiLocalIntegralSet L K v
      (semiLocalLevelSet_subset K L v N (semiLocalComponent_mem_semiLocalLevelSet L K v hx)) ha)
    (semiLocalLevelSet_subset K L v N (semiLocalComponent_mem_semiLocalLevelSet L K v hy))

end Cosets

section Converse

open scoped Pointwise

variable (L : Type) [Field L] [NumberField L]

private theorem isLocalLevelOne_one (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L)) :
    IsLocalLevelOne L N w ((1 : GL (Fin 2) (w.adicCompletion L)).val) := by
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · rw [Units.val_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne hij]; exact zero_mem _
  · rw [Units.val_one, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_zero]; exact zero_le'
  · rw [Units.val_one, Matrix.one_apply_eq, sub_self, map_zero]; exact zero_le'

private theorem local_mul_entries_mem (w : HeightOneSpectrum (𝓞 L)) {A B : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)}
    (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers L) (hB : ∀ i j, B i j ∈ w.adicCompletionIntegers L) (i j : Fin 2) :
    (A * B) i j ∈ w.adicCompletionIntegers L := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (mul_mem (hA i 0) (hB 0 j)) (mul_mem (hA i 1) (hB 1 j))

variable (K : Type) [Field K] [NumberField K] [Algebra K L] (v : HeightOneSpectrum (𝓞 K))

private def wEval (w : v.Extension (𝓞 L)) : L ⊗[K] v.adicCompletion K →+* w.1.adicCompletion L :=
  (Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toRingEquiv.toRingHom

private theorem wEval_apply (w : v.Extension (𝓞 L)) (x : L ⊗[K] v.adicCompletion K) :
    wEval L K v w x = semiLocalHomeomorph K L v x w :=
  rfl

private theorem wEval_injective (x y : L ⊗[K] v.adicCompletion K)
    (h : ∀ w : v.Extension (𝓞 L), wEval L K v w x = wEval L K v w y) :
    x = y :=
  (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).injective (funext h)

private def wComp
    (w : v.Extension (𝓞 L)) : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L) :=
  Matrix.GeneralLinearGroup.map (wEval L K v w)

private theorem wComp_val (w : v.Extension (𝓞 L)) (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (wComp L K v w γ).val = componentEntries K L v γ.val w :=
  rfl

private theorem wComp_inv_val (w : v.Extension (𝓞 L)) (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ((wComp L K v w γ)⁻¹).val = componentEntries K L v (γ⁻¹).val w := by
  rw [← map_inv]
  rfl

private theorem semiLocal_gl_ext {γ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (h : ∀ w : v.Extension (𝓞 L), wComp L K v w γ = wComp L K v w δ) : γ = δ := by
  refine Units.ext (Matrix.ext fun i j => wEval_injective L K v _ _ fun w => ?_)
  have hw := congrArg (fun x : GL (Fin 2) (w.1.adicCompletion L) => x.val i j) (h w)
  exact hw

private theorem wComp_semiLocalComponent (w : v.Extension (𝓞 L)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    wComp L K v w (semiLocalComponent K L v h) = AdelicLevel.finComponent (𝓞 L) L w.1 h := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := congrFun (congrFun (componentEntries_semiLocalComponent K L v h w) i) j
  exact this

private theorem isLocalLevelOne_wComp_of_mem {N : Ideal (𝓞 L)} {γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hγ : γ ∈ semiLocalLevelSet K L v N) (w : v.Extension (𝓞 L)) :
    IsLocalLevelOne L N w.1 (wComp L K v w γ).val ∧ IsLocalLevelOne L N w.1 ((wComp L K v w γ)⁻¹).val := by
  rw [wComp_val, wComp_inv_val]
  exact hγ w

private theorem wComp_entries_mem_of_mem
    {γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)} (hγ : γ ∈ semiLocalIntegralSet K L v)
    (w : v.Extension (𝓞 L)) :
    (∀ i j, (wComp L K v w γ).val i j ∈ w.1.adicCompletionIntegers L) ∧
      ∀ i j, ((wComp L K v w γ)⁻¹).val i j ∈ w.1.adicCompletionIntegers L := by
  have hγ' := mem_integralUnitsSet.mp hγ
  rw [wComp_val, wComp_inv_val]
  exact ⟨fun i j => forall_of_mem_semiLocalIntegers K L v _ (hγ'.1 i j) w,
    fun i j => forall_of_mem_semiLocalIntegers K L v _ (hγ'.2 i j) w⟩

end Converse

section ConverseMain

open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def toExt (w : HeightOneSpectrum (𝓞 L)) : (w.under (𝓞 K)).Extension (𝓞 L) :=
  ⟨w, rfl⟩

private theorem mem_doubleCoset_of_forall_semiLocalComponent_mem
    {N : Ideal (𝓞 L)} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hmax : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ w : v.Extension (𝓞 L), AdelicLevel.idealBound (𝓞 L) N w.1 = 1)
    {a h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → semiLocalComponent K L v a ∈ semiLocalIntegralSet K L v)
    (hh : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v)
    (hS : ∀ v ∈ S, semiLocalComponent K L v h ∈ semiLocalDoubleCoset L K v N (semiLocalComponent K L v a)) :
    h ∈ DoubleCoset.doubleCoset a
      (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
      (AdelicLevel.finiteLevelOne (𝓞 L) L N) := by
  classical

  have hS' : ∀ v ∈ S, ∃ γ ∈ semiLocalLevelSet K L v N, ∃ γ' ∈ semiLocalLevelSet K L v N,
      semiLocalComponent K L v h = γ * semiLocalComponent K L v a * γ' := by
    intro v hv
    obtain ⟨x, hx, γ', hγ', hxe⟩ := Set.mem_mul.mp (hS v hv)
    obtain ⟨γ, hγ, a', ha', hxa⟩ := Set.mem_mul.mp hx
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    exact ⟨γ, hγ, γ', hγ', by rw [← hxe, ← hxa]⟩
  choose! γ hγ γ' hγ' hγeq using hS'

  let g : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L) := fun w =>
    if _hv : w.under (𝓞 K) ∈ S then wComp L K _ (toExt w) (γ (w.under (𝓞 K)))
    else AdelicLevel.finComponent (𝓞 L) L w h * (AdelicLevel.finComponent (𝓞 L) L w a)⁻¹
  let g' : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L) := fun w =>
    if _hv : w.under (𝓞 K) ∈ S then wComp L K _ (toExt w) (γ' (w.under (𝓞 K))) else 1

  have hg : ∀ w, IsLocalLevelOne L N w (g w).val ∧ IsLocalLevelOne L N w ((g w)⁻¹).val := by
    intro w
    by_cases hv : w.under (𝓞 K) ∈ S
    · simp only [g, dif_pos hv]
      exact isLocalLevelOne_wComp_of_mem L K _ (hγ _ hv) (toExt w)
    · simp only [g, dif_neg hv]
      have hmax' := hmax _ hv (toExt w)
      have hhw := wComp_entries_mem_of_mem L K _ (hh _ hv) (toExt w)
      have haw := wComp_entries_mem_of_mem L K _ (ha _ hv) (toExt w)
      rw [wComp_semiLocalComponent] at hhw haw
      refine ⟨isLocalLevelOne_of_integral hmax' ?_, isLocalLevelOne_of_integral hmax' ?_⟩
      · rw [Units.val_mul]
        exact local_mul_entries_mem L w hhw.1 haw.2
      · rw [mul_inv_rev, inv_inv, Units.val_mul]
        exact local_mul_entries_mem L w haw.1 hhw.2
  have hg' : ∀ w, IsLocalLevelOne L N w (g' w).val ∧ IsLocalLevelOne L N w ((g' w)⁻¹).val := by
    intro w
    by_cases hv : w.under (𝓞 K) ∈ S
    · simp only [g', dif_pos hv]
      exact isLocalLevelOne_wComp_of_mem L K _ (hγ' _ hv) (toExt w)
    · simp only [g', dif_neg hv, inv_one]
      exact ⟨isLocalLevelOne_one L N w, isLocalLevelOne_one L N w⟩

  refine DoubleCoset.mem_doubleCoset.mpr ⟨Components.assembleGL g hg, Components.assembleGL_mem_finiteLevelOne g hg,
    Components.assembleGL g' hg', Components.assembleGL_mem_finiteLevelOne g' hg', ?_⟩
  refine Components.gl_ext_of_forall_finComponent fun w => ?_
  rw [map_mul, map_mul, Components.finComponent_assembleGL, Components.finComponent_assembleGL]
  by_cases hv : w.under (𝓞 K) ∈ S
  · simp only [g, g', dif_pos hv]
    have key := congrArg (wComp L K _ (toExt w)) (hγeq _ hv)
    rw [map_mul, map_mul, wComp_semiLocalComponent, wComp_semiLocalComponent] at key
    exact key
  · simp only [g, g', dif_neg hv, mul_one, inv_mul_cancel_right]

end ConverseMain

section Assembly

open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private abbrev finDoubleCoset (N : Ideal (𝓞 L)) (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :=
  DoubleCoset.doubleCoset a
    (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
    (AdelicLevel.finiteLevelOne (𝓞 L) L N)

private theorem mul_mem_finDoubleCoset_iff {N : Ideal (𝓞 L)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N) (a x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    u * x ∈ finDoubleCoset N a ↔ x ∈ finDoubleCoset N a := by
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, e⟩ := DoubleCoset.mem_doubleCoset.mp hx
    refine DoubleCoset.mem_doubleCoset.mpr ⟨u⁻¹ * y, (AdelicLevel.finiteLevelOne (𝓞 L) L N).mul_mem
      ((AdelicLevel.finiteLevelOne (𝓞 L) L N).inv_mem hu) hy, z, hz, ?_⟩
    calc x = u⁻¹ * (u * x) := by group
      _ = u⁻¹ * y * a * z := by rw [e]; group
  · intro hx
    obtain ⟨y, hy, z, hz, e⟩ := DoubleCoset.mem_doubleCoset.mp hx
    refine DoubleCoset.mem_doubleCoset.mpr
      ⟨u * y, (AdelicLevel.finiteLevelOne (𝓞 L) L N).mul_mem hu hy, z, hz, ?_⟩
    rw [e]; group

private theorem mem_finDoubleCoset_mul_iff {N : Ideal (𝓞 L)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N) (a x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    x * u ∈ finDoubleCoset N a ↔ x ∈ finDoubleCoset N a := by
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, e⟩ := DoubleCoset.mem_doubleCoset.mp hx
    refine DoubleCoset.mem_doubleCoset.mpr ⟨y, hy, z * u⁻¹, (AdelicLevel.finiteLevelOne (𝓞 L) L N).mul_mem
      hz ((AdelicLevel.finiteLevelOne (𝓞 L) L N).inv_mem hu), ?_⟩
    calc x = x * u * u⁻¹ := by group
      _ = y * a * (z * u⁻¹) := by rw [e]; group
  · intro hx
    obtain ⟨y, hy, z, hz, e⟩ := DoubleCoset.mem_doubleCoset.mp hx
    refine DoubleCoset.mem_doubleCoset.mpr
      ⟨y, hy, z * u, (AdelicLevel.finiteLevelOne (𝓞 L) L N).mul_mem hz hu, ?_⟩
    rw [e]; group

private def piece (N : Ideal (𝓞 L)) (θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (g : GL (Fin 2) (AdeleRing (𝓞 L) L)) : ℂ :=
  θa (AdelicLevel.glArch (𝓞 L) L g) *
    (finDoubleCoset N a).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 L) L g)

private theorem indicator_finDoubleCoset_eq_prod {N : Ideal (𝓞 L)} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hmax : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ w : v.Extension (𝓞 L), AdelicLevel.idealBound (𝓞 L) N w.1 = 1)
    {a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → semiLocalComponent K L v a ∈ semiLocalIntegralSet K L v)
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (hh : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) :
    (finDoubleCoset N a).indicator (fun _ => (1 : ℂ)) h =
      ∏ v ∈ S, (semiLocalDoubleCoset L K v N (semiLocalComponent K L v a)).indicator (fun _ => (1 : ℂ))
        (semiLocalComponent K L v h) := by
  by_cases hmem : h ∈ finDoubleCoset N a
  · rw [Set.indicator_of_mem hmem]
    symm
    refine Finset.prod_eq_one fun v _ => ?_
    rw [Set.indicator_of_mem (semiLocalComponent_mem_semiLocalDoubleCoset L K v hmem)]
  · rw [Set.indicator_of_notMem hmem]
    symm
    by_contra hne
    apply hmem
    refine mem_doubleCoset_of_forall_semiLocalComponent_mem S hmax ha hh fun v hv => ?_
    by_contra hv'
    exact hne (Finset.prod_eq_zero hv (Set.indicator_of_notMem hv' _))

private theorem isSemiLocalFactorization_piece {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hmax : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ w : v.Extension (𝓞 L), AdelicLevel.idealBound (𝓞 L) N w.1 = 1)
    {θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} (hθa : IsArchTestFactor L θa)
    {a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → semiLocalComponent K L v a ∈ semiLocalIntegralSet K L v) :
    IsSemiLocalFactorization K L S (piece N θa a) θa ((finDoubleCoset N a).indicator fun _ => (1 : ℂ))
      fun v => (semiLocalDoubleCoset L K v N (semiLocalComponent K L v a)).indicator fun _ => (1 : ℂ) := by
  refine ⟨hθa, isFinTestFactor_indicator_doubleCoset L hN a,
    fun v _ => isSemiLocalTestFn_indicator_semiLocalDoubleCoset L K v hN _,
    fun h hh => indicator_finDoubleCoset_eq_prod S hmax ha h hh, fun h hh => ?_, fun g => rfl⟩
  obtain ⟨v, hv, hvh⟩ := hh
  apply Set.indicator_of_notMem
  intro hmem
  exact hvh (semiLocalComponent_mem_semiLocalIntegralSet_of_mem_doubleCoset L K v hmem (ha v hv))

private theorem isBiInvariantUnder_piece (N : Ideal (𝓞 L)) (θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    IsBiInvariantUnder L (AdelicLevel.levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (piece N θa a) := by
  intro u hu g
  obtain ⟨hu₁, hu₂⟩ := Subgroup.mem_inf.mp hu
  have harch : AdelicLevel.glArch (𝓞 L) L u = 1 := (mem_finiteAdelicGL2Subgroup_iff L u).mp hu₂
  have hfin : AdelicLevel.glFin (𝓞 L) L u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N :=
    (AdelicLevel.mem_levelOne_iff).mp hu₁
  constructor
  · simp only [piece, map_mul, harch, one_mul]
    by_cases hx : AdelicLevel.glFin (𝓞 L) L g ∈ finDoubleCoset N a
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((mul_mem_finDoubleCoset_iff hfin a _).mpr hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun h' => hx ((mul_mem_finDoubleCoset_iff hfin a _).mp h'))]
  · simp only [piece, map_mul, harch, mul_one]
    by_cases hx : AdelicLevel.glFin (𝓞 L) L g ∈ finDoubleCoset N a
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((mem_finDoubleCoset_mul_iff hfin a _).mpr hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun h' => hx ((mem_finDoubleCoset_mul_iff hfin a _).mp h'))]

private theorem exists_finset_eq_sum_smul_piece {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hmax : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ w : v.Extension (𝓞 L), AdelicLevel.idealBound (𝓞 L) N w.1 = 1)
    {θ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} {θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    {θf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {θS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hθ : IsSemiLocalFactorization K L S θ θa θf θS)
    (hθf : ∀ u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N, ∀ x, θf (u * x) = θf x ∧ θf (x * u) = θf x) :
    ∃ s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)),
      (∀ a ∈ s, IsUnitFactorizableAbove K L (AdelicLevel.levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) S
        (piece N θa a)) ∧
      θ = ∑ a ∈ s, θf a • piece N θa a := by
  obtain ⟨hθa, hθfin, -, -, hvan, hprod⟩ := hθ
  obtain ⟨s₀, -, hsum⟩ := exists_finset_eq_sum_smul_indicator_doubleCoset
    (AdelicLevel.finiteLevelOne (𝓞 L) L N) (AdelicLevel.isOpen_finiteLevelOne (𝓞 L) L hN) θf hθfin.2
    (fun u hu x => (hθf u hu x).1) (fun u hu x => (hθf u hu x).2)
  refine ⟨s₀.filter fun a => θf a ≠ 0, fun a ha => ?_, ?_⟩
  · obtain ⟨-, ha0⟩ := Finset.mem_filter.mp ha

    have haint : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        semiLocalComponent K L v a ∈ semiLocalIntegralSet K L v := by
      intro v hv
      by_contra hcon
      exact ha0 (hvan a ⟨v, hv, hcon⟩)
    exact ⟨isBiInvariantUnder_piece N θa a, _, _, _, isSemiLocalFactorization_piece hN S hmax hθa haint⟩
  · funext g
    rw [hprod g, Finset.sum_apply]
    have hsum' := congrFun hsum (AdelicLevel.glFin (𝓞 L) L g)
    rw [Finset.sum_apply] at hsum'
    rw [hsum', Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, piece]
    split_ifs with ha0
    · ring
    · rw [not_not.mp ha0]
      ring

end Assembly

end LevelPieces.Pieces

namespace LevelPieces
namespace Split

open LevelPieces.Components LevelPieces.Pieces
open scoped Pointwise

section General

variable {L : Type} [Field L] [NumberField L]

private def assembleAdele' (x : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L)
    (hx : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, x w ∈ w.adicCompletionIntegers L) :
    FiniteAdeleRing (𝓞 L) L :=
  ⟨x, hx⟩

private def assembleMatrix' (m : ∀ w : HeightOneSpectrum (𝓞 L), Matrix (Fin 2) (Fin 2) (w.adicCompletion L))
    (hm : ∀ i j, ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, m w i j ∈ w.adicCompletionIntegers L) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  fun i j => assembleAdele' (fun w => m w i j) (hm i j)

private theorem mapMatrix_assembleMatrix'
    (m : ∀ w : HeightOneSpectrum (𝓞 L), Matrix (Fin 2) (Fin 2) (w.adicCompletion L))
    (hm : ∀ i j, ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, m w i j ∈ w.adicCompletionIntegers L)
    (w : HeightOneSpectrum (𝓞 L)) :
    (AdelicLevel.finAdeleEval (𝓞 L) L w).mapMatrix (assembleMatrix' m hm) = m w :=
  Matrix.ext fun _ _ => rfl

private def assembleGL' (g : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L))
    (hg : ∀ i j, ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, (g w).val i j ∈ w.adicCompletionIntegers L)
    (hg' : ∀ i j, ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ((g w)⁻¹).val i j ∈ w.adicCompletionIntegers L) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) where
  val := assembleMatrix' (fun w => (g w).val) hg
  inv := assembleMatrix' (fun w => ((g w)⁻¹).val) hg'
  val_inv := by
    refine matrix_ext_of_forall_mapMatrix fun w => ?_
    rw [map_mul, map_one, mapMatrix_assembleMatrix', mapMatrix_assembleMatrix']
    exact Units.mul_inv (g w)
  inv_val := by
    refine matrix_ext_of_forall_mapMatrix fun w => ?_
    rw [map_mul, map_one, mapMatrix_assembleMatrix', mapMatrix_assembleMatrix']
    exact Units.inv_mul (g w)

private theorem finComponent_assembleGL' (g : ∀ w : HeightOneSpectrum (𝓞 L), GL (Fin 2) (w.adicCompletion L))
    (hg : ∀ i j, ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, (g w).val i j ∈ w.adicCompletionIntegers L)
    (hg' : ∀ i j, ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ((g w)⁻¹).val i j ∈ w.adicCompletionIntegers L)
    (w : HeightOneSpectrum (𝓞 L)) : AdelicLevel.finComponent (𝓞 L) L w (assembleGL' g hg hg') = g w :=
  Units.ext (mapMatrix_assembleMatrix' (fun w => (g w).val) hg w)

private theorem eventually_entry_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      (AdelicLevel.finComponent (𝓞 L) L w a).val i j ∈ w.adicCompletionIntegers L :=
  (a.val i j).2

private theorem eventually_inv_entry_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ((AdelicLevel.finComponent (𝓞 L) L w a)⁻¹).val i j ∈ w.adicCompletionIntegers L := by
  refine (eventually_entry_mem a⁻¹ i j).mono fun w hw => ?_
  rw [← map_inv]
  exact hw

private theorem one_entry_mem (w : HeightOneSpectrum (𝓞 L)) (i j : Fin 2) :
    ((1 : GL (Fin 2) (w.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
      w.adicCompletionIntegers L := by
  rw [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

end General

section Split

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K) (v : HeightOneSpectrum (𝓞 K))

open scoped Classical in

private def vPartFamily (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (w : HeightOneSpectrum (𝓞 L)) :
    GL (Fin 2) (w.adicCompletion L) :=
  if w.under (𝓞 K) = v then AdelicLevel.finComponent (𝓞 L) L w a else 1

open scoped Classical in

private def vDropFamily (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (w : HeightOneSpectrum (𝓞 L)) :
    GL (Fin 2) (w.adicCompletion L) :=
  if w.under (𝓞 K) = v then 1 else AdelicLevel.finComponent (𝓞 L) L w a

private theorem vPartFamily_entry_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, (vPartFamily K v a w).val i j ∈ w.adicCompletionIntegers L := by
  have _ := ‹NumberField K›
  classical
  refine (eventually_entry_mem a i j).mono fun w hw => ?_
  unfold vPartFamily
  split_ifs
  · exact hw
  · exact one_entry_mem w i j

private theorem vPartFamily_inv_entry_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ((vPartFamily K v a w)⁻¹).val i j ∈ w.adicCompletionIntegers L := by
  have _ := ‹NumberField K›
  classical
  refine (eventually_inv_entry_mem a i j).mono fun w hw => ?_
  unfold vPartFamily
  split_ifs
  · exact hw
  · rw [inv_one]
    exact one_entry_mem w i j

private theorem vDropFamily_entry_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, (vDropFamily K v a w).val i j ∈ w.adicCompletionIntegers L := by
  have _ := ‹NumberField K›
  classical
  refine (eventually_entry_mem a i j).mono fun w hw => ?_
  unfold vDropFamily
  split_ifs
  · exact one_entry_mem w i j
  · exact hw

private theorem vDropFamily_inv_entry_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ((vDropFamily K v a w)⁻¹).val i j ∈ w.adicCompletionIntegers L := by
  have _ := ‹NumberField K›
  classical
  refine (eventually_inv_entry_mem a i j).mono fun w hw => ?_
  unfold vDropFamily
  split_ifs
  · rw [inv_one]
    exact one_entry_mem w i j
  · exact hw

private def vPart (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  assembleGL' (vPartFamily K v a) (vPartFamily_entry_mem K v a) (vPartFamily_inv_entry_mem K v a)

private def vDrop (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  assembleGL' (vDropFamily K v a) (vDropFamily_entry_mem K v a) (vDropFamily_inv_entry_mem K v a)

private theorem finComponent_vPart_of_under (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w.under (𝓞 K) = v) :
    AdelicLevel.finComponent (𝓞 L) L w (vPart K v a) = AdelicLevel.finComponent (𝓞 L) L w a := by
  classical
  rw [vPart, finComponent_assembleGL', vPartFamily, if_pos hw]

private theorem finComponent_vPart_of_ne (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w.under (𝓞 K) ≠ v) : AdelicLevel.finComponent (𝓞 L) L w (vPart K v a) = 1 := by
  classical
  rw [vPart, finComponent_assembleGL', vPartFamily, if_neg hw]

private theorem finComponent_vDrop_of_under (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w.under (𝓞 K) = v) : AdelicLevel.finComponent (𝓞 L) L w (vDrop K v a) = 1 := by
  classical
  rw [vDrop, finComponent_assembleGL', vDropFamily, if_pos hw]

private theorem finComponent_vDrop_of_ne (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w.under (𝓞 K) ≠ v) :
    AdelicLevel.finComponent (𝓞 L) L w (vDrop K v a) = AdelicLevel.finComponent (𝓞 L) L w a := by
  classical
  rw [vDrop, finComponent_assembleGL', vDropFamily, if_neg hw]

private theorem semiLocalComponent_vPart_self (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalComponent K L v (vPart K v a) = semiLocalComponent K L v a := by
  refine semiLocal_gl_ext L K v fun w => ?_
  rw [wComp_semiLocalComponent, wComp_semiLocalComponent, finComponent_vPart_of_under K v a w.2]

private theorem semiLocalComponent_vPart_of_ne
    (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {v' : HeightOneSpectrum (𝓞 K)}
    (hv' : v' ≠ v) : semiLocalComponent K L v' (vPart K v a) = 1 := by
  refine semiLocal_gl_ext L K v' fun w => ?_
  rw [wComp_semiLocalComponent, map_one, finComponent_vPart_of_ne K v a (by rw [w.2]; exact hv')]

private theorem semiLocalComponent_vDrop_self (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalComponent K L v (vDrop K v a) = 1 := by
  refine semiLocal_gl_ext L K v fun w => ?_
  rw [wComp_semiLocalComponent, map_one, finComponent_vDrop_of_under K v a w.2]

private theorem semiLocalComponent_vDrop_of_ne
    (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {v' : HeightOneSpectrum (𝓞 K)}
    (hv' : v' ≠ v) : semiLocalComponent K L v' (vDrop K v a) = semiLocalComponent K L v' a := by
  refine semiLocal_gl_ext L K v' fun w => ?_
  rw [wComp_semiLocalComponent, wComp_semiLocalComponent, finComponent_vDrop_of_ne K v a (by rw [w.2]; exact hv')]

private theorem vPart_mul_vDrop (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : vPart K v a * vDrop K v a = a := by
  classical
  refine gl_ext_of_forall_finComponent fun w => ?_
  rw [map_mul]
  by_cases hw : w.under (𝓞 K) = v
  · rw [finComponent_vPart_of_under K v a hw, finComponent_vDrop_of_under K v a hw, mul_one]
  · rw [finComponent_vPart_of_ne K v a hw, finComponent_vDrop_of_ne K v a hw, one_mul]

private theorem vPart_mul_comm_of_forall_under {x y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hy : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) = v → AdelicLevel.finComponent (𝓞 L) L w y = 1) :
    vPart K v x * y = y * vPart K v x := by
  classical
  refine gl_ext_of_forall_finComponent fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w.under (𝓞 K) = v
  · rw [hy w hw, mul_one, one_mul]
  · rw [finComponent_vPart_of_ne K v x hw, mul_one, one_mul]

private theorem vPart_mul_vDrop_comm (x y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    vPart K v x * vDrop K v y = vDrop K v y * vPart K v x :=
  vPart_mul_comm_of_forall_under K v fun _ hw => finComponent_vDrop_of_under K v y hw

private theorem semiLocalComponent_eq_one_iff_forall (y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalComponent K L v y = 1 ↔
      ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) = v → AdelicLevel.finComponent (𝓞 L) L w y = 1 := by
  constructor
  · intro h w hw
    have := congrArg (wComp L K v ⟨w, hw⟩) h
    rwa [wComp_semiLocalComponent, map_one] at this
  · intro h
    refine semiLocal_gl_ext L K v fun w => ?_
    rw [wComp_semiLocalComponent, map_one, h w.1 w.2]

private theorem vDrop_mul
    (x y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : vDrop K v (x * y) = vDrop K v x * vDrop K v y := by
  classical
  refine gl_ext_of_forall_finComponent fun w => ?_
  rw [map_mul]
  by_cases hw : w.under (𝓞 K) = v
  · rw [finComponent_vDrop_of_under K v _ hw, finComponent_vDrop_of_under K v _ hw,
      finComponent_vDrop_of_under K v _ hw, mul_one]
  · rw [finComponent_vDrop_of_ne K v _ hw, finComponent_vDrop_of_ne K v _ hw, finComponent_vDrop_of_ne K v _ hw,
      map_mul]

private theorem vDrop_vPart (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : vDrop K v (vPart K v a) = 1 := by
  classical
  refine gl_ext_of_forall_finComponent fun w => ?_
  rw [map_one]
  by_cases hw : w.under (𝓞 K) = v
  · exact finComponent_vDrop_of_under K v _ hw
  · rw [finComponent_vDrop_of_ne K v _ hw, finComponent_vPart_of_ne K v a hw]

private theorem vDrop_mem_finiteLevelOne {N : Ideal (𝓞 L)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N) : vDrop K v u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N := by
  classical
  rw [mem_finiteLevelOne_iff_forall] at hu ⊢
  intro w

  have hcomp : ∀ (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)),
      (fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w (x.val i j)) = (AdelicLevel.finComponent (𝓞 L) L w x).val :=
    fun _ => rfl
  rw [hcomp, hcomp, map_inv]
  by_cases hw : w.under (𝓞 K) = v
  · rw [finComponent_vDrop_of_under K v u hw, inv_one]
    exact ⟨isLocalLevelOne_one L N w, isLocalLevelOne_one L N w⟩
  · rw [finComponent_vDrop_of_ne K v u hw, ← map_inv]
    exact hu w

private theorem vDrop_mem_finiteLevelOne_of_mem {N : Ideal (𝓞 L)} (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    {b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hb : b ∈ finDoubleCoset N (vPart K v a)) :
    vDrop K v b ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N := by
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hb
  rw [vDrop_mul, vDrop_mul, vDrop_vPart, mul_one]
  exact (AdelicLevel.finiteLevelOne (𝓞 L) L N).mul_mem (vDrop_mem_finiteLevelOne K v hx)
    (vDrop_mem_finiteLevelOne K v hy)

private theorem vPart_eq_mul_inv (b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : vPart K v b = b * (vDrop K v b)⁻¹ :=
  eq_mul_inv_of_mul_eq (vPart_mul_vDrop K v b)

private theorem smul_finiteLevelOne_eq {N : Ideal (𝓞 L)} {b h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hh : h ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N) :
    (b * h) • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) =
      b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) := by
  rw [mul_smul, smul_coe_set hh]

private theorem smul_finDoubleCoset_eq {N : Ideal (𝓞 L)} {b h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hh : h ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N) (c : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    (b * h) • finDoubleCoset N c = b • finDoubleCoset N c := by
  rw [mul_smul]
  congr 1
  ext x
  simp only [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  exact mul_mem_finDoubleCoset_iff ((AdelicLevel.finiteLevelOne (𝓞 L) L N).inv_mem hh) c x

private theorem exists_pure_system {N : Ideal (𝓞 L)} (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) (hs₁ : ∀ b ∈ s, b ∈ finDoubleCoset N (vPart K v a))
    (hs₂ : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' →
      Disjoint (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
        (b' • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))) :
    ∃ s' : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)),
      (∀ b ∈ s', vDrop K v b = 1) ∧
      (∀ b ∈ s', b ∈ finDoubleCoset N (vPart K v a)) ∧
      (∀ b ∈ s', ∀ b' ∈ s', b ≠ b' →
        Disjoint (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
          (b' • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))) ∧
      (∀ x, ∑ b ∈ s', (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N :
          Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator (fun _ => (1 : ℂ)) x =
        ∑ b ∈ s, (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N :
          Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator (fun _ => (1 : ℂ)) x) ∧
      (∀ c x, ∑ b ∈ s', (b • finDoubleCoset N c).indicator (fun _ => (1 : ℂ)) x =
        ∑ b ∈ s, (b • finDoubleCoset N c).indicator (fun _ => (1 : ℂ)) x) := by
  classical

  have hU : ∀ b ∈ s, (vPart K v b) • (AdelicLevel.finiteLevelOne (𝓞 L) L N :
      Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) = b • (AdelicLevel.finiteLevelOne (𝓞 L) L N :
      Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) := fun b hb => by
    rw [vPart_eq_mul_inv K v b]
    exact smul_finiteLevelOne_eq
      ((AdelicLevel.finiteLevelOne (𝓞 L) L N).inv_mem (vDrop_mem_finiteLevelOne_of_mem K v a (hs₁ b hb)))
  have hD : ∀ b ∈ s, ∀ c, (vPart K v b) • finDoubleCoset N c = b • finDoubleCoset N c := fun b hb c => by
    rw [vPart_eq_mul_inv K v b]
    exact smul_finDoubleCoset_eq
      ((AdelicLevel.finiteLevelOne (𝓞 L) L N).inv_mem (vDrop_mem_finiteLevelOne_of_mem K v a (hs₁ b hb))) c

  have hinj : ∀ b ∈ s, ∀ b' ∈ s, vPart K v b = vPart K v b' → b = b' := by
    intro b hb b' hb' h
    by_contra hne
    have hdisj := hs₂ b hb b' hb' hne
    rw [← hU b hb, ← hU b' hb', h] at hdisj
    have hmem : vPart K v b' ∈ (vPart K v b') • (AdelicLevel.finiteLevelOne (𝓞 L) L N :
        Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :=
      ⟨1, (AdelicLevel.finiteLevelOne (𝓞 L) L N).one_mem, by simp⟩
    exact Set.disjoint_left.mp hdisj hmem hmem
  refine ⟨s.image (vPart K v), ?_, ?_, ?_, fun x => ?_, fun c x => ?_⟩
  · intro b hb
    obtain ⟨b₀, -, rfl⟩ := Finset.mem_image.mp hb
    exact vDrop_vPart K v b₀
  · intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    rw [vPart_eq_mul_inv K v b₀]
    exact (mem_finDoubleCoset_mul_iff
      ((AdelicLevel.finiteLevelOne (𝓞 L) L N).inv_mem (vDrop_mem_finiteLevelOne_of_mem K v a (hs₁ b₀ hb₀))) _ _).mpr
      (hs₁ b₀ hb₀)
  · intro b hb b' hb' hne
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨b₀', hb₀', rfl⟩ := Finset.mem_image.mp hb'
    rw [hU b₀ hb₀, hU b₀' hb₀']
    exact hs₂ b₀ hb₀ b₀' hb₀' fun h => hne (by rw [h])
  · rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun b hb => by rw [hU b hb]
  · rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun b hb => by rw [hD b hb c]

end Split

end LevelPieces.Split

namespace LevelPieces
namespace Part

open LevelPieces.Components LevelPieces.Pieces LevelPieces.Split
open scoped Pointwise

variable {L : Type} [Field L] [NumberField L]
variable (P : Set (HeightOneSpectrum (𝓞 L)))

open scoped Classical in
private def partFamily (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (w : HeightOneSpectrum (𝓞 L)) :
    GL (Fin 2) (w.adicCompletion L) :=
  if w ∈ P then AdelicLevel.finComponent (𝓞 L) L w a else 1

open scoped Classical in
private def dropFamily (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (w : HeightOneSpectrum (𝓞 L)) :
    GL (Fin 2) (w.adicCompletion L) :=
  if w ∈ P then 1 else AdelicLevel.finComponent (𝓞 L) L w a

private theorem partFamily_entry_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, (partFamily P a w).val i j ∈ w.adicCompletionIntegers L := by
  classical
  refine (eventually_entry_mem a i j).mono fun w hw => ?_
  unfold partFamily
  split_ifs
  · exact hw
  · exact one_entry_mem w i j

private theorem partFamily_inv_entry_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ((partFamily P a w)⁻¹).val i j ∈ w.adicCompletionIntegers L := by
  classical
  refine (eventually_inv_entry_mem a i j).mono fun w hw => ?_
  unfold partFamily
  split_ifs
  · exact hw
  · rw [inv_one]
    exact one_entry_mem w i j

private theorem dropFamily_entry_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, (dropFamily P a w).val i j ∈ w.adicCompletionIntegers L := by
  classical
  refine (eventually_entry_mem a i j).mono fun w hw => ?_
  unfold dropFamily
  split_ifs
  · exact one_entry_mem w i j
  · exact hw

private theorem dropFamily_inv_entry_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ((dropFamily P a w)⁻¹).val i j ∈ w.adicCompletionIntegers L := by
  classical
  refine (eventually_inv_entry_mem a i j).mono fun w hw => ?_
  unfold dropFamily
  split_ifs
  · rw [inv_one]
    exact one_entry_mem w i j
  · exact hw

private def partOn (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  assembleGL' (partFamily P a) (partFamily_entry_mem P a) (partFamily_inv_entry_mem P a)

private def dropOn (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  assembleGL' (dropFamily P a) (dropFamily_entry_mem P a) (dropFamily_inv_entry_mem P a)

private theorem finComponent_partOn_of_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ P) : AdelicLevel.finComponent (𝓞 L) L w (partOn P a) = AdelicLevel.finComponent (𝓞 L) L w a := by
  classical
  rw [partOn, finComponent_assembleGL', partFamily, if_pos hw]

private theorem finComponent_partOn_of_notMem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∉ P) : AdelicLevel.finComponent (𝓞 L) L w (partOn P a) = 1 := by
  classical
  rw [partOn, finComponent_assembleGL', partFamily, if_neg hw]

private theorem finComponent_dropOn_of_mem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ P) : AdelicLevel.finComponent (𝓞 L) L w (dropOn P a) = 1 := by
  classical
  rw [dropOn, finComponent_assembleGL', dropFamily, if_pos hw]

private theorem finComponent_dropOn_of_notMem (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∉ P) : AdelicLevel.finComponent (𝓞 L) L w (dropOn P a) = AdelicLevel.finComponent (𝓞 L) L w a := by
  classical
  rw [dropOn, finComponent_assembleGL', dropFamily, if_neg hw]

private def partHom : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) →* GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) where
  toFun := partOn P
  map_one' := by
    classical
    refine gl_ext_of_forall_finComponent fun w => ?_
    rw [map_one]
    by_cases hw : w ∈ P
    · rw [finComponent_partOn_of_mem P _ hw, map_one]
    · exact finComponent_partOn_of_notMem P _ hw
  map_mul' x y := by
    classical
    refine gl_ext_of_forall_finComponent fun w => ?_
    rw [map_mul]
    by_cases hw : w ∈ P
    · rw [finComponent_partOn_of_mem P _ hw, finComponent_partOn_of_mem P _ hw, finComponent_partOn_of_mem P _ hw,
        map_mul]
    · rw [finComponent_partOn_of_notMem P _ hw, finComponent_partOn_of_notMem P _ hw,
        finComponent_partOn_of_notMem P _ hw, mul_one]

private def dropHom : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) →* GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) where
  toFun := dropOn P
  map_one' := by
    classical
    refine gl_ext_of_forall_finComponent fun w => ?_
    rw [map_one]
    by_cases hw : w ∈ P
    · exact finComponent_dropOn_of_mem P _ hw
    · rw [finComponent_dropOn_of_notMem P _ hw, map_one]
  map_mul' x y := by
    classical
    refine gl_ext_of_forall_finComponent fun w => ?_
    rw [map_mul]
    by_cases hw : w ∈ P
    · rw [finComponent_dropOn_of_mem P _ hw, finComponent_dropOn_of_mem P _ hw, finComponent_dropOn_of_mem P _ hw,
        mul_one]
    · rw [finComponent_dropOn_of_notMem P _ hw, finComponent_dropOn_of_notMem P _ hw,
        finComponent_dropOn_of_notMem P _ hw, map_mul]

private theorem partHom_apply (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : partHom P a = partOn P a := rfl
private theorem dropHom_apply (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : dropHom P a = dropOn P a := rfl

private theorem partOn_mul (x y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : partOn P (x * y) = partOn P x * partOn P y :=
  (partHom P).map_mul x y
private theorem dropOn_mul (x y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : dropOn P (x * y) = dropOn P x * dropOn P y :=
  (dropHom P).map_mul x y
private theorem partOn_inv
    (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : partOn P x⁻¹ = (partOn P x)⁻¹ := (partHom P).map_inv x
private theorem dropOn_inv
    (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : dropOn P x⁻¹ = (dropOn P x)⁻¹ := (dropHom P).map_inv x

private theorem partOn_mul_dropOn (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : partOn P a * dropOn P a = a := by
  classical
  refine gl_ext_of_forall_finComponent fun w => ?_
  rw [map_mul]
  by_cases hw : w ∈ P
  · rw [finComponent_partOn_of_mem P a hw, finComponent_dropOn_of_mem P a hw, mul_one]
  · rw [finComponent_partOn_of_notMem P a hw, finComponent_dropOn_of_notMem P a hw, one_mul]

private def IsPure (b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Prop := dropOn P b = 1

private theorem isPure_partOn (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : IsPure P (partOn P a) := by
  classical
  refine gl_ext_of_forall_finComponent fun w => ?_
  rw [map_one]
  by_cases hw : w ∈ P
  · exact finComponent_dropOn_of_mem P _ hw
  · rw [finComponent_dropOn_of_notMem P _ hw, finComponent_partOn_of_notMem P a hw]

private theorem partOn_eq_self_of_isPure
    {b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hb : IsPure P b) : partOn P b = b := by
  conv_rhs => rw [← partOn_mul_dropOn P b, hb, mul_one]

private theorem partOn_partOn (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : partOn P (partOn P a) = partOn P a :=
  partOn_eq_self_of_isPure P (isPure_partOn P a)

private theorem partOn_dropOn (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : partOn P (dropOn P a) = 1 := by
  classical
  refine gl_ext_of_forall_finComponent fun w => ?_
  rw [map_one]
  by_cases hw : w ∈ P
  · rw [finComponent_partOn_of_mem P _ hw, finComponent_dropOn_of_mem P a hw]
  · exact finComponent_partOn_of_notMem P _ hw

private theorem dropOn_dropOn (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : dropOn P (dropOn P a) = dropOn P a := by
  classical
  refine gl_ext_of_forall_finComponent fun w => ?_
  by_cases hw : w ∈ P
  · rw [finComponent_dropOn_of_mem P _ hw, finComponent_dropOn_of_mem P a hw]
  · rw [finComponent_dropOn_of_notMem P _ hw]

private theorem isPure_mul_comm {b y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hb : IsPure P b) (hy : partOn P y = 1) :
    b * y = y * b := by
  classical
  refine gl_ext_of_forall_finComponent fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w ∈ P
  · have h1 : AdelicLevel.finComponent (𝓞 L) L w y = 1 := by
      rw [← finComponent_partOn_of_mem P y hw, hy, map_one]
    rw [h1, mul_one, one_mul]
  · have h1 : AdelicLevel.finComponent (𝓞 L) L w b = 1 := by
      rw [← finComponent_dropOn_of_notMem P b hw, hb, map_one]
    rw [h1, mul_one, one_mul]

private theorem partOn_mul_comm_dropOn (x y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    partOn P x * dropOn P y = dropOn P y * partOn P x :=
  isPure_mul_comm P (isPure_partOn P x) (partOn_dropOn P y)

private theorem partOn_mem_finiteLevelOne {N : Ideal (𝓞 L)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N) : partOn P u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N := by
  classical
  rw [mem_finiteLevelOne_iff_forall] at hu ⊢
  intro w
  have hcomp : ∀ (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)),
      (fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w (x.val i j)) = (AdelicLevel.finComponent (𝓞 L) L w x).val :=
    fun _ => rfl
  rw [hcomp, hcomp, map_inv]
  by_cases hw : w ∈ P
  · rw [finComponent_partOn_of_mem P u hw, ← map_inv]
    exact hu w
  · rw [finComponent_partOn_of_notMem P u hw, inv_one]
    exact ⟨isLocalLevelOne_one L N w, isLocalLevelOne_one L N w⟩

private theorem dropOn_mem_finiteLevelOne {N : Ideal (𝓞 L)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N) : dropOn P u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N := by
  classical
  rw [mem_finiteLevelOne_iff_forall] at hu ⊢
  intro w
  have hcomp : ∀ (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)),
      (fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w (x.val i j)) = (AdelicLevel.finComponent (𝓞 L) L w x).val :=
    fun _ => rfl
  rw [hcomp, hcomp, map_inv]
  by_cases hw : w ∈ P
  · rw [finComponent_dropOn_of_mem P u hw, inv_one]
    exact ⟨isLocalLevelOne_one L N w, isLocalLevelOne_one L N w⟩
  · rw [finComponent_dropOn_of_notMem P u hw, ← map_inv]
    exact hu w

section Split

variable {N : Ideal (𝓞 L)}

private theorem parts_mem_of_mem {a x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hx : x ∈ finDoubleCoset N a) :
    partOn P x ∈ finDoubleCoset N (partOn P a) ∧ dropOn P x ∈ finDoubleCoset N (dropOn P a) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  constructor
  · rw [partOn_mul, partOn_mul]
    exact DoubleCoset.mem_doubleCoset.mpr ⟨_, partOn_mem_finiteLevelOne P hu, _, partOn_mem_finiteLevelOne P hu', rfl⟩
  · rw [dropOn_mul, dropOn_mul]
    exact DoubleCoset.mem_doubleCoset.mpr ⟨_, dropOn_mem_finiteLevelOne P hu, _, dropOn_mem_finiteLevelOne P hu', rfl⟩

private theorem mem_of_parts_mem {a x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (h₁ : partOn P x ∈ finDoubleCoset N (partOn P a)) (h₂ : dropOn P x ∈ finDoubleCoset N (dropOn P a)) :
    x ∈ finDoubleCoset N a := by
  obtain ⟨u₁, hu₁, u₁', hu₁', hx₁⟩ := DoubleCoset.mem_doubleCoset.mp h₁
  obtain ⟨u₂, hu₂, u₂', hu₂', hx₂⟩ := DoubleCoset.mem_doubleCoset.mp h₂

  have hx₁' : partOn P x = partOn P u₁ * partOn P a * partOn P u₁' := by
    rw [← partOn_partOn P x, hx₁, partOn_mul, partOn_mul, partOn_partOn]
  have hx₂' : dropOn P x = dropOn P u₂ * dropOn P a * dropOn P u₂' := by
    rw [← dropOn_dropOn P x, hx₂, dropOn_mul, dropOn_mul, dropOn_dropOn]
  refine DoubleCoset.mem_doubleCoset.mpr ⟨partOn P u₁ * dropOn P u₂,
    (AdelicLevel.finiteLevelOne (𝓞 L) L N).mul_mem (partOn_mem_finiteLevelOne P hu₁) (dropOn_mem_finiteLevelOne P hu₂),
    partOn P u₁' * dropOn P u₂', (AdelicLevel.finiteLevelOne (𝓞 L) L N).mul_mem (partOn_mem_finiteLevelOne P hu₁')
      (dropOn_mem_finiteLevelOne P hu₂'), ?_⟩

  have h1 : ∀ c, dropOn P u₂ * (partOn P a * c) = partOn P a * (dropOn P u₂ * c) := fun c => by
    rw [← mul_assoc, ← partOn_mul_comm_dropOn, mul_assoc]
  have h2 : ∀ c, dropOn P u₂ * (partOn P u₁' * c) = partOn P u₁' * (dropOn P u₂ * c) := fun c => by
    rw [← mul_assoc, ← partOn_mul_comm_dropOn, mul_assoc]
  have h3 : ∀ c, dropOn P a * (partOn P u₁' * c) = partOn P u₁' * (dropOn P a * c) := fun c => by
    rw [← mul_assoc, ← partOn_mul_comm_dropOn, mul_assoc]
  rw [← partOn_mul_dropOn P a, ← partOn_mul_dropOn P x, hx₁', hx₂']
  simp only [mul_assoc]
  rw [h1, h3, h2]

private theorem mem_iff_parts_mem (a x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    x ∈ finDoubleCoset N a ↔ partOn P x ∈ finDoubleCoset N (partOn P a) ∧ dropOn P x ∈ finDoubleCoset N (dropOn P a) :=
  ⟨parts_mem_of_mem P, fun h => mem_of_parts_mem P h.1 h.2⟩

private theorem mem_smul_doubleCoset_dropOn_iff {a b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hb : IsPure P b)
    (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    x ∈ b • finDoubleCoset N (dropOn P a) ↔
      partOn P x ∈ b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) ∧
        dropOn P x ∈ finDoubleCoset N (dropOn P a) := by
  simp only [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  rw [mem_iff_parts_mem P, partOn_mul, dropOn_mul, partOn_inv, dropOn_inv, partOn_eq_self_of_isPure P hb,
    show dropOn P b = 1 from hb, inv_one, one_mul, partOn_dropOn, dropOn_dropOn]

  have h1 : ∀ y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
      y ∈ finDoubleCoset N 1 ↔
        y ∈ (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) := by
    intro y
    constructor
    · intro hy
      obtain ⟨u, hu, u', hu', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
      rw [mul_one]
      exact (AdelicLevel.finiteLevelOne (𝓞 L) L N).mul_mem hu hu'
    · intro hy
      exact DoubleCoset.mem_doubleCoset.mpr
        ⟨y, hy, 1, (AdelicLevel.finiteLevelOne (𝓞 L) L N).one_mem, by rw [mul_one, mul_one]⟩
  rw [h1]

private theorem indicator_doubleCoset_eq_sum (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    {s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))} (hpure : ∀ b ∈ s, IsPure P b)
    (hdec : ∀ y, (finDoubleCoset N (partOn P a)).indicator (fun _ => (1 : ℂ)) y =
      ∑ b ∈ s, (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator
        (fun _ => (1 : ℂ)) y)
    (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    (finDoubleCoset N a).indicator (fun _ => (1 : ℂ)) x =
      ∑ b ∈ s, (b • finDoubleCoset N (dropOn P a)).indicator (fun _ => (1 : ℂ)) x := by
  classical

  have hterm : ∀ b ∈ s, (b • finDoubleCoset N (dropOn P a)).indicator (fun _ => (1 : ℂ)) x =
      (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator
          (fun _ => (1 : ℂ)) (partOn P x) *
        (finDoubleCoset N (dropOn P a)).indicator (fun _ => (1 : ℂ)) (dropOn P x) := by
    intro b hb
    by_cases hx : x ∈ b • finDoubleCoset N (dropOn P a)
    · obtain ⟨h₁, h₂⟩ := (mem_smul_doubleCoset_dropOn_iff P (hpure b hb) x).mp hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem h₁, Set.indicator_of_mem h₂, one_mul]
    · rw [Set.indicator_of_notMem hx]
      by_cases h₁ :
          partOn P x ∈ b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
      · have h₂ : dropOn P x ∉ finDoubleCoset N (dropOn P a) :=
          fun h₂ => hx ((mem_smul_doubleCoset_dropOn_iff P (hpure b hb) x).mpr ⟨h₁, h₂⟩)
        rw [Set.indicator_of_notMem h₂, mul_zero]
      · rw [Set.indicator_of_notMem h₁, zero_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← hdec (partOn P x)]

  by_cases hx : x ∈ finDoubleCoset N a
  · obtain ⟨h₁, h₂⟩ := parts_mem_of_mem P hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem h₁, Set.indicator_of_mem h₂, one_mul]
  · rw [Set.indicator_of_notMem hx]
    by_cases h₁ : partOn P x ∈ finDoubleCoset N (partOn P a)
    · have h₂ : dropOn P x ∉ finDoubleCoset N (dropOn P a) := fun h₂ => hx (mem_of_parts_mem P h₁ h₂)
      rw [Set.indicator_of_notMem h₂, mul_zero]
    · rw [Set.indicator_of_notMem h₁, zero_mul]

end Split

end LevelPieces.Part

namespace LevelPieces
namespace Part

open LevelPieces.Components LevelPieces.Pieces LevelPieces.Split
open scoped Pointwise

variable {L : Type} [Field L] [NumberField L]
variable (P : Set (HeightOneSpectrum (𝓞 L)))

private theorem dropOn_partOn
    (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : dropOn P (partOn P a) = 1 := isPure_partOn P a

private theorem partOn_eq_mul_inv (b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : partOn P b = b * (dropOn P b)⁻¹ :=
  eq_mul_inv_of_mul_eq (partOn_mul_dropOn P b)

private theorem dropOn_mem_finiteLevelOne_of_mem {N : Ideal (𝓞 L)} (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    {b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hb : b ∈ finDoubleCoset N (partOn P a)) :
    dropOn P b ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N := by
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hb
  rw [dropOn_mul, dropOn_mul, dropOn_partOn, mul_one]
  exact (AdelicLevel.finiteLevelOne (𝓞 L) L N).mul_mem (dropOn_mem_finiteLevelOne P hx)
    (dropOn_mem_finiteLevelOne P hy)

private theorem exists_pure_system {N : Ideal (𝓞 L)} (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) (hs₁ : ∀ b ∈ s, b ∈ finDoubleCoset N (partOn P a))
    (hs₂ : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' →
      Disjoint (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
        (b' • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))) :
    ∃ s' : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)),
      (∀ b ∈ s', IsPure P b) ∧
      (∀ b ∈ s', b ∈ finDoubleCoset N (partOn P a)) ∧
      (∀ b ∈ s', ∀ b' ∈ s', b ≠ b' →
        Disjoint (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
          (b' • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))) ∧
      (∀ x, ∑ b ∈ s', (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N :
          Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator (fun _ => (1 : ℂ)) x =
        ∑ b ∈ s, (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N :
          Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator (fun _ => (1 : ℂ)) x) ∧
      (∀ c x, ∑ b ∈ s', (b • finDoubleCoset N c).indicator (fun _ => (1 : ℂ)) x =
        ∑ b ∈ s, (b • finDoubleCoset N c).indicator (fun _ => (1 : ℂ)) x) := by
  classical

  have hU : ∀ b ∈ s, (partOn P b) • (AdelicLevel.finiteLevelOne (𝓞 L) L N :
      Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) = b • (AdelicLevel.finiteLevelOne (𝓞 L) L N :
      Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) := fun b hb => by
    rw [partOn_eq_mul_inv P b]
    exact smul_finiteLevelOne_eq
      ((AdelicLevel.finiteLevelOne (𝓞 L) L N).inv_mem (dropOn_mem_finiteLevelOne_of_mem P a (hs₁ b hb)))
  have hD : ∀ b ∈ s, ∀ c, (partOn P b) • finDoubleCoset N c = b • finDoubleCoset N c := fun b hb c => by
    rw [partOn_eq_mul_inv P b]
    exact smul_finDoubleCoset_eq
      ((AdelicLevel.finiteLevelOne (𝓞 L) L N).inv_mem (dropOn_mem_finiteLevelOne_of_mem P a (hs₁ b hb))) c

  have hinj : ∀ b ∈ s, ∀ b' ∈ s, partOn P b = partOn P b' → b = b' := by
    intro b hb b' hb' h
    by_contra hne
    have hdisj := hs₂ b hb b' hb' hne
    rw [← hU b hb, ← hU b' hb', h] at hdisj
    have hmem : partOn P b' ∈ (partOn P b') • (AdelicLevel.finiteLevelOne (𝓞 L) L N :
        Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :=
      ⟨1, (AdelicLevel.finiteLevelOne (𝓞 L) L N).one_mem, by simp⟩
    exact Set.disjoint_left.mp hdisj hmem hmem
  refine ⟨s.image (partOn P), ?_, ?_, ?_, fun x => ?_, fun c x => ?_⟩
  · intro b hb
    obtain ⟨b₀, -, rfl⟩ := Finset.mem_image.mp hb
    exact isPure_partOn P b₀
  · intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    rw [partOn_eq_mul_inv P b₀]
    exact (mem_finDoubleCoset_mul_iff
      ((AdelicLevel.finiteLevelOne (𝓞 L) L N).inv_mem (dropOn_mem_finiteLevelOne_of_mem P a (hs₁ b₀ hb₀))) _ _).mpr
      (hs₁ b₀ hb₀)
  · intro b hb b' hb' hne
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨b₀', hb₀', rfl⟩ := Finset.mem_image.mp hb'
    rw [hU b₀ hb₀, hU b₀' hb₀']
    exact hs₂ b₀ hb₀ b₀' hb₀' fun h => hne (by rw [h])
  · rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun b hb => by rw [hU b hb]
  · rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun b hb => by rw [hD b hb c]

end LevelPieces.Part

namespace LevelPieces
namespace Descent

open LevelPieces.Components LevelPieces.Pieces LevelPieces.Split LevelPieces.Part
open scoped Pointwise

variable {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {N : Ideal (𝓞 L)}

private theorem partOn_singleton_eq
    (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : partOn {w} x = (AdelicDock.localEmbed (𝓞 L)
    L w) ((AdelicLevel.finComponent (𝓞 L) L w) x) := by
  refine gl_ext_of_forall_finComponent fun w' => ?_
  by_cases hw : w' = w
  · rw [hw, finComponent_partOn_of_mem {w} x (Set.mem_singleton w), AdelicDock.finComponent_localEmbed_self]
  · rw [finComponent_partOn_of_notMem {w} x (by simpa using hw), AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hw]

private theorem isPure_localEmbed
    (t : GL (Fin 2) (w.adicCompletion L)) : IsPure {w} ((AdelicDock.localEmbed (𝓞 L) L w) t) :=
    by
  refine gl_ext_of_forall_finComponent fun w' => ?_
  rw [map_one]
  by_cases hw : w' = w
  · rw [hw]
    exact finComponent_dropOn_of_mem {w} _ (Set.mem_singleton w)
  · rw [finComponent_dropOn_of_notMem {w} _ (by simpa using hw), AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hw]

private theorem localEmbed_comp_of_isPure {b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hb : IsPure {w} b) :
    (AdelicDock.localEmbed (𝓞 L) L w) ((AdelicLevel.finComponent (𝓞 L) L w) b) = b := by
  rw [← partOn_singleton_eq, partOn_eq_self_of_isPure {w} hb]

private theorem comp_mem_localLevelOne_of_mem {u : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hu : u ∈
    (AdelicLevel.finiteLevelOne (𝓞 L) L N)) : (AdelicLevel.finComponent (𝓞 L) L w) u ∈ (AdelicDock.localLevelOne (𝓞
      L) L w N) := by
  rw [← AdelicDock.localEmbed_mem_finiteLevelOne_iff, ← partOn_singleton_eq]
  exact partOn_mem_finiteLevelOne {w} hu

private theorem mem_finiteLevelOne_iff_parts (z : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    z ∈ (AdelicLevel.finiteLevelOne (𝓞 L) L N) ↔ partOn {w} z ∈ (AdelicLevel.finiteLevelOne (𝓞 L) L N) ∧
      dropOn {w} z ∈ (AdelicLevel.finiteLevelOne (𝓞 L) L N) :=
  ⟨fun hz => ⟨partOn_mem_finiteLevelOne {w} hz, dropOn_mem_finiteLevelOne {w} hz⟩,
    fun h => partOn_mul_dropOn {w} z ▸ ((AdelicLevel.finiteLevelOne (𝓞 L) L N)).mul_mem h.1 h.2⟩

private theorem mem_doubleCoset_one_iff (y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : y ∈ finDoubleCoset N 1 ↔
    y ∈ (AdelicLevel.finiteLevelOne (𝓞 L) L N) := by
  constructor
  · intro hy
    obtain ⟨u, hu, u', hu', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
    rw [mul_one]
    exact ((AdelicLevel.finiteLevelOne (𝓞 L) L N)).mul_mem hu hu'
  · intro hy
    exact DoubleCoset.mem_doubleCoset.mpr ⟨y, hy, 1, ((AdelicLevel.finiteLevelOne (𝓞 L) L N)).one_mem,
      by rw [mul_one, mul_one]⟩

private theorem localEmbed_mem_finDoubleCoset_iff (a t : GL (Fin 2) (w.adicCompletion L)) :
    (AdelicDock.localEmbed (𝓞 L) L w) t ∈ finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) a) ↔
      t ∈ HeckePair.doubleCoset (AdelicDock.localLevelOne (𝓞 L) L w N) a := by
  constructor
  · intro ht
    obtain ⟨u, hu, u', hu', he⟩ := DoubleCoset.mem_doubleCoset.mp ht
    have hparts := congrArg (partOn {w}) he
    rw [partOn_eq_self_of_isPure {w} (isPure_localEmbed w t), partOn_mul, partOn_mul,
      partOn_eq_self_of_isPure {w} (isPure_localEmbed w a), partOn_singleton_eq, partOn_singleton_eq, ← map_mul,
      ← map_mul] at hparts
    refine HeckePair.mem_doubleCoset_iff.mpr ⟨(AdelicLevel.finComponent (𝓞 L) L w) u,
      comp_mem_localLevelOne_of_mem w hu, (AdelicLevel.finComponent (𝓞 L) L w) u',
      comp_mem_localLevelOne_of_mem w hu', ?_⟩
    exact (AdelicDock.localEmbed_injective (𝓞 L) L w hparts).symm
  · intro ht
    obtain ⟨h, hh, h', hh', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp ht
    rw [map_mul, map_mul]
    exact DoubleCoset.mem_doubleCoset.mpr ⟨(AdelicDock.localEmbed (𝓞 L) L w) h,
      (AdelicDock.localEmbed_mem_finiteLevelOne_iff _ _ _ _).mpr hh, (AdelicDock.localEmbed (𝓞 L) L w) h',
      (AdelicDock.localEmbed_mem_finiteLevelOne_iff _ _ _ _).mpr hh', rfl⟩

private theorem mem_localEmbed_smul_iff
    (t : GL (Fin 2) (w.adicCompletion L)) (y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    y ∈ (AdelicDock.localEmbed (𝓞 L) L w) t • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2)
      (FiniteAdeleRing (𝓞 L) L))) ↔
      (AdelicLevel.finComponent (𝓞 L) L w) y ∈ t • ((AdelicDock.localLevelOne (𝓞 L) L w N) : Set (GL (Fin 2)
        (w.adicCompletion L))) ∧ dropOn {w} y ∈ (AdelicLevel.finiteLevelOne (𝓞 L) L N) := by
  simp only [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe]
  rw [mem_finiteLevelOne_iff_parts w, partOn_mul, dropOn_mul, partOn_inv, dropOn_inv,
    partOn_eq_self_of_isPure {w} (isPure_localEmbed w t),
      show dropOn {w} ((AdelicDock.localEmbed (𝓞 L) L w) t) = 1 from isPure_localEmbed w t,
    inv_one, one_mul, partOn_singleton_eq, ← map_inv, ← map_mul, AdelicDock.localEmbed_mem_finiteLevelOne_iff]

private theorem mem_finDoubleCoset_localEmbed_iff (a : GL (Fin 2) (w.adicCompletion L))
    (y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    y ∈ finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) a) ↔
      (AdelicLevel.finComponent (𝓞 L) L w) y ∈ HeckePair.doubleCoset (AdelicDock.localLevelOne (𝓞 L) L w N) a ∧
        dropOn {w} y ∈ (AdelicLevel.finiteLevelOne (𝓞 L) L N) := by
  rw [mem_iff_parts_mem {w}, partOn_eq_self_of_isPure {w} (isPure_localEmbed w a),
    show dropOn {w} ((AdelicDock.localEmbed (𝓞 L) L w) a) = 1 from isPure_localEmbed w a, mem_doubleCoset_one_iff,
      partOn_singleton_eq,
    localEmbed_mem_finDoubleCoset_iff]

section System

variable (a : GL (Fin 2) (w.adicCompletion L)) {s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))}
  (hpure : ∀ b ∈ s, IsPure {w} b) (hs₁ : ∀ b ∈ s, b ∈ finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) a))
  (hs₂ : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' →
    Disjoint (b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
      (b' • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))))
  (hdec : ∀ y, (finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) a)).indicator (fun _ => (1 : ℂ)) y =
    ∑ b ∈ s, (b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator
      (fun _ => (1 : ℂ)) y)

include hpure in

private theorem comp_inj : ∀ b ∈ s, ∀ b' ∈ s,
    (AdelicLevel.finComponent (𝓞 L) L w) b = (AdelicLevel.finComponent (𝓞 L) L w) b' → b = b' := by
  intro b hb b' hb' h
  rw [← localEmbed_comp_of_isPure w (hpure b hb), ← localEmbed_comp_of_isPure w (hpure b' hb'), h]

include hs₁ hpure in

private theorem comp_mem_doubleCoset {b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hb : b ∈ s) :
    (AdelicLevel.finComponent (𝓞 L) L w) b ∈ HeckePair.doubleCoset (AdelicDock.localLevelOne (𝓞 L) L w N) a := by
  have h := hs₁ b hb
  rw [← localEmbed_comp_of_isPure w (hpure b hb), localEmbed_mem_finDoubleCoset_iff] at h
  exact h

include hs₂ hpure in

private theorem comp_eq_of_mk_eq {b b' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hb : b ∈ s) (hb' : b' ∈ s)
    (h : (QuotientGroup.mk ((AdelicLevel.finComponent (𝓞 L) L w) b) : GL (Fin 2) (w.adicCompletion L) ⧸
      (AdelicDock.localLevelOne (𝓞 L) L w N)) = QuotientGroup.mk ((AdelicLevel.finComponent (𝓞 L) L w) b')) :
    (AdelicLevel.finComponent (𝓞 L) L w) b = (AdelicLevel.finComponent (𝓞 L) L w) b' := by
  by_contra hne
  have hbb' : b ≠ b' := fun e => hne (by rw [e])

  have h₁ : b ∈ b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) := ⟨1,
      ((AdelicLevel.finiteLevelOne (𝓞 L) L N)).one_mem, by simp⟩
  have h₂ : b ∈ b' • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) := by
    have h' := (mem_localEmbed_smul_iff w ((AdelicLevel.finComponent (𝓞 L) L w) b') b).mpr
      ⟨Set.mem_smul_set_iff_inv_smul_mem.mpr (QuotientGroup.eq.mp h.symm),
        by rw [show dropOn {w} b = 1 from hpure b hb]; exact ((AdelicLevel.finiteLevelOne (𝓞 L) L N)).one_mem⟩
    rwa [localEmbed_comp_of_isPure w (hpure b' hb')] at h'
  exact Set.disjoint_left.mp (hs₂ b hb b' hb' hbb') h₁ h₂

include hdec hpure in

private theorem exists_mem_comp_smul {t : GL (Fin 2) (w.adicCompletion L)} (ht : t ∈ HeckePair.doubleCoset
    (AdelicDock.localLevelOne (𝓞 L) L w N) a) :
    ∃ b ∈ s, t ∈ (AdelicLevel.finComponent (𝓞 L) L w) b • ((AdelicDock.localLevelOne (𝓞 L) L w N) : Set (GL (Fin 2)
      (w.adicCompletion L))) := by
  classical
  have hglobal : (AdelicDock.localEmbed (𝓞 L) L w) t ∈ finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) a) :=
      (localEmbed_mem_finDoubleCoset_iff w a t).mpr ht
  have hsum := hdec ((AdelicDock.localEmbed (𝓞 L) L w) t)
  rw [Set.indicator_of_mem hglobal] at hsum
  obtain ⟨b, hb, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [← hsum]; exact one_ne_zero)
  have hmem : (AdelicDock.localEmbed (𝓞 L) L w) t ∈ b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2)
      (FiniteAdeleRing (𝓞 L) L))) := by
    by_contra hcon
    exact hne (Set.indicator_of_notMem hcon _)
  refine ⟨b, hb, ?_⟩
  rw [← localEmbed_comp_of_isPure w (hpure b hb), mem_localEmbed_smul_iff,
    AdelicDock.finComponent_localEmbed_self] at hmem
  exact hmem.1

include hdec hpure in

private theorem hfin_of_system :
    (QuotientGroup.mk '' (((AdelicDock.localLevelOne (𝓞 L) L w N) : Set (GL (Fin 2) (w.adicCompletion L))) * {a}) :
      Set (GL (Fin 2) (w.adicCompletion L) ⧸ (AdelicDock.localLevelOne (𝓞 L) L w N))).Finite := by
  classical
  rw [← HeckePair.image_mk_doubleCoset]
  refine (s.image fun b => (QuotientGroup.mk ((AdelicLevel.finComponent (𝓞 L) L w) b) : GL (Fin 2) (w.adicCompletion
      L) ⧸ (AdelicDock.localLevelOne (𝓞 L) L w N))).finite_toSet.subset
    ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨b, hb, htb⟩ := exists_mem_comp_smul w a hpure hdec ht
  refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, hb, ?_⟩)
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe] at htb
  exact QuotientGroup.eq.mpr htb

include hpure in
open scoped Classical in

private theorem sum_eq_sum_comp (F : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) :
    ∑ b ∈ s, F b = ∑ t ∈ s.image (AdelicLevel.finComponent (𝓞 L) L w), F ((AdelicDock.localEmbed (𝓞 L) L w) t) := by
  classical
  rw [Finset.sum_image (comp_inj w hpure)]
  exact Finset.sum_congr rfl fun b hb => by rw [localEmbed_comp_of_isPure w (hpure b hb)]

end System

private theorem localLevelOne_eq_integralSubgroup (hmax : AdelicLevel.idealBound (𝓞 L) N w = 1) :
    (AdelicDock.localLevelOne (𝓞 L) L w N) = LocalGL2.integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion
      L) := by
  ext k
  rw [AdelicDock.mem_localLevelOne_iff, FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem Subtype.val_injective]

  have hrange : ∀ x : w.adicCompletion L,
      x ∈ Set.range (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) ↔
        x ∈ w.adicCompletionIntegers L := by
    intro x
    constructor
    · rintro ⟨r, rfl⟩
      exact r.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  simp only [hrange]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.integral, h₂.integral⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁, ?_, ?_⟩, ⟨h₂, ?_, ?_⟩⟩
    · rw [hmax]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h₁ 1 0)
    · rw [hmax]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (sub_mem (h₁ 1 1) (one_mem _))
    · rw [hmax]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h₂ 1 0)
    · rw [hmax]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (sub_mem (h₂ 1 1) (one_mem _))

end LevelPieces.Descent

section FiniteInclusion

open AutomorphicForm
p2m_open "NumberField IsDedekindDomain NumberField.AdelicLevel"

namespace LevelPieces
namespace FinIncl

variable (F : Type) [Field F] [NumberField F]

private def adelicFinGLIncl : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* AdelicGL2 (𝓞 F) F :=
  (Units.mapEquiv (adelicMatrixProdEquiv F).symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (1 : _ →* GL (Fin 2) (InfiniteAdeleRing F)) (MonoidHom.id _)

private theorem glArch_adelicFinGLIncl (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glArch (𝓞 F) F (adelicFinGLIncl F x) = 1 := by
  ext i j
  rfl

private theorem glFin_adelicFinGLIncl (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glFin (𝓞 F) F (adelicFinGLIncl F x) = x := by
  ext i j
  rfl

private theorem adelicFinGLIncl_mem {N : Ideal (𝓞 F)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hu : u ∈ finiteLevelOne (𝓞 F) F N) :
    adelicFinGLIncl F u ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, glFin_adelicFinGLIncl]
    exact hu
  · rw [mem_finiteAdelicGL2Subgroup_iff]
    exact glArch_adelicFinGLIncl F u

variable {F}

private theorem ext_of_glArch_glFin {a b : AdelicGL2 (𝓞 F) F} (hA : glArch (𝓞 F) F a = glArch (𝓞 F) F b)
    (hF : glFin (𝓞 F) F a = glFin (𝓞 F) F b) : a = b := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : (glArch (𝓞 F) F a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j =
      (glArch (𝓞 F) F b : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := by rw [hA]
  have h2 : (glFin (𝓞 F) F a : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j =
      (glFin (𝓞 F) F b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := by rw [hF]
  rw [glArch_apply, glArch_apply] at h1
  rw [glFin_apply, glFin_apply] at h2
  exact Prod.ext h1 h2

private theorem prod_apply_incl {θ : AdelicGL2 (𝓞 F) F → ℂ} {θa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    {θf : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hprod : ∀ g, θ g = θa (glArch (𝓞 F) F g) * θf (glFin (𝓞 F) F g))
    (ginf : GL (Fin 2) (InfiniteAdeleRing F)) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    θ (adelicArchGLIncl F ginf * adelicFinGLIncl F x) = θa ginf * θf x := by
  rw [hprod, map_mul, map_mul, glArch_adelicArchGLIncl, glArch_adelicFinGLIncl, glFin_adelicArchGLIncl,
    glFin_adelicFinGLIncl, mul_one, one_mul]

private theorem finFactor_biInvariant {N : Ideal (𝓞 F)} {θ : AdelicGL2 (𝓞 F) F → ℂ}
    {θa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {θf : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hθ : IsBiInvariantUnder F (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) θ)
    (hprod : ∀ g, θ g = θa (glArch (𝓞 F) F g) * θf (glFin (𝓞 F) F g))
    {ginf : GL (Fin 2) (InfiniteAdeleRing F)} (hne : θa ginf ≠ 0) :
    ∀ u ∈ finiteLevelOne (𝓞 F) F N, ∀ x, θf (u * x) = θf x ∧ θf (x * u) = θf x := by
  intro u hu x
  have hmem := adelicFinGLIncl_mem F hu
  obtain ⟨hl, hr⟩ := hθ (adelicFinGLIncl F u) hmem (adelicArchGLIncl F ginf * adelicFinGLIncl F x)
  constructor
  ·
    have h1 : adelicFinGLIncl F u * (adelicArchGLIncl F ginf * adelicFinGLIncl F x) =
        adelicArchGLIncl F ginf * adelicFinGLIncl F (u * x) := by
      refine ext_of_glArch_glFin ?_ ?_
      · simp only [map_mul, glArch_adelicArchGLIncl, glArch_adelicFinGLIncl, one_mul, mul_one]
      · simp only [map_mul, glFin_adelicArchGLIncl, glFin_adelicFinGLIncl, one_mul]
    rw [h1, prod_apply_incl hprod, prod_apply_incl hprod] at hl
    exact mul_left_cancel₀ hne hl
  · have h2 : adelicArchGLIncl F ginf * adelicFinGLIncl F x * adelicFinGLIncl F u =
        adelicArchGLIncl F ginf * adelicFinGLIncl F (x * u) := by
      rw [map_mul, mul_assoc]
    rw [h2, prod_apply_incl hprod, prod_apply_incl hprod] at hr
    exact mul_left_cancel₀ hne hr

end LevelPieces.FinIncl

end FiniteInclusion

namespace LevelPieces
namespace HeckeAct

open HeckePair
open scoped Pointwise

variable {G : Type*} [Group G] {U : Subgroup G} {R₀ : Type*} [CommRing R₀]

private def act (f : HeckeAlgebra U R₀) (u : G → R₀) (x : G) : R₀ :=
  ∑ᶠ c : G ⧸ U, (f : G → R₀) c.out * u (x * c.out)

private theorem support_actTerm_subset (f : HeckeAlgebra U R₀) (u : G → R₀) (x : G) :
    Function.support (fun c : G ⧸ U => (f : G → R₀) c.out * u (x * c.out))
      ⊆ QuotientGroup.mk '' Function.support (f : G → R₀) := by
  intro c hc
  rw [Function.mem_support] at hc
  exact ⟨c.out, left_ne_zero_of_mul hc, QuotientGroup.out_eq' c⟩

private theorem act_eq_sum (f : HeckeAlgebra U R₀) (u : G → R₀) (x : G) {T : Finset (G ⧸ U)}
    (hT : QuotientGroup.mk '' Function.support (f : G → R₀) ⊆ (T : Set (G ⧸ U))) :
    act f u x = ∑ c ∈ T, (f : G → R₀) c.out * u (x * c.out) :=
  finsum_eq_sum_of_support_subset _ ((support_actTerm_subset f u x).trans hT)

private def cosets (f : HeckeAlgebra U R₀) : Finset (G ⧸ U) := (finite_cosets f).toFinset

private theorem coe_cosets (f : HeckeAlgebra U R₀) :
    (cosets f : Set (G ⧸ U)) = QuotientGroup.mk '' Function.support (f : G → R₀) :=
  (finite_cosets f).coe_toFinset

private theorem act_eq_sum_cosets (f : HeckeAlgebra U R₀) (u : G → R₀) (x : G) :
    act f u x = ∑ c ∈ cosets f, (f : G → R₀) c.out * u (x * c.out) :=
  act_eq_sum f u x (coe_cosets f).ge

private theorem mk_mem_cosets_of_ne_zero (f : HeckeAlgebra U R₀) {y : G} (hy : (f : G → R₀) y ≠ 0) :
    (QuotientGroup.mk y : G ⧸ U) ∈ cosets f := by
  rw [← Finset.mem_coe, coe_cosets]
  exact ⟨y, hy, rfl⟩

private theorem convTerm_out (f g : HeckeAlgebra U R₀) (y : G) (d : G ⧸ U) :
    convTerm f g y d = (f : G → R₀) d.out * (g : G → R₀) (d.out⁻¹ * y) := by
  conv_lhs => rw [← QuotientGroup.out_eq' d]
  exact convTerm_mk f g y d.out

private theorem act_apply_mul (g : HeckeAlgebra U R₀) {u : G → R₀} (hu : ∀ k ∈ U, ∀ z, u (z * k) = u z) (x y : G)
    {W : Finset (G ⧸ U)} (hW : ∀ e ∈ cosets g, (QuotientGroup.mk (y * e.out) : G ⧸ U) ∈ W) :
    act g u (x * y) = ∑ c ∈ W, (g : G → R₀) (y⁻¹ * c.out) * u (x * c.out) := by
  classical
  rw [act_eq_sum_cosets]
  set φ : G ⧸ U → G ⧸ U := fun e => QuotientGroup.mk (y * e.out) with hφ
  have hinj : ∀ e ∈ cosets g, ∀ e' ∈ cosets g, φ e = φ e' → e = e' := by
    intro e _ e' _ h
    have h' : (QuotientGroup.mk e.out : G ⧸ U) = QuotientGroup.mk e'.out := by
      rw [hφ] at h
      rw [QuotientGroup.eq] at h ⊢
      simpa [mul_inv_rev, mul_assoc] using h
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h'
  have hterm : ∀ e ∈ cosets g,
      (g : G → R₀) (y⁻¹ * (φ e).out) * u (x * (φ e).out) = (g : G → R₀) e.out * u (x * y * e.out) := by
    intro e _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U (y * e.out)
    rw [hφ]
    dsimp only
    rw [hh, show y⁻¹ * (y * e.out * (h : G)) = e.out * h by group, apply_mul_right g h.2,
      show x * (y * e.out * (h : G)) = x * y * e.out * h by group, hu _ h.2]
  calc ∑ e ∈ cosets g, (g : G → R₀) e.out * u (x * y * e.out)
      = ∑ e ∈ cosets g, (g : G → R₀) (y⁻¹ * (φ e).out) * u (x * (φ e).out) :=
        Finset.sum_congr rfl fun e he => (hterm e he).symm
    _ = ∑ c ∈ (cosets g).image φ, (g : G → R₀) (y⁻¹ * c.out) * u (x * c.out) := by rw [Finset.sum_image hinj]
    _ = ∑ c ∈ W, (g : G → R₀) (y⁻¹ * c.out) * u (x * c.out) := by
        apply Finset.sum_subset
        · intro c hc
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
          exact hW e he
        · intro c _ hc
          by_contra hne
          apply hc
          have hg : (g : G → R₀) (y⁻¹ * c.out) ≠ 0 := left_ne_zero_of_mul hne
          refine Finset.mem_image.mpr ⟨QuotientGroup.mk (y⁻¹ * c.out), mk_mem_cosets_of_ne_zero g hg, ?_⟩
          obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U (y⁻¹ * c.out)
          rw [hφ]
          dsimp only
          rw [hh, show y * (y⁻¹ * c.out * (h : G)) = c.out * h by group, QuotientGroup.mk_mul_of_mem _ h.2,
            QuotientGroup.out_eq']

open scoped Classical in

private def mulCosets (f g : HeckeAlgebra U R₀) : Finset (G ⧸ U) :=
  (cosets f ×ˢ cosets g).image fun p => (QuotientGroup.mk (p.1.out * p.2.out) : G ⧸ U)

private theorem mk_mem_mulCosets (f g : HeckeAlgebra U R₀) {d e : G ⧸ U} (hd : d ∈ cosets f) (he : e ∈ cosets g) :
    (QuotientGroup.mk (d.out * e.out) : G ⧸ U) ∈ mulCosets f g := by
  classical
  unfold mulCosets
  exact Finset.mem_image.mpr ⟨(d, e), Finset.mem_product.mpr ⟨hd, he⟩, rfl⟩

private theorem support_mul_subset (f g : HeckeAlgebra U R₀) :
    QuotientGroup.mk '' Function.support ((f * g : HeckeAlgebra U R₀) : G → R₀)
      ⊆ (mulCosets f g : Set (G ⧸ U)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Function.mem_support, coe_mul, conv_eq_sum f g y (coe_cosets f).ge] at hy
  obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  rw [convTerm_out] at hne
  have hg : (g : G → R₀) (d.out⁻¹ * y) ≠ 0 := right_ne_zero_of_mul hne
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U (d.out⁻¹ * y)
  have hmem := mk_mem_mulCosets f g hd (mk_mem_cosets_of_ne_zero g hg)
  rw [hh, show d.out * (d.out⁻¹ * y * (h : G)) = y * h by group, QuotientGroup.mk_mul_of_mem _ h.2] at hmem
  exact Finset.mem_coe.mpr hmem

private theorem act_mul (f g : HeckeAlgebra U R₀) {u : G → R₀} (hu : ∀ k ∈ U, ∀ z, u (z * k) = u z) (x : G) :
    act (f * g) u x = act f (act g u) x := by
  have hR : act f (act g u) x = ∑ d ∈ cosets f,
      (f : G → R₀) d.out * ∑ c ∈ mulCosets f g, (g : G → R₀) (d.out⁻¹ * c.out) * u (x * c.out) := by
    rw [act_eq_sum_cosets f (act g u) x]
    exact Finset.sum_congr rfl fun d hd => by
      rw [act_apply_mul g hu x d.out fun e he => mk_mem_mulCosets f g hd he]
  rw [hR, act_eq_sum (f * g) u x (support_mul_subset f g)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [coe_mul, conv_eq_sum f g c.out (coe_cosets f).ge, Finset.sum_mul]
  exact Finset.sum_congr rfl fun d _ => by rw [convTerm_out, mul_assoc]

private theorem act_eq_sum_of_system (f : HeckeAlgebra U R₀) {u : G → R₀} (hu : ∀ k ∈ U, ∀ z, u (z * k) = u z) (x : G)
    {s : Finset G} (hinj : ∀ b ∈ s, ∀ b' ∈ s, (QuotientGroup.mk b : G ⧸ U) = QuotientGroup.mk b' → b = b')
    (hcov : ∀ y : G, (f : G → R₀) y ≠ 0 → ∃ b ∈ s, (QuotientGroup.mk y : G ⧸ U) = QuotientGroup.mk b) :
    act f u x = ∑ b ∈ s, (f : G → R₀) b * u (x * b) := by
  classical
  have hT : QuotientGroup.mk '' Function.support (f : G → R₀)
      ⊆ ((s.image (QuotientGroup.mk : G → G ⧸ U) : Finset (G ⧸ U)) : Set (G ⧸ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb, hyb⟩ := hcov y hy
    rw [Finset.coe_image]
    exact ⟨b, hb, hyb.symm⟩
  rw [act_eq_sum f u x hT, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U b
  rw [hh, apply_mul_right f h.2, ← mul_assoc, hu _ h.2]

private theorem act_heckeIndicator (a : G) (hfin : (QuotientGroup.mk '' ((U : Set G) * {a}) : Set (G ⧸ U)).Finite)
    {u : G → R₀} (hu : ∀ k ∈ U, ∀ z, u (z * k) = u z) (x : G) {s : Finset G} (hs : ∀ b ∈ s, b ∈ doubleCoset U a)
    (hinj : ∀ b ∈ s, ∀ b' ∈ s, (QuotientGroup.mk b : G ⧸ U) = QuotientGroup.mk b' → b = b')
    (hcov : ∀ y ∈ doubleCoset U a, ∃ b ∈ s, (QuotientGroup.mk y : G ⧸ U) = QuotientGroup.mk b) :
    act (heckeIndicator R₀ a hfin : HeckeAlgebra U R₀) u x = ∑ b ∈ s, u (x * b) := by
  rw [act_eq_sum_of_system _ hu x hinj]
  · exact Finset.sum_congr rfl fun b hb => by rw [heckeIndicator_apply_of_mem hfin (hs b hb), one_mul]
  · intro y hy
    refine hcov y ?_
    by_contra hyD
    exact hy (heckeIndicator_apply_of_notMem hfin hyD)

private theorem act_act_comm_of_mul_comm {f g : HeckeAlgebra U R₀} (hfg : f * g = g * f) {u : G → R₀}
    (hu : ∀ k ∈ U, ∀ z, u (z * k) = u z) : act f (act g u) = act g (act f u) := by
  funext x
  rw [← act_mul f g hu x, ← act_mul g f hu x, hfg]

end LevelPieces.HeckeAct

namespace LevelPieces
namespace LocalCommutation

open LevelPieces.Pieces LevelPieces.Split LevelPieces.Part LevelPieces.Descent LevelPieces.FinIncl LevelPieces.HeckeAct
open HeckePair
open scoped Pointwise

section Generic

variable {G : Type*} [Group G] {U : Subgroup G}

private theorem out_ne_zero_of_mem_cosets
    (f : HeckeAlgebra U ℂ) {e : G ⧸ U} (he : e ∈ cosets f) : (f : G → ℂ) e.out ≠ 0 := by
  have he' : e ∈ (QuotientGroup.mk '' Function.support (f : G → ℂ) : Set (G ⧸ U)) := by
    rw [← coe_cosets]
    exact Finset.mem_coe.mpr he
  obtain ⟨y, hy, rfl⟩ := he'
  have hmem : y⁻¹ * (QuotientGroup.mk y : G ⧸ U).out ∈ U := QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
  rw [← mul_inv_cancel_left y (QuotientGroup.mk y : G ⧸ U).out, apply_mul_right f hmem]
  exact hy

private theorem act_apply_mul_of_mem
    (f : HeckeAlgebra U ℂ) {u : G → ℂ} (hu : ∀ k ∈ U, ∀ z, u (z * k) = u z) (x : G) {k : G}
    (hk : k ∈ U) : act f u (x * k) = act f u x := by
  classical
  have hW : ∀ e ∈ cosets f, (QuotientGroup.mk (k * e.out) : G ⧸ U) ∈ cosets f := by
    intro e he
    apply mk_mem_cosets_of_ne_zero
    rw [apply_left_mul f hk]
    exact out_ne_zero_of_mem_cosets f he
  rw [act_apply_mul f hu x k hW, act_eq_sum_cosets]
  exact Finset.sum_congr rfl fun c _ => by rw [apply_left_mul f (U.inv_mem hk)]

private theorem act_right_inv (f : HeckeAlgebra U ℂ) {u : G → ℂ} (hu : ∀ k ∈ U, ∀ z, u (z * k) = u z) :
    ∀ k ∈ U, ∀ x, act f u (x * k) = act f u x :=
  fun _ hk x => act_apply_mul_of_mem f hu x hk

end Generic

variable {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {N : Ideal (𝓞 L)}

private theorem hecke_comm
    (hmax : AdelicLevel.idealBound (𝓞 L) N w = 1) (f₁ f₂ : HeckeAlgebra ((AdelicDock.localLevelOne (𝓞
    L) L w N)) ℂ) :
    f₁ * f₂ = f₂ * f₁ := by
  revert f₁ f₂
  rw [localLevelOne_eq_integralSubgroup w hmax]
  intro f₁ f₂
  exact LocalGL2.localHeckeMul_comm f₁ f₂

section Slice

variable (z : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L)

private def slice : GL (Fin 2) (w.adicCompletion L) →
    ℂ := fun t => z (g * adelicFinGLIncl L ((AdelicDock.localEmbed (𝓞 L) L w) t))

private theorem slice_apply (t : GL (Fin 2) (w.adicCompletion L)) : slice w z g t = z (g * adelicFinGLIncl L
    ((AdelicDock.localEmbed (𝓞 L) L w) t)) := rfl

variable {z} in
private theorem slice_right_inv
    (hz : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L, ∀ u ∈ (AdelicLevel.finiteLevelOne (𝓞 L) L N),
    z (x * adelicFinGLIncl L u) = z x) :
    ∀ k ∈ (AdelicDock.localLevelOne (𝓞 L) L w N), ∀ t, slice w z g (t * k) = slice w z g t := by
  intro k hk t
  rw [slice_apply, slice_apply, map_mul, map_mul, ← mul_assoc]
  exact hz _ _ ((AdelicDock.localEmbed_mem_finiteLevelOne_iff _ _ _ _).mpr hk)

end Slice

section Identify

variable (a : GL (Fin 2) (w.adicCompletion L)) {s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))}
  (hpure : ∀ b ∈ s, IsPure {w} b) (hs₁ : ∀ b ∈ s, b ∈ finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) a))
  (hs₂ : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' →
    Disjoint (b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
      (b' • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))))
  (hdec : ∀ y, (finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) a)).indicator (fun _ => (1 : ℂ)) y =
    ∑ b ∈ s, (b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator
      (fun _ => (1 : ℂ)) y)

include hpure hs₁ hs₂ hdec in

private theorem act_indicator_eq_sum (u : GL (Fin 2) (w.adicCompletion L) →
    ℂ) (hu : ∀ k ∈ (AdelicDock.localLevelOne (𝓞 L) L w N), ∀ t, u (t * k) = u t)
    (x : GL (Fin 2) (w.adicCompletion L)) :
    act (heckeIndicator ℂ a (hfin_of_system w a hpure hdec)) u x = ∑ b ∈ s,
      u (x * (AdelicLevel.finComponent (𝓞 L) L w) b) := by
  classical
  rw [act_heckeIndicator a (hfin_of_system w a hpure hdec) hu x (s := s.image (AdelicLevel.finComponent (𝓞 L) L w))
    ?_ ?_ ?_, Finset.sum_image (comp_inj w hpure)]
  · intro t ht
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
    exact comp_mem_doubleCoset w a hpure hs₁ hb
  · intro t ht t' ht' h
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp ht'
    exact comp_eq_of_mk_eq w hpure hs₂ hb hb' h
  · intro y hy
    obtain ⟨b, hb, hyb⟩ := exists_mem_comp_smul w a hpure hdec hy
    refine ⟨(AdelicLevel.finComponent (𝓞 L) L w) b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe] at hyb
    exact (QuotientGroup.eq.mpr hyb).symm

end Identify

section Commute

variable {z : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ}
  (hz : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L, ∀ u ∈ (AdelicLevel.finiteLevelOne (𝓞 L) L N),
      z (x * adelicFinGLIncl L u) = z x)
  (a c : GL (Fin 2) (w.adicCompletion L)) {s s' : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))}
  (hpure : ∀ b ∈ s, IsPure {w} b) (hs₁ : ∀ b ∈ s, b ∈ finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) a))
  (hs₂ : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' →
    Disjoint (b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
      (b' • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))))
  (hdec : ∀ y, (finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) a)).indicator (fun _ => (1 : ℂ)) y =
    ∑ b ∈ s, (b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator
      (fun _ => (1 : ℂ)) y)
  (hpure' : ∀ b ∈ s', IsPure {w} b) (hs₁' : ∀ b ∈ s', b ∈ finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) c))
  (hs₂' : ∀ b ∈ s', ∀ b' ∈ s', b ≠ b' →
    Disjoint (b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
      (b' • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))))
  (hdec' : ∀ y, (finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) c)).indicator (fun _ => (1 : ℂ)) y =
    ∑ b ∈ s', (b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator
      (fun _ => (1 : ℂ)) y)

include hz hpure hs₁ hs₂ hdec hpure' hs₁' hs₂' hdec' in

private theorem double_sum_eq_act_act (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    act (heckeIndicator ℂ a (hfin_of_system w a hpure hdec))
        (act (heckeIndicator ℂ c (hfin_of_system w c hpure' hdec')) (slice w z g)) 1 =
      ∑ b ∈ s, ∑ b' ∈ s', z (g * adelicFinGLIncl L b * adelicFinGLIncl L b') := by
  have hsl := slice_right_inv w g hz
  rw [act_indicator_eq_sum w a hpure hs₁ hs₂ hdec _ (act_right_inv _ hsl) 1]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [act_indicator_eq_sum w c hpure' hs₁' hs₂' hdec' _ hsl]
  refine Finset.sum_congr rfl fun b' hb' => ?_
  rw [slice_apply, one_mul, map_mul, localEmbed_comp_of_isPure w (hpure b hb),
    localEmbed_comp_of_isPure w (hpure' b' hb'), map_mul, mul_assoc]

include hz hpure hs₁ hs₂ hdec hpure' hs₁' hs₂' hdec' in

private theorem double_sum_comm (hmax : AdelicLevel.idealBound (𝓞 L) N w = 1) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    ∑ b ∈ s, ∑ b' ∈ s', z (g * adelicFinGLIncl L b * adelicFinGLIncl L b') =
      ∑ b' ∈ s', ∑ b ∈ s, z (g * adelicFinGLIncl L b' * adelicFinGLIncl L b) := by
  rw [← double_sum_eq_act_act w hz a c hpure hs₁ hs₂ hdec hpure' hs₁' hs₂' hdec' g,
    ← double_sum_eq_act_act w hz c a hpure' hs₁' hs₂' hdec' hpure hs₁ hs₂ hdec g]
  exact congrFun (act_act_comm_of_mul_comm (hecke_comm w hmax _ _) (slice_right_inv w g hz)) 1

end Commute

end LevelPieces.LocalCommutation

namespace LevelPieces
namespace CrossCommutation

open LevelPieces.Part LevelPieces.Descent LevelPieces.FinIncl

variable {L : Type} [Field L] [NumberField L]

private theorem partOn_singleton_eq_one_of_isPure {w w' : HeightOneSpectrum (𝓞 L)} (hww' : w ≠ w')
    {b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hb : IsPure ({w'} : Set (HeightOneSpectrum (𝓞 L))) b) :
    partOn ({w} : Set (HeightOneSpectrum (𝓞 L))) b = 1 := by
  rw [partOn_singleton_eq, ← localEmbed_comp_of_isPure w' hb, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hww',
    map_one]

private theorem mul_comm_of_isPure_of_isPure {w w' : HeightOneSpectrum (𝓞 L)} (hww' : w ≠ w')
    {b b' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hb : IsPure ({w} : Set (HeightOneSpectrum (𝓞 L))) b)
    (hb' : IsPure ({w'} : Set (HeightOneSpectrum (𝓞 L))) b') : b * b' = b' * b :=
  isPure_mul_comm _ hb (partOn_singleton_eq_one_of_isPure hww' hb')

private theorem double_sum_comm_of_ne {w w' : HeightOneSpectrum (𝓞 L)} (hww' : w ≠ w')
    (z : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    {s s' : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))}
    (hpure : ∀ b ∈ s, IsPure ({w} : Set (HeightOneSpectrum (𝓞 L))) b)
    (hpure' : ∀ b ∈ s', IsPure ({w'} : Set (HeightOneSpectrum (𝓞 L))) b) :
    ∑ b ∈ s, ∑ b' ∈ s', z (g * adelicFinGLIncl L b * adelicFinGLIncl L b') =
      ∑ b' ∈ s', ∑ b ∈ s, z (g * adelicFinGLIncl L b' * adelicFinGLIncl L b) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' hb' => Finset.sum_congr rfl fun b hb => ?_
  rw [mul_assoc, ← map_mul, mul_comm_of_isPure_of_isPure hww' (hpure b hb) (hpure' b' hb'), map_mul, ← mul_assoc]

end LevelPieces.CrossCommutation

namespace LevelPieces
namespace Badness

open LevelPieces.Components LevelPieces.Pieces LevelPieces.Split LevelPieces.Part

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def IsGoodAt
    (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Prop :=
  (IsLocalLevelOne L N w fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w (h.val i j)) ∧
    IsLocalLevelOne L N w fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w ((h⁻¹).val i j)

private theorem isGoodAt_iff
    (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    IsGoodAt N w h ↔
      IsLocalLevelOne L N w (AdelicLevel.finComponent (𝓞 L) L w h).val ∧
        IsLocalLevelOne L N w (AdelicLevel.finComponent (𝓞 L) L w h⁻¹).val :=
  Iff.rfl

private theorem isGoodAt_of_entries_mem (N : Ideal (𝓞 L)) {w : HeightOneSpectrum (𝓞 L)}
    (hb : AdelicLevel.idealBound (𝓞 L) N w = 1) {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (h₁ : ∀ i j, (AdelicLevel.finComponent (𝓞 L) L w h).val i j ∈ w.adicCompletionIntegers L)
    (h₂ : ∀ i j, ((AdelicLevel.finComponent (𝓞 L) L w h)⁻¹).val i j ∈ w.adicCompletionIntegers L) :
    IsGoodAt N w h := by
  rw [isGoodAt_iff, map_inv]
  exact ⟨isLocalLevelOne_of_integral hb h₁, isLocalLevelOne_of_integral hb h₂⟩

private theorem isGoodAt_of_finComponent_eq_one (N : Ideal (𝓞 L)) {w : HeightOneSpectrum (𝓞 L)}
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hw : AdelicLevel.finComponent (𝓞 L) L w h = 1) : IsGoodAt N w h := by
  rw [isGoodAt_iff, map_inv, hw, inv_one]
  exact ⟨isLocalLevelOne_one L N w, isLocalLevelOne_one L N w⟩

private theorem isGoodAt_congr
    (N : Ideal (𝓞 L)) {w : HeightOneSpectrum (𝓞 L)} {h h' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (e : AdelicLevel.finComponent (𝓞 L) L w h = AdelicLevel.finComponent (𝓞 L) L w h') :
    IsGoodAt N w h ↔ IsGoodAt N w h' := by
  rw [isGoodAt_iff, isGoodAt_iff, map_inv, map_inv, e]

private def badSet
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 L)) (r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    Set (HeightOneSpectrum (𝓞 L)) :=
  {w | w.under (𝓞 K) ∉ SK ∧ ¬ IsGoodAt N w r}

private theorem badSet_finite (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 L))
    (hmax : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      ∀ w : v.Extension (𝓞 L), AdelicLevel.idealBound (𝓞 L) N w.1 = 1)
    (r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : (badSet SK N r).Finite := by
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, w.under (𝓞 K) ∉ SK → IsGoodAt N w r := by
    have h₁ := Filter.eventually_all.mpr fun i : Fin 2 =>
      Filter.eventually_all.mpr fun j : Fin 2 => eventually_entry_mem r i j
    have h₂ := Filter.eventually_all.mpr fun i : Fin 2 =>
      Filter.eventually_all.mpr fun j : Fin 2 => eventually_inv_entry_mem r i j
    filter_upwards [h₁, h₂] with w hw₁ hw₂ hv
    exact isGoodAt_of_entries_mem N (hmax _ hv (toExt w) : AdelicLevel.idealBound (𝓞 L) N w = 1) hw₁ hw₂
  refine (Filter.eventually_cofinite.mp hev).subset fun w hw => ?_
  exact fun hgood => hw.2 (hgood hw.1)

private noncomputable def badFinset (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 L))
    (hmax : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      ∀ w : v.Extension (𝓞 L), AdelicLevel.idealBound (𝓞 L) N w.1 = 1)
    (r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Finset (HeightOneSpectrum (𝓞 L)) :=
  (badSet_finite SK N hmax r).toFinset

variable {SK : Finset (HeightOneSpectrum (𝓞 K))} {N : Ideal (𝓞 L)}
  (hmax : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → ∀ w : v.Extension (𝓞 L), AdelicLevel.idealBound (𝓞 L) N w.1 = 1)

private theorem mem_badFinset {r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ badFinset SK N hmax r ↔ w.under (𝓞 K) ∉ SK ∧ ¬ IsGoodAt N w r :=
  (badSet_finite SK N hmax r).mem_toFinset

open scoped Classical in

private theorem badFinset_dropOn (r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (w : HeightOneSpectrum (𝓞 L)) :
    badFinset SK N hmax (dropOn {w} r) = (badFinset SK N hmax r).erase w := by
  ext w'
  rw [Finset.mem_erase, mem_badFinset, mem_badFinset]
  by_cases hw : w' = w
  · rw [hw]
    have hg : IsGoodAt N w (dropOn {w} r) :=
      isGoodAt_of_finComponent_eq_one N (finComponent_dropOn_of_mem {w} r (Set.mem_singleton w))
    exact ⟨fun h => absurd hg h.2, fun h => absurd rfl h.1⟩
  · have e := finComponent_dropOn_of_notMem {w} r (fun h : w' ∈ ({w} : Set (HeightOneSpectrum (𝓞 L))) =>
      hw (Set.mem_singleton_iff.mp h))
    rw [isGoodAt_congr N e]
    exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩

open scoped Classical in
private theorem card_badFinset_dropOn_lt {r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ badFinset SK N hmax r) :
    (badFinset SK N hmax (dropOn {w} r)).card < (badFinset SK N hmax r).card := by
  rw [badFinset_dropOn]
  exact Finset.card_erase_lt_of_mem hw

private theorem semiLocalComponent_mem_of_badFinset_eq_empty {r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hr : badFinset SK N hmax r = ∅) :
    ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → semiLocalComponent K L v r ∈ semiLocalIntegralSet K L v := by
  intro v hv
  refine semiLocalLevelSet_subset K L v N ?_
  rw [semiLocalComponent_mem_semiLocalLevelSet_iff]
  intro w
  have hw : w.1 ∉ badFinset SK N hmax r := by
    rw [hr]
    exact Finset.notMem_empty _
  rw [mem_badFinset, not_and, not_not] at hw
  exact hw (by rw [w.2]; exact hv)

private theorem isUnitFactorizableAbove_piece_of_badFinset_eq_empty (hN : N ≠ ⊥)
    {θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} (hθa : IsArchTestFactor L θa)
    {r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hr : badFinset SK N hmax r = ∅) :
    IsUnitFactorizableAbove K L (AdelicLevel.levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK (piece N θa r) :=
  ⟨isBiInvariantUnder_piece N θa r, _, _, _,
    isSemiLocalFactorization_piece hN SK hmax hθa (semiLocalComponent_mem_of_badFinset_eq_empty hmax hr)⟩

private theorem exists_finset_eq_sum_smul_piece_of_factor (hN : N ≠ ⊥) (θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    {θf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ} (hθf : HasCompactSupport θf)
    (hbi : ∀ u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N, ∀ x, θf (u * x) = θf x ∧ θf (x * u) = θf x) :
    ∃ s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)),
      (fun g : GL (Fin 2) (AdeleRing (𝓞 L) L) =>
          θa (AdelicLevel.glArch (𝓞 L) L g) * θf (AdelicLevel.glFin (𝓞 L) L g)) =
        ∑ a ∈ s, θf a • piece N θa a := by
  obtain ⟨s, -, hsum⟩ := exists_finset_eq_sum_smul_indicator_doubleCoset
    (AdelicLevel.finiteLevelOne (𝓞 L) L N) (AdelicLevel.isOpen_finiteLevelOne (𝓞 L) L hN) θf hθf
    (fun u hu x => (hbi u hu x).1) (fun u hu x => (hbi u hu x).2)
  refine ⟨s, ?_⟩
  funext g
  have hsum' := congrFun hsum (AdelicLevel.glFin (𝓞 L) L g)
  rw [Finset.sum_apply] at hsum'
  rw [Finset.sum_apply, hsum', Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, piece]
  ring

end LevelPieces.Badness

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]

private theorem aux_map_algebraMap_ne_bot {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥ :=
  fun h => hNK ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).mp h)

private theorem aux_idealBound_map_eq_one_of_not_mem [NumberField K] [NumberField L] {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥)
    {SK : Finset (HeightOneSpectrum (𝓞 K))} (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK) :
    ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → ∀ w : v.Extension (𝓞 L),
      AdelicLevel.idealBound (𝓞 L) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) w.1 = 1 := by
  intro v hv w
  refine AdelicLevel.idealBound_eq_one_of_not_dvd (aux_map_algebraMap_ne_bot K L hNK) ?_
  intro hdvd
  apply hv
  apply hNS
  rw [Ideal.dvd_iff_le] at hdvd ⊢
  rw [← w.2, HeightOneSpectrum.under_asIdeal, Ideal.under_def]
  exact Ideal.map_le_iff_le_comap.mp hdvd

end

section ContinuityContext

open AutomorphicForm.CuspidalConstituent

section ConstituentContinuity

variable (F : Type) [Field F] [NumberField F]

private theorem aux_continuous_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, hcont, -⟩
    exact hcont
  · exact continuous_zero
  · intro x y _ _ hx hy
    exact hx.add hy
  · intro c x _ hx
    exact hx.const_smul c

private theorem aux_continuous_of_mem_of_isCuspConstituent (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hV : IsCuspConstituent F pins ξ V)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ V) : Continuous φ :=
  aux_continuous_of_mem_cuspKFiniteSubmodule F pins ξ (hV.1.le hφ)

end ConstituentContinuity

end ContinuityContext

section CosetSystems

open scoped Pointwise

namespace LevelPieces

variable {G : Type*} [Group G]

private theorem mem_smul_coset_self (H : Subgroup G) (b : G) : b ∈ b • (H : Set G) := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_mul_cancel]
  exact H.one_mem

private theorem mem_smul_coset_iff (H : Subgroup G) (b x : G) : x ∈ b • (H : Set G) ↔ (b : G ⧸ H) = x := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, QuotientGroup.eq, SetLike.mem_coe]

section RepIndependence

variable (H : Subgroup G)

private def IsCosetSystem (C : Set G) (s : Finset G) : Prop :=
  (∀ b ∈ s, b ∈ C) ∧
    ∀ x, C.indicator (fun _ => (1 : ℂ)) x = ∑ b ∈ s, (b • (H : Set G)).indicator (fun _ => (1 : ℂ)) x

private theorem isCosetSystem_of_exists {C : Set G} {s : Finset G} (h₁ : ∀ b ∈ s, b ∈ C)
    (h₃ : ∀ x, C.indicator (fun _ => (1 : ℂ)) x = ∑ b ∈ s, (b • (H : Set G)).indicator (fun _ => (1 : ℂ)) x) :
    IsCosetSystem H C s :=
  ⟨h₁, h₃⟩

variable {H}

private theorem mem_smul_coset_comm {b b' : G} : b ∈ b' • (H : Set G) ↔ b' ∈ b • (H : Set G) := by
  rw [mem_smul_coset_iff, mem_smul_coset_iff, eq_comm]

private theorem eq_of_mem_smul_coset_of_rightInvariant {F : G → ℂ} (hF : ∀ h ∈ H, ∀ r, F (r * h) = F r) {b b' : G}
    (hb : b ∈ b' • (H : Set G)) : F b = F b' := by
  obtain ⟨h, hh, rfl⟩ := hb
  exact hF h hh b'

private theorem indicator_mul_comm {F : G → ℂ} (hF : ∀ h ∈ H, ∀ r, F (r * h) = F r) (b b' : G) :
    (b' • (H : Set G)).indicator (fun _ => (1 : ℂ)) b * F b =
      (b • (H : Set G)).indicator (fun _ => (1 : ℂ)) b' * F b' := by
  by_cases hb : b ∈ b' • (H : Set G)
  · have hb' : b' ∈ b • (H : Set G) := mem_smul_coset_comm.mp hb
    rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb', eq_of_mem_smul_coset_of_rightInvariant hF hb]
  · have hb' : b' ∉ b • (H : Set G) := fun h' => hb (mem_smul_coset_comm.mp h')
    rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb', zero_mul, zero_mul]

private theorem sum_eq_sum_of_isCosetSystem {C : Set G} {s s' : Finset G} (hs : IsCosetSystem H C s)
    (hs' : IsCosetSystem H C s') {F : G → ℂ} (hF : ∀ h ∈ H, ∀ r, F (r * h) = F r) :
    ∑ b ∈ s, F b = ∑ b ∈ s', F b := by

  have hleft : ∀ b ∈ s, F b = ∑ b' ∈ s', (b' • (H : Set G)).indicator (fun _ => (1 : ℂ)) b * F b := by
    intro b hb
    rw [← Finset.sum_mul, ← hs'.2 b, Set.indicator_of_mem (hs.1 b hb), one_mul]

  have hright : ∀ b' ∈ s', F b' = ∑ b ∈ s, (b • (H : Set G)).indicator (fun _ => (1 : ℂ)) b' * F b' := by
    intro b' hb'
    rw [← Finset.sum_mul, ← hs.2 b', Set.indicator_of_mem (hs'.1 b' hb'), one_mul]
  calc ∑ b ∈ s, F b
      = ∑ b ∈ s, ∑ b' ∈ s', (b' • (H : Set G)).indicator (fun _ => (1 : ℂ)) b * F b :=
        Finset.sum_congr rfl hleft
    _ = ∑ b' ∈ s', ∑ b ∈ s, (b' • (H : Set G)).indicator (fun _ => (1 : ℂ)) b * F b := Finset.sum_comm
    _ = ∑ b' ∈ s', ∑ b ∈ s, (b • (H : Set G)).indicator (fun _ => (1 : ℂ)) b' * F b' :=
        Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b _ => indicator_mul_comm hF b b'
    _ = ∑ b' ∈ s', F b' := Finset.sum_congr rfl fun b' hb' => (hright b' hb').symm

private theorem isCosetSystem_image_mul_left
    [DecidableEq G] {C : Set G} {s : Finset G} (hs : IsCosetSystem H C s) {k : G}
    (hkC : ∀ x, k * x ∈ C ↔ x ∈ C) : IsCosetSystem H C (s.image fun b => k * b) := by
  refine ⟨?_, fun x => ?_⟩
  · intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    exact (hkC b₀).mpr (hs.1 b₀ hb₀)
  · have himg : ∑ b ∈ s.image (fun b => k * b), (b • (H : Set G)).indicator (fun _ => (1 : ℂ)) x =
        ∑ b ∈ s, ((k * b) • (H : Set G)).indicator (fun _ => (1 : ℂ)) x :=
      Finset.sum_image fun _ _ _ _ h => mul_left_cancel h
    rw [himg]

    have hx : C.indicator (fun _ => (1 : ℂ)) x = C.indicator (fun _ => (1 : ℂ)) (k⁻¹ * x) := by
      by_cases hxC : x ∈ C
      · rw [Set.indicator_of_mem hxC, Set.indicator_of_mem ((hkC (k⁻¹ * x)).mp (by rwa [mul_inv_cancel_left]))]
      · rw [Set.indicator_of_notMem hxC,
          Set.indicator_of_notMem fun h' => hxC (by simpa [mul_inv_cancel_left] using (hkC (k⁻¹ * x)).mpr h')]
    rw [hx, hs.2]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hiff : k⁻¹ * x ∈ b • (H : Set G) ↔ x ∈ (k * b) • (H : Set G) := by
      rw [mem_smul_coset_iff, mem_smul_coset_iff, QuotientGroup.eq, QuotientGroup.eq, mul_inv_rev, mul_assoc]
    by_cases hxb : k⁻¹ * x ∈ b • (H : Set G)
    · rw [Set.indicator_of_mem hxb, Set.indicator_of_mem (hiff.mp hxb)]
    · rw [Set.indicator_of_notMem hxb, Set.indicator_of_notMem fun h' => hxb (hiff.mpr h')]

private theorem sum_mul_left_eq_sum_of_isCosetSystem {C : Set G} {s : Finset G} (hs : IsCosetSystem H C s) {k : G}
    (hkC : ∀ x, k * x ∈ C ↔ x ∈ C) {F : G → ℂ} (hF : ∀ h ∈ H, ∀ r, F (r * h) = F r) :
    ∑ b ∈ s, F (k * b) = ∑ b ∈ s, F b := by
  classical
  have himg : ∑ b ∈ s.image (fun b => k * b), F b = ∑ b ∈ s, F (k * b) :=
    Finset.sum_image fun _ _ _ _ h => mul_left_cancel h
  rw [← himg]
  exact sum_eq_sum_of_isCosetSystem (isCosetSystem_image_mul_left hs hkC) hs hF

end RepIndependence

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem exists_finset_indicator_eq_sum_indicator_smul_coset
    (H : Subgroup G) (hH : IsOpen (H : Set G)) {C : Set G}
    (hC : IsCompact C) (hCH : ∀ c ∈ C, ∀ h ∈ H, c * h ∈ C) :
    ∃ s : Finset G, (∀ b ∈ s, b ∈ C) ∧
      (∀ b ∈ s, ∀ b' ∈ s, b ≠ b' → Disjoint (b • (H : Set G)) (b' • (H : Set G))) ∧
      ∀ x, C.indicator (fun _ => (1 : ℂ)) x = ∑ b ∈ s, (b • (H : Set G)).indicator (fun _ => (1 : ℂ)) x := by
  classical

  obtain ⟨t, htsub, htfin, htcov⟩ := hC.elim_finite_subcover_image (fun c (_ : c ∈ C) => hH.smul c)
    (fun x hx => Set.mem_biUnion hx (mem_smul_coset_self H x))

  set s : Finset G := (htfin.toFinset.image fun c : G => (c : G ⧸ H)).image fun q => q.out with hs_def

  have hcoset_sub : ∀ c ∈ C, c • (H : Set G) ⊆ C := by
    intro c hc x hx
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hx
    have := hCH c hc _ hx
    rwa [mul_inv_cancel_left] at this

  have hmem_s : ∀ b ∈ s, ∃ c ∈ C, (c : G ⧸ H) = b := by
    intro b hb
    rw [hs_def, Finset.mem_image] at hb
    obtain ⟨q, hq, rfl⟩ := hb
    rw [Finset.mem_image] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    exact ⟨c, htsub (htfin.mem_toFinset.mp hc), (QuotientGroup.out_eq' _).symm⟩
  have hs_C : ∀ b ∈ s, b ∈ C := by
    intro b hb
    obtain ⟨c, hc, hcb⟩ := hmem_s b hb
    exact hcoset_sub c hc ((mem_smul_coset_iff H c b).mpr hcb)
  refine ⟨s, hs_C, ?_, ?_⟩
  ·
    intro b hb b' hb' hne
    rw [Set.disjoint_left]
    intro x hx hx'
    apply hne
    have h1 := (mem_smul_coset_iff H b x).mp hx
    have h2 := (mem_smul_coset_iff H b' x).mp hx'
    rw [hs_def, Finset.mem_image] at hb hb'
    obtain ⟨q, -, rfl⟩ := hb
    obtain ⟨q', -, rfl⟩ := hb'
    rw [QuotientGroup.out_eq'] at h1 h2
    rw [← h2] at h1
    exact congrArg Quotient.out h1
  · intro x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]

      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (htcov hx)
      have hc' : c ∈ C := htsub hc
      set b : G := (c : G ⧸ H).out with hb_def
      have hb_s : b ∈ s := by
        rw [hs_def, Finset.mem_image]
        exact ⟨(c : G ⧸ H), Finset.mem_image.mpr ⟨c, htfin.mem_toFinset.mpr hc, rfl⟩, rfl⟩
      have hxb : x ∈ b • (H : Set G) := by
        rw [mem_smul_coset_iff, hb_def, QuotientGroup.out_eq']
        exact (mem_smul_coset_iff H c x).mp hxc
      rw [Finset.sum_eq_single b]
      · rw [Set.indicator_of_mem hxb]
      · intro b' hb' hne
        have hdis := (mem_smul_coset_iff H b' x).not.mpr ?_
        · exact Set.indicator_of_notMem hdis _
        · intro hb'x
          apply hne
          have h1 := (mem_smul_coset_iff H b x).mp hxb
          rw [hs_def, Finset.mem_image] at hb'
          obtain ⟨q', -, rfl⟩ := hb'
          rw [hb_def, QuotientGroup.out_eq'] at h1
          rw [QuotientGroup.out_eq'] at hb'x
          rw [hb_def, h1, ← hb'x]
      · intro habs
        exact absurd hb_s habs
    · rw [Set.indicator_of_notMem hx]
      refine (Finset.sum_eq_zero fun b hb => ?_).symm
      refine Set.indicator_of_notMem (fun hxb => hx ?_) _
      exact hcoset_sub b (hs_C b hb) hxb

end LevelPieces

end CosetSystems

namespace LevelPieces
namespace PieceTranslates

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm LevelPieces.FinIncl LevelPieces.Pieces
open scoped Pointwise

variable {L : Type} [Field L] [NumberField L]

private theorem piece_inv_mul (N : Ideal (𝓞 L)) (θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (c b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (y : AdelicGL2 (𝓞 L) L) :
    piece N θa c ((adelicFinGLIncl L b)⁻¹ * y) =
      θa (AdelicLevel.glArch (𝓞 L) L y) *
        (b • finDoubleCoset N c).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 L) L y) := by
  classical
  unfold piece
  rw [map_mul, map_mul, map_inv, map_inv, glArch_adelicFinGLIncl, glFin_adelicFinGLIncl, inv_one, one_mul]
  congr 1
  rw [Set.indicator_apply, Set.indicator_apply]
  simp only [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

private theorem piece_eq_sum_piece_inv_mul (N : Ideal (𝓞 L)) (θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (a c : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
    (hs : ∀ x, (finDoubleCoset N a).indicator (fun _ => (1 : ℂ)) x =
      ∑ b ∈ s, (b • finDoubleCoset N c).indicator (fun _ => (1 : ℂ)) x)
    (y : AdelicGL2 (𝓞 L) L) :
    piece N θa a y = ∑ b ∈ s, piece N θa c ((adelicFinGLIncl L b)⁻¹ * y) := by
  simp only [piece_inv_mul, ← Finset.mul_sum, ← hs]
  rfl

private theorem integrable_mul_piece_inv_mul (N : Ideal (𝓞 L)) (θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (c : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ)
    (hk : Continuous (piece N θa c))
    (hks : HasCompactSupport (piece N θa c)) (g : AdelicGL2 (𝓞 L) L) (b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 L) L
    Integrable (fun y => φ (g * y) * piece N θa c ((adelicFinGLIncl L b)⁻¹ * y))
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
    NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  have h1 : Continuous fun y : AdelicGL2 (𝓞 L) L => piece N θa c ((adelicFinGLIncl L b)⁻¹ * y) :=
    hk.comp (continuous_const.mul continuous_id)
  have h2 : HasCompactSupport fun y : AdelicGL2 (𝓞 L) L => piece N θa c ((adelicFinGLIncl L b)⁻¹ * y) :=
    hks.comp_homeomorph (Homeomorph.mulLeft (adelicFinGLIncl L b)⁻¹)
  exact ((hφ.comp (continuous_const.mul continuous_id)).mul h1).integrable_of_hasCompactSupport h2.mul_left

private theorem convOp_piece_eq_sum_convOp_piece_mul (N : Ideal (𝓞 L)) (θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (a c : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
    (hs : ∀ x, (finDoubleCoset N a).indicator (fun _ => (1 : ℂ)) x =
      ∑ b ∈ s, (b • finDoubleCoset N c).indicator (fun _ => (1 : ℂ)) x)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L)
    (hint : ∀ b ∈ s,
      letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 L) L
      Integrable (fun y => φ (g * y) * piece N θa c ((adelicFinGLIncl L b)⁻¹ * y))
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L)) :
    convOp L (piece N θa a) φ g = ∑ b ∈ s, convOp L (piece N θa c) φ (g * adelicFinGLIncl L b) := by
  letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 L) L
  rw [convOp_apply, rightConv_apply]
  simp_rw [piece_eq_sum_piece_inv_mul N θa a c s hs, Finset.mul_sum]
  rw [integral_finsetSum s hint]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [convOp_apply, rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, rightConv_apply]

private theorem convOp_piece_eq_sum_convOp_piece_mul_of_continuous (N : Ideal (𝓞 L))
    (θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (a c : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
    (hs : ∀ x, (finDoubleCoset N a).indicator (fun _ => (1 : ℂ)) x =
      ∑ b ∈ s, (b • finDoubleCoset N c).indicator (fun _ => (1 : ℂ)) x)
    (hk : Continuous (piece N θa c)) (hks : HasCompactSupport (piece N θa c))
    {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 L) L) :
    convOp L (piece N θa a) φ g = ∑ b ∈ s, convOp L (piece N θa c) φ (g * adelicFinGLIncl L b) :=
  convOp_piece_eq_sum_convOp_piece_mul N θa a c s hs φ g fun b _ =>
    integrable_mul_piece_inv_mul N θa c hφ hk hks g b

private theorem convOp_piece_eq_sum_rightTranslate_convOp_piece (N : Ideal (𝓞 L))
    (θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (a c : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
    (hs : ∀ x, (finDoubleCoset N a).indicator (fun _ => (1 : ℂ)) x =
      ∑ b ∈ s, (b • finDoubleCoset N c).indicator (fun _ => (1 : ℂ)) x)
    (hk : Continuous (piece N θa c)) (hks : HasCompactSupport (piece N θa c))
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : Continuous u) :
    convOp L (piece N θa a) u =
      ∑ b ∈ s, CuspidalConstituent.rightTranslate L (adelicFinGLIncl L b) (convOp L (piece N θa c) u) := by
  funext g
  rw [Finset.sum_apply]
  exact convOp_piece_eq_sum_convOp_piece_mul_of_continuous N θa a c s hs hk hks hu g

end LevelPieces.PieceTranslates

namespace LevelPieces
namespace UnitCommutation

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm AutomorphicForm.CuspidalConstituent LevelPieces.FinIncl

variable {L : Type} [Field L] [NumberField L]

private theorem integrable_mul_left_mul (b : AdelicGL2 (𝓞 L) L) {ψ w : AdelicGL2 (𝓞 L) L → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hwc : Continuous w) (g : AdelicGL2 (𝓞 L) L) :
    letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 L) L
    Integrable (fun x => w (g * b * x) * ψ x) (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
    NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  exact ((hwc.comp (continuous_const.mul continuous_id)).mul hψc).integrable_of_hasCompactSupport hψs.mul_left

private theorem convOp_sum_rightTranslate_eq_sum_rightTranslate_convOp (N : Ideal (𝓞 L))
    (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) {ψ w : AdelicGL2 (𝓞 L) L → ℂ}
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hwc : Continuous w)
    (hw : ∀ u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N, ∀ y, w (y * adelicFinGLIncl L u) = w y)
    (hsplit : ∀ x : AdelicGL2 (𝓞 L) L, ψ x ≠ 0 →
      ∃ xr : AdelicGL2 (𝓞 L) L, ∃ kv ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N,
        x = xr * adelicFinGLIncl L kv ∧ ∀ b ∈ s, xr * adelicFinGLIncl L b = adelicFinGLIncl L b * xr)
    (hrep : ∀ k ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N, ∀ F : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ,
      (∀ u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N, ∀ y, F (y * u) = F y) →
        ∑ b ∈ s, F (k * b) = ∑ b ∈ s, F b) :
    convOp L ψ (∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) w) =
      ∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) (convOp L ψ w) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 L) L
  funext g
  have hpt : ∀ x : AdelicGL2 (𝓞 L) L,
      (∑ b ∈ s, w (g * x * adelicFinGLIncl L b)) * ψ x = (∑ b ∈ s, w (g * adelicFinGLIncl L b * x)) * ψ x := by
    intro x
    by_cases hx : ψ x = 0
    · simp only [hx, mul_zero]
    obtain ⟨xr, kv, hkv, rfl, hcomm⟩ := hsplit x hx
    congr 1
    have hF : ∀ u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N, ∀ y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
        w (g * xr * adelicFinGLIncl L (y * u)) = w (g * xr * adelicFinGLIncl L y) := by
      intro u hu y
      rw [map_mul, ← mul_assoc, hw u hu]
    have hleft : ∑ b ∈ s, w (g * (xr * adelicFinGLIncl L kv) * adelicFinGLIncl L b) =
        ∑ b ∈ s, w (g * xr * adelicFinGLIncl L b) := by
      have := hrep kv hkv (fun y => w (g * xr * adelicFinGLIncl L y)) hF
      simpa only [map_mul, mul_assoc] using this
    rw [hleft]
    refine Finset.sum_congr rfl fun b hb => ?_
    have e1 : g * adelicFinGLIncl L b * (xr * adelicFinGLIncl L kv) =
        g * xr * adelicFinGLIncl L b * adelicFinGLIncl L kv := by
      calc g * adelicFinGLIncl L b * (xr * adelicFinGLIncl L kv)
          = g * (adelicFinGLIncl L b * xr) * adelicFinGLIncl L kv := by simp only [mul_assoc]
        _ = g * (xr * adelicFinGLIncl L b) * adelicFinGLIncl L kv := by rw [← hcomm b hb]
        _ = g * xr * adelicFinGLIncl L b * adelicFinGLIncl L kv := by simp only [mul_assoc]
    rw [e1, hw kv hkv]
  calc convOp L ψ (∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) w) g
      = ∫ x, (∑ b ∈ s, w (g * x * adelicFinGLIncl L b)) * ψ x
          ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) := by
        rw [convOp_apply, rightConv_apply]
        simp only [Finset.sum_apply, rightTranslate_apply]
    _ = ∑ b ∈ s, ∫ x, w (g * adelicFinGLIncl L b * x) * ψ x
          ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) := by
        simp only [hpt]
        simp only [Finset.sum_mul]
        exact integral_finsetSum s fun b _ => integrable_mul_left_mul (adelicFinGLIncl L b) hψc hψs hwc g
    _ = (∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) (convOp L ψ w)) g := by
        rw [Finset.sum_apply]
        simp only [rightTranslate_apply, convOp_apply, rightConv_apply]

end LevelPieces.UnitCommutation

namespace LevelPieces
namespace PureSplitting

p2m_open "NumberField IsDedekindDomain NumberField.AdelicLevel AutomorphicForm"
open LevelPieces.Components LevelPieces.Pieces LevelPieces.Part LevelPieces.FinIncl

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (P : Set (HeightOneSpectrum (𝓞 L)))

private theorem glFin_mul_inv_partOn (x : AdelicGL2 (𝓞 L) L) :
    glFin (𝓞 L) L (x * (adelicFinGLIncl L (partOn P (glFin (𝓞 L) L x)))⁻¹) = dropOn P (glFin (𝓞 L) L x) := by
  rw [map_mul, map_inv, glFin_adelicFinGLIncl]
  have h := partOn_mul_dropOn P (glFin (𝓞 L) L x)
  rw [partOn_mul_comm_dropOn] at h
  calc glFin (𝓞 L) L x * (partOn P (glFin (𝓞 L) L x))⁻¹
      = dropOn P (glFin (𝓞 L) L x) * partOn P (glFin (𝓞 L) L x) * (partOn P (glFin (𝓞 L) L x))⁻¹ := by rw [h]
    _ = dropOn P (glFin (𝓞 L) L x) := mul_inv_cancel_right _ _

private theorem mul_adelicFinGLIncl_comm_of_isPure
    {xr : AdelicGL2 (𝓞 L) L} {f b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hxr : glFin (𝓞 L) L xr = dropOn P f) (hb : IsPure P b) :
    xr * adelicFinGLIncl L b = adelicFinGLIncl L b * xr := by
  refine ext_of_glArch_glFin ?_ ?_
  · rw [map_mul, map_mul, glArch_adelicFinGLIncl, mul_one, one_mul]
  · rw [map_mul, map_mul, glFin_adelicFinGLIncl, hxr]
    exact (isPure_mul_comm P hb (partOn_dropOn P f)).symm

private theorem exists_split_of_isPure (N : Ideal (𝓞 L)) (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
    (hpure : ∀ b ∈ s, IsPure P b) (x : AdelicGL2 (𝓞 L) L)
    (hk : partOn P (glFin (𝓞 L) L x) ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N) :
    ∃ xr : AdelicGL2 (𝓞 L) L, ∃ kv ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N,
      x = xr * adelicFinGLIncl L kv ∧ ∀ b ∈ s, xr * adelicFinGLIncl L b = adelicFinGLIncl L b * xr :=
  ⟨x * (adelicFinGLIncl L (partOn P (glFin (𝓞 L) L x)))⁻¹, partOn P (glFin (𝓞 L) L x), hk,
    (inv_mul_cancel_right x _).symm,
    fun b hb => mul_adelicFinGLIncl_comm_of_isPure P (glFin_mul_inv_partOn P x) (hpure b hb)⟩

private theorem partOn_glFin_mem_finiteLevelOne {N : Ideal (𝓞 L)} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {ψ : AdelicGL2 (𝓞 L) L → ℂ} (hψ : IsUnitFactorizableAbove K L U S ψ)
    (hP : ∀ w ∈ P, w.under (𝓞 K) ∉ S ∧ AdelicLevel.idealBound (𝓞 L) N w = 1)
    {x : AdelicGL2 (𝓞 L) L} (hx : ψ x ≠ 0) :
    partOn P (glFin (𝓞 L) L x) ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N := by
  classical
  rw [mem_finiteLevelOne_iff_forall]
  intro w
  have hcomp : ∀ y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
      (fun i j => AdelicLevel.finAdeleEval (𝓞 L) L w (y.val i j)) = (AdelicLevel.finComponent (𝓞 L) L w y).val :=
    fun _ => rfl
  rw [hcomp, hcomp, map_inv]
  by_cases hw : w ∈ P
  · obtain ⟨hS, hmax⟩ := hP w hw
    have hint : semiLocalComponent K L (w.under (𝓞 K)) (glFin (𝓞 L) L x)
        ∈ semiLocalIntegralSet K L (w.under (𝓞 K)) := by
      by_contra hcon
      obtain ⟨-, φa, φf, φS, -, -, -, -, hvan, hφ⟩ := hψ
      exact hx (by rw [hφ x, hvan _ ⟨w.under (𝓞 K), hS, hcon⟩, mul_zero])
    rw [finComponent_partOn_of_mem P _ hw]
    have hw' := wComp_entries_mem_of_mem L K _ hint (toExt w)
    rw [wComp_semiLocalComponent] at hw'
    exact ⟨isLocalLevelOne_of_integral hmax hw'.1, isLocalLevelOne_of_integral hmax hw'.2⟩
  · rw [finComponent_partOn_of_notMem P _ hw, inv_one]
    exact ⟨isLocalLevelOne_one L N w, isLocalLevelOne_one L N w⟩

private theorem partOn_singleton_glFin_mem_finiteLevelOne {N : Ideal (𝓞 L)} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {ψ : AdelicGL2 (𝓞 L) L → ℂ} (hψ : IsUnitFactorizableAbove K L U S ψ)
    {w : HeightOneSpectrum (𝓞 L)} (hS : w.under (𝓞 K) ∉ S) (hmax : AdelicLevel.idealBound (𝓞 L) N w = 1)
    {x : AdelicGL2 (𝓞 L) L} (hx : ψ x ≠ 0) :
    partOn {w} (glFin (𝓞 L) L x) ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N :=
  partOn_glFin_mem_finiteLevelOne {w} hψ
    (fun w' hw' => by rw [Set.mem_singleton_iff] at hw'; subst hw'; exact ⟨hS, hmax⟩) hx

end LevelPieces.PureSplitting

namespace LevelPieces
namespace ArchTypePieces

p2m_open "NumberField IsDedekindDomain NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero.LevelPieces.FinIncl P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero.LevelPieces.Pieces"

variable (L : Type) [Field L] [NumberField L]

private def archProj : AdelicGL2 (𝓞 L) L →* AdelicGL2 (𝓞 L) L := (adelicArchGLIncl L).comp (glArch (𝓞 L) L)

private theorem archProj_apply (x : AdelicGL2 (𝓞 L) L) : archProj L x = adelicArchGLIncl L (glArch (𝓞 L) L x) := rfl

private theorem glArch_archProj (x : AdelicGL2 (𝓞 L) L) : glArch (𝓞 L) L (archProj L x) = glArch (𝓞 L) L x := by
  rw [archProj_apply, glArch_adelicArchGLIncl]

private theorem glFin_archProj (x : AdelicGL2 (𝓞 L) L) : glFin (𝓞 L) L (archProj L x) = 1 := by
  rw [archProj_apply, glFin_adelicArchGLIncl]

private theorem archProj_rowIsometryInclAt₀ (w : InfinitePlace L) (k : rowIsometrySubgroup₀ w.Completion) :
    archProj L (rowIsometryInclAt₀ L w k) = rowIsometryInclAt₀ L w k := by
  refine ext_of_glArch_glFin ?_ ?_
  · exact glArch_archProj L _
  · rw [glFin_archProj, glFin_rowIsometryInclAt₀]

private theorem commute_adelicFinGLIncl_rowIsometryInclAt₀
    (b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (w : InfinitePlace L)
    (k : rowIsometrySubgroup₀ w.Completion) : Commute (adelicFinGLIncl L b) (rowIsometryInclAt₀ L w k) := by
  refine ext_of_glArch_glFin ?_ ?_
  · rw [map_mul, map_mul, glArch_adelicFinGLIncl, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_adelicFinGLIncl, glFin_rowIsometryInclAt₀, one_mul, mul_one]

variable {L}

private theorem map_mem_iSup_of_forall {n : ℕ} {S : Fin n → Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)}
    (Φ : (AdelicGL2 (𝓞 L) L → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ)) (hΦ : ∀ i, ∀ g ∈ S i, Φ g ∈ S i)
    {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : f ∈ ⨆ i, S i) : Φ f ∈ ⨆ i, S i := by
  refine Submodule.iSup_induction _ (motive := fun g => Φ g ∈ ⨆ i, S i) hf ?_ ?_ ?_
  · intro i g hgi
    exact le_iSup S i (hΦ i g hgi)
  · show Φ 0 ∈ ⨆ i, S i
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro g h hg hh
    rw [map_add]
    exact Submodule.add_mem _ hg hh

private def rightOp (y : AdelicGL2 (𝓞 L) L) : (AdelicGL2 (𝓞 L) L → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ) where
  toFun u x := u (x * y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def projMulOp (m : AdelicGL2 (𝓞 L) L → ℂ) : (AdelicGL2 (𝓞 L) L → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ) where
  toFun u x := u (archProj L x) * m x
  map_add' _ _ := funext fun _ => add_mul _ _ _
  map_smul' _ _ := funext fun _ => mul_assoc _ _ _

private theorem rightOp_apply (y : AdelicGL2 (𝓞 L) L) (u : AdelicGL2 (𝓞 L) L → ℂ) :
    rightOp y u = fun x => u (x * y) := rfl

private theorem projMulOp_apply (m u : AdelicGL2 (𝓞 L) L → ℂ) : projMulOp m u = fun x => u (archProj L x) * m x := rfl

private def IsArchRightInvariant (m : AdelicGL2 (𝓞 L) L → ℂ) : Prop :=
  ∀ (w : InfinitePlace L) (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
    m (x * rowIsometryInclAt₀ L w k) = m x

private theorem rightOp_mem_archCutSubmodule {tys : ArchTypeFamily L} {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hf : f ∈ archCutSubmodule L tys) (b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    rightOp (adelicFinGLIncl L b) f ∈ archCutSubmodule L tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine map_mem_iSup_of_forall _ (fun i g hgi => ?_) (hf w)
  exact comp_mul_mem_typeSubmodule_of_commute hgi (adelicFinGLIncl L b)
    (commute_adelicFinGLIncl_rowIsometryInclAt₀ L b w)

private theorem rightOp_mem_archDualCutSubmodule {tys : ArchTypeFamily L} {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hf : f ∈ archDualCutSubmodule L tys) (b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    rightOp (adelicFinGLIncl L b) f ∈ archDualCutSubmodule L tys := by
  rw [mem_archDualCutSubmodule_iff] at hf ⊢
  intro w
  refine map_mem_iSup_of_forall _ (fun i g hgi => ?_) (hf w)
  exact comp_mul_mem_typeSubmodule_of_commute hgi (adelicFinGLIncl L b)
    (commute_adelicFinGLIncl_rowIsometryInclAt₀ L b w)

private theorem projMulOp_mem_archCutSubmodule {tys : ArchTypeFamily L} {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hf : f ∈ archCutSubmodule L tys) {m : AdelicGL2 (𝓞 L) L → ℂ} (hm : IsArchRightInvariant m) :
    projMulOp m f ∈ archCutSubmodule L tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine map_mem_iSup_of_forall _ (fun i g hgi => ?_) (hf w)
  exact comp_mul_mem_typeSubmodule_of_hom (archProj L) (archProj_rowIsometryInclAt₀ L w) (hm w) hgi

private theorem projMulOp_mem_archDualCutSubmodule {tys : ArchTypeFamily L} {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hf : f ∈ archDualCutSubmodule L tys) {m : AdelicGL2 (𝓞 L) L → ℂ} (hm : IsArchRightInvariant m) :
    projMulOp m f ∈ archDualCutSubmodule L tys := by
  rw [mem_archDualCutSubmodule_iff] at hf ⊢
  intro w
  refine map_mem_iSup_of_forall _ (fun i g hgi => ?_) (hf w)
  exact comp_mul_mem_typeSubmodule_of_hom (archProj L) (archProj_rowIsometryInclAt₀ L w) (hm w) hgi

private theorem mem_of_mul_const_mem {X : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)} {f : AdelicGL2 (𝓞 L) L → ℂ} {c : ℂ}
    (hc : c ≠ 0) (h : (fun x => f x * c) ∈ X) : f ∈ X := by
  have h' := X.smul_mem c⁻¹ h
  convert h' using 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_comm c⁻¹, mul_assoc, mul_inv_cancel₀ hc, mul_one]

private theorem isArchRightInvariant_comp_glFin (φ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) :
    IsArchRightInvariant fun x => φ (glFin (𝓞 L) L x) := by
  intro w k x
  simp only [map_mul, glFin_rowIsometryInclAt₀, mul_one]

private theorem isArchRightInvariant_comp_glFin_inv (φ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) :
    IsArchRightInvariant fun x => φ (glFin (𝓞 L) L x)⁻¹ := by
  intro w k x
  simp only [map_mul, glFin_rowIsometryInclAt₀, mul_one]

private theorem comp_glArch_mem_archDualCutSubmodule {tys : ArchTypeFamily L} {θ : AdelicGL2 (𝓞 L) L → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    (hθ : ∀ g, θ g = fa (glArch (𝓞 L) L g) * ff (glFin (𝓞 L) L g)) {x₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hx₀ : ff x₀ ≠ 0) (hbf : θ ∈ archDualCutSubmodule L tys) :
    (fun x => fa (glArch (𝓞 L) L x)) ∈ archDualCutSubmodule L tys := by
  have h := projMulOp_mem_archDualCutSubmodule (rightOp_mem_archDualCutSubmodule hbf x₀)
    (m := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
  refine mem_of_mul_const_mem hx₀ ?_
  convert h using 1
  funext x
  simp only [projMulOp_apply, rightOp_apply, hθ, map_mul, glArch_archProj, glFin_archProj, glArch_adelicFinGLIncl,
    glFin_adelicFinGLIncl, one_mul, mul_one]

private theorem comp_glArch_inv_mem_archCutSubmodule {tys : ArchTypeFamily L} {θ : AdelicGL2 (𝓞 L) L → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    (hθ : ∀ g, θ g = fa (glArch (𝓞 L) L g) * ff (glFin (𝓞 L) L g)) {x₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hx₀ : ff x₀ ≠ 0) (hbf : (fun x => θ x⁻¹) ∈ archCutSubmodule L tys) :
    (fun x => fa (glArch (𝓞 L) L x)⁻¹) ∈ archCutSubmodule L tys := by
  have h := projMulOp_mem_archCutSubmodule (rightOp_mem_archCutSubmodule hbf x₀⁻¹)
    (m := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
  refine mem_of_mul_const_mem hx₀ ?_
  convert h using 1
  funext x
  simp only [projMulOp_apply, rightOp_apply, hθ, map_inv, map_mul, glArch_archProj, glFin_archProj,
    glArch_adelicFinGLIncl, glFin_adelicFinGLIncl, one_mul, mul_one, inv_one, inv_inv]

private theorem isArchBiFinite_piece {tys : ArchTypeFamily L} {θ : AdelicGL2 (𝓞 L) L → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    (hθ : ∀ g, θ g = fa (glArch (𝓞 L) L g) * ff (glFin (𝓞 L) L g)) {x₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hx₀ : ff x₀ ≠ 0) (hbf : IsArchBiFinite L tys θ) (N : Ideal (𝓞 L)) (c : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    IsArchBiFinite L tys (piece N fa c) := by
  obtain ⟨hinv, hdual⟩ := hbf
  constructor
  · have h := projMulOp_mem_archCutSubmodule (comp_glArch_inv_mem_archCutSubmodule hθ hx₀ hinv)
      (isArchRightInvariant_comp_glFin_inv ((finDoubleCoset N c).indicator fun _ => (1 : ℂ)))
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  · have h := projMulOp_mem_archDualCutSubmodule (comp_glArch_mem_archDualCutSubmodule hθ hx₀ hdual)
      (isArchRightInvariant_comp_glFin ((finDoubleCoset N c).indicator fun _ => (1 : ℂ)))
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip

end LevelPieces.ArchTypePieces

section StabilityContext

p2m_open "NumberField IsDedekindDomain NumberField.AdelicLevel"
open scoped Pointwise

namespace LevelPieces
namespace CutStability

open LevelPieces LevelPieces.FinIncl LevelPieces.Pieces AutomorphicForm.CuspidalConstituent

variable {L : Type} [Field L] [NumberField L]

private theorem commute_adelicFinGLIncl_rowIsometryInclAt₀
    (b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (w : InfinitePlace L)
    (k : rowIsometrySubgroup₀ w.Completion) : Commute (adelicFinGLIncl L b) (rowIsometryInclAt₀ L w k) := by
  show adelicFinGLIncl L b * rowIsometryInclAt₀ L w k = rowIsometryInclAt₀ L w k * adelicFinGLIncl L b
  refine ext_of_glArch_glFin ?_ ?_
  · rw [map_mul, map_mul, glArch_adelicFinGLIncl, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_adelicFinGLIncl, glFin_rowIsometryInclAt₀, one_mul, mul_one]

private theorem rightTranslate_adelicFinGLIncl_mem_archCutSubmodule
    {tys : ArchTypeFamily L} {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hf : f ∈ archCutSubmodule L tys) (b : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    rightTranslate L (adelicFinGLIncl L b) f ∈ archCutSubmodule L tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => rightTranslate L (adelicFinGLIncl L b) f ∈
      ⨆ i : Fin (tys.card w), archTypeSubmoduleAt L w (tys.rep w i)) (hf w) ?_ ?_ ?_
  · intro i f hfi
    refine le_iSup (fun j => archTypeSubmoduleAt L w (tys.rep w j)) i ?_
    exact comp_mul_mem_typeSubmodule_of_commute hfi (adelicFinGLIncl L b)
      (commute_adelicFinGLIncl_rowIsometryInclAt₀ b w)
  · exact Submodule.zero_mem _
  · exact fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂

private theorem eq_adelicFinGLIncl_glFin_of_mem {N : Ideal (𝓞 L)} {u : AdelicGL2 (𝓞 L) L}
    (hu : u ∈ AdelicLevel.levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) :
    u = adelicFinGLIncl L (AdelicLevel.glFin (𝓞 L) L u) := by
  refine ext_of_glArch_glFin ?_ ?_
  · rw [glArch_adelicFinGLIncl]
    exact (mem_finiteAdelicGL2Subgroup_iff L u).mp (Subgroup.mem_inf.mp hu).2
  · rw [glFin_adelicFinGLIncl]

private theorem sum_rightTranslate_mem
    (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ) {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)}
    (hVs : IsCuspSubrep L pins ξ V) {N : Ideal (𝓞 L)}
    (hU : pins.U N = AdelicLevel.levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (tys : ArchTypeFamily L)
    {aV : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} {s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))}
    (hs : IsCosetSystem (AdelicLevel.finiteLevelOne (𝓞 L) L N) (finDoubleCoset N aV) s)
    {w : AdelicGL2 (𝓞 L) L → ℂ} (hw : w ∈ V ⊓ levelInvariantSubmodule L pins N ⊓ archCutSubmodule L tys) :
    (∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) w) ∈
      V ⊓ levelInvariantSubmodule L pins N ⊓ archCutSubmodule L tys := by
  obtain ⟨⟨hwV, hwU⟩, hwT⟩ := hw
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  ·
    exact Submodule.sum_mem _ fun b _ => hVs.rightTranslate_fin_mem _
      ((mem_finiteAdelicGL2Subgroup_iff L _).mpr (glArch_adelicFinGLIncl L b)) w hwV
  ·
    intro g u hu
    rw [hU] at hu
    have hu' : AdelicLevel.glFin (𝓞 L) L u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N :=
      AdelicLevel.mem_levelOne_iff.mp (Subgroup.mem_inf.mp hu).1

    have hwU' : ∀ x : AdelicGL2 (𝓞 L) L, ∀ u' ∈ pins.U N, w (x * u') = w x := hwU
    have hF : ∀ h ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N, ∀ r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
        (fun r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) => w (g * adelicFinGLIncl L r)) (r * h) =
          (fun r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) => w (g * adelicFinGLIncl L r)) r := by
      intro h hh r
      show w (g * adelicFinGLIncl L (r * h)) = w (g * adelicFinGLIncl L r)
      rw [map_mul, ← mul_assoc]
      exact hwU' (g * adelicFinGLIncl L r) (adelicFinGLIncl L h) (by rw [hU]; exact adelicFinGLIncl_mem L hh)
    have hkC : ∀ x, AdelicLevel.glFin (𝓞 L) L u * x ∈ finDoubleCoset N aV ↔ x ∈ finDoubleCoset N aV :=
      fun x => mul_mem_finDoubleCoset_iff hu' aV x
    have hmoved := sum_mul_left_eq_sum_of_isCosetSystem (F := fun r => w (g * adelicFinGLIncl L r)) hs hkC hF
    simp only [Finset.sum_apply, rightTranslate]
    calc ∑ b ∈ s, w (g * u * adelicFinGLIncl L b)
        = ∑ b ∈ s, w (g * adelicFinGLIncl L (AdelicLevel.glFin (𝓞 L) L u * b)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [map_mul, ← mul_assoc, ← eq_adelicFinGLIncl_glFin_of_mem hu]
      _ = ∑ b ∈ s, w (g * adelicFinGLIncl L b) := hmoved
  ·
    exact Submodule.sum_mem _ fun b _ => rightTranslate_adelicFinGLIncl_mem_archCutSubmodule hwT b

end LevelPieces.CutStability

end StabilityContext

namespace LevelPieces
namespace TranslateEigenvector

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private theorem exists_eigenvector_mem (E : Submodule ℂ M) [FiniteDimensional ℂ E] (T : M →ₗ[ℂ] M)
    (hTE : ∀ z ∈ E, T z ∈ E) {y : M} (hyE : y ∈ E) (hy0 : y ≠ 0) :
    ∃ (μ : ℂ) (v : M), v ∈ E ∧ v ≠ 0 ∧ T v = μ • v := by
  haveI : Nontrivial E := nontrivial_of_ne ⟨y, hyE⟩ 0 fun h => hy0 ((Submodule.mk_eq_zero E hyE).mp h)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (T.restrict hTE)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, v, v.2, fun h => hv.2 (Subtype.ext h), ?_⟩
  have h := congrArg Subtype.val hv.apply_eq_smul
  simpa only [LinearMap.restrict_apply, Submodule.coe_smul] using h

private theorem apply_eq_smul_of_mem_span {ι : Type*} (T : M →ₗ[ℂ] M) (R : ι → M → M)
    (hR : ∀ (i : ι) (a : ℂ) (z : M), R i (a • z) = a • R i z) {v : M} {μ : ℂ} (hv : T v = μ • v)
    (hcomm : ∀ i, T (R i v) = R i (T v)) {y : M} (hy : y ∈ Submodule.span ℂ (Set.range fun i => R i v)) :
    T y = μ • y := by
  have hle : Submodule.span ℂ (Set.range fun i => R i v) ≤ Module.End.eigenspace T μ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, hcomm i, hv, hR]
  exact Module.End.mem_eigenspace_iff.mp (hle hy)

private theorem exists_apply_eq_smul (E : Submodule ℂ M) [FiniteDimensional ℂ E] (T : M →ₗ[ℂ] M)
    (hTE : ∀ z ∈ E, T z ∈ E) {ι : Type*} (R : ι → M → M) (hR : ∀ (i : ι) (a : ℂ) (z : M), R i (a • z) = a • R i z)
    (hcomm : ∀ i, ∀ z ∈ E, T (R i z) = R i (T z)) {y : M} (hyE : y ∈ E) (hy0 : y ≠ 0)
    (hcyc : ∀ v ∈ E, v ≠ 0 → y ∈ Submodule.span ℂ (Set.range fun i => R i v)) :
    ∃ μ : ℂ, T y = μ • y := by
  obtain ⟨μ, v, hvE, hv0, hv⟩ := exists_eigenvector_mem E T hTE hyE hy0
  exact ⟨μ, apply_eq_smul_of_mem_span T R hR hv (fun i => hcomm i v hvE) (hcyc v hvE hv0)⟩

section Concrete

open AutomorphicForm AutomorphicForm.CuspidalConstituent NumberField IsDedekindDomain LevelPieces.FinIncl

variable {L : Type} [Field L] [NumberField L]

private def transSum (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :
    (AdelicGL2 (𝓞 L) L → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ) where
  toFun z := ∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) z
  map_add' z₁ z₂ := by
    funext x
    simp only [Finset.sum_apply, Pi.add_apply, rightTranslate, Finset.sum_add_distrib]
  map_smul' a z := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, rightTranslate, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

private theorem transSum_apply (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) (z : AdelicGL2 (𝓞 L) L → ℂ) :
    transSum s z = ∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) z := rfl

private theorem exists_sum_rightTranslate_eq_smul (E : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)) [FiniteDimensional ℂ E]
    (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
    (hTE : ∀ z ∈ E, (∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) z) ∈ E)
    (Class : (AdelicGL2 (𝓞 L) L → ℂ) → Prop)
    (hcomm : ∀ χ, Class χ → ∀ z ∈ E, (∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) (convOp L χ z))
      = convOp L χ (∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) z))
    {y : AdelicGL2 (𝓞 L) L → ℂ} (hyE : y ∈ E) (hy0 : y ≠ 0)
    (hcyc : ∀ v ∈ E, v ≠ 0 → y ∈ Submodule.span ℂ (Set.range fun χ : {χ // Class χ} => convOp L χ.1 v)) :
    ∃ μ : ℂ, (∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) y) = μ • y := by
  obtain ⟨μ, hμ⟩ := exists_apply_eq_smul E (transSum s) (fun z hz => by simpa only [transSum_apply] using hTE z hz)
    (fun χ : {χ // Class χ} => convOp L χ.1) (fun χ a z => convOp_smul L χ.1 a z)
    (fun χ z hz => by simpa only [transSum_apply] using hcomm χ.1 χ.2 z hz) hyE hy0 hcyc
  exact ⟨μ, by simpa only [transSum_apply] using hμ⟩

end Concrete

end LevelPieces.TranslateEigenvector

namespace LevelPieces
namespace Recursion

private structure Interface (X ι ρ : Type) where

  Cont : (X → ℂ) → Prop

  Inv : (X → ℂ) → Prop

  R : ρ → (X → ℂ) → (X → ℂ)

  B : ρ → Finset ι

  R_cont : ∀ r f, Cont f → Cont (R r f)

  R_inv : ∀ r f, Cont f → Inv (R r f)

  T : (X → ℂ) → (X → ℂ)

  T_cont : ∀ f, Cont f → Cont (T f)

  step : ∀ r : ρ, (B r).Nonempty → ∃ (r' : ρ) (S : (X → ℂ) → (X → ℂ)),
    (B r').card < (B r).card ∧ (∀ f, Cont f → R r f = S (R r' f)) ∧ (∀ f, Cont f → Inv f → T (S f) = S (T f))

  base : ∀ r : ρ, B r = ∅ → ∀ f, Cont f → Inv f → T (R r f) = R r (T f)

variable {X ι ρ : Type} (I : Interface X ι ρ)

private theorem T_comm_R_aux :
    ∀ n : ℕ, ∀ r : ρ, (I.B r).card = n → ∀ f, I.Cont f → I.Inv f → I.T (I.R r f) = I.R r (I.T f) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r hn f hf hfi
    by_cases hB : I.B r = ∅
    · exact I.base r hB f hf hfi
    obtain ⟨r', S, hlt, hRS, hTS⟩ := I.step r (Finset.nonempty_iff_ne_empty.mpr hB)
    rw [hRS f hf, hRS (I.T f) (I.T_cont f hf), hTS (I.R r' f) (I.R_cont r' f hf) (I.R_inv r' f hf),
      ih _ (lt_of_lt_of_eq hlt hn) r' rfl f hf hfi]

private theorem T_comm_R (r : ρ) (f : X → ℂ) (hf : I.Cont f) (hfi : I.Inv f) : I.T (I.R r f) = I.R r (I.T f) :=
  T_comm_R_aux I _ r rfl f hf hfi

private structure InterfaceE (ρ : Type) (M : Type) [AddCommMonoid M] [Module ℂ M] (ι : Type) where

  Ry : ρ → M
  B : ρ → Finset ι
  W : Submodule ℂ M

  base_mem : ∀ r : ρ, B r = ∅ → Ry r ∈ W

  stepE : ∀ r : ρ, (B r).Nonempty → ∃ (r' : ρ) (S : M → M), (B r').card < (B r).card ∧ Ry r = S (Ry r') ∧
    ∀ g ∈ W, S g ∈ W

variable {M : Type} [AddCommMonoid M] [Module ℂ M] (J : InterfaceE ρ M ι)

private theorem Ry_mem_W_aux : ∀ n : ℕ, ∀ r : ρ, (J.B r).card = n → J.Ry r ∈ J.W := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r hn
    by_cases hB : J.B r = ∅
    · exact J.base_mem r hB
    obtain ⟨r', S, hlt, hRS, hSW⟩ := J.stepE r (Finset.nonempty_iff_ne_empty.mpr hB)
    rw [hRS]
    exact hSW _ (ih _ (lt_of_lt_of_eq hlt hn) r' rfl)

private theorem Ry_mem_W (r : ρ) : J.Ry r ∈ J.W := Ry_mem_W_aux J _ r rfl

private theorem mapsTo_span_of_comm_of_smul (S : M → M) (gens : Set (M → M)) (y : M)
    (hadd : ∀ f g, S (f + g) = S f + S g) (hsmul : ∀ (c : ℂ) f, S (c • f) = c • S f) (hzero : S 0 = 0)
    (hcomm : ∀ Rφ ∈ gens, S (Rφ y) = Rφ (S y)) (lam : ℂ) (hlam : S y = lam • y)
    (hgens : ∀ Rφ ∈ gens, Rφ (lam • y) = lam • Rφ y) :
    ∀ g ∈ Submodule.span ℂ ((fun Rφ : M → M => Rφ y) '' gens),
      S g ∈ Submodule.span ℂ ((fun Rφ : M → M => Rφ y) '' gens) := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Rφ, hRφ, rfl⟩ := hx
    show S (Rφ y) ∈ _
    rw [hcomm Rφ hRφ, hlam, hgens Rφ hRφ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Rφ, hRφ, rfl⟩)
  | zero => rw [hzero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [hadd]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [hsmul]; exact Submodule.smul_mem _ _ hf

end LevelPieces.Recursion

namespace LevelPieces
namespace Assembly

private theorem exists_finset_of_mem_span_range {X : Type*} (Good : (X → ℂ) → Prop) (v : (X → ℂ) → (X → ℂ))
    {z : X → ℂ} (hz : z ∈ Submodule.span ℂ (Set.range fun φ : {φ : X → ℂ // Good φ} => v φ.1)) :
    ∃ (s : Finset (X → ℂ)) (a : (X → ℂ) → ℂ), (∀ φ ∈ s, Good φ) ∧ z = ∑ φ ∈ s, a φ • v φ := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  refine ⟨c.support.image Subtype.val, fun φ => if h : Good φ then c ⟨φ, h⟩ else 0, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hφ
    exact i.2
  · rw [Finset.sum_image fun _ _ _ _ h => Subtype.val_injective h, ← hc, Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [dif_pos i.2, Subtype.coe_eta]

end LevelPieces.Assembly

namespace LevelPieces
namespace PieceDecomposition

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm AutomorphicForm.CuspidalConstituent
open LevelPieces LevelPieces.FinIncl LevelPieces.Pieces LevelPieces.Part LevelPieces.Badness
open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section PieceTest

variable {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) {θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} (hθa : IsArchTestFactor L θa)
include hN hθa

private theorem isFactorizableTestFn_piece (r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    IsFactorizableTestFn L (piece N θa r) :=
  ⟨θa, _, hθa, isFinTestFactor_indicator_doubleCoset L hN r, fun _ => rfl⟩

private theorem continuous_piece (r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Continuous (piece N θa r) :=
  (continuous_and_hasCompactSupport_of_isFactorizableTestFn L _ (isFactorizableTestFn_piece hN hθa r)).1

private theorem hasCompactSupport_piece
    (r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : HasCompactSupport (piece N θa r) :=
  (continuous_and_hasCompactSupport_of_isFactorizableTestFn L _ (isFactorizableTestFn_piece hN hθa r)).2

private theorem continuous_convOp_piece (r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hf : Continuous f) : Continuous (convOp L (piece N θa r) f) := by
  rw [convOp_apply]
  exact (continuous_rightConv_and_contDiff_of_isFactorizableTestFn L f hf _ (isFactorizableTestFn_piece hN hθa r)).1

private theorem convOp_sum_smul_piece (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))
    (c : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f) :
    convOp L (∑ r ∈ s, c r • piece N θa r) f = ∑ r ∈ s, c r • convOp L (piece N θa r) f := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
    NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  funext g
  have key : ∀ y : AdelicGL2 (𝓞 L) L,
      f (g * y) * (∑ r ∈ s, c r • piece N θa r) y = ∑ r ∈ s, c r * (f (g * y) * piece N θa r y) := by
    intro y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hint : ∀ r ∈ s, Integrable (fun y : AdelicGL2 (𝓞 L) L => c r * (f (g * y) * piece N θa r y))
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) := fun r _ =>
    (((hf.comp (continuous_const.mul continuous_id)).mul (continuous_piece hN hθa r)).integrable_of_hasCompactSupport
      (hasCompactSupport_piece hN hθa r).mul_left).const_mul (c r)
  rw [convOp_apply, rightConv_apply]
  simp_rw [key]
  rw [integral_finsetSum s hint, Finset.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, convOp_apply, rightConv_apply, integral_const_mul]

end PieceTest

private theorem convOp_zero_test (f : AdelicGL2 (𝓞 L) L → ℂ) : convOp L (0 : AdelicGL2 (𝓞 L) L → ℂ) f = 0 := by
  rw [convOp_apply]
  exact rightConv_zero_right L f

private def trSum
    (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) (f : AdelicGL2 (𝓞 L) L → ℂ) : AdelicGL2 (𝓞 L) L → ℂ :=
  ∑ b ∈ s, rightTranslate L (adelicFinGLIncl L b) f

private theorem trSum_apply (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) (f : AdelicGL2 (𝓞 L) L → ℂ)
    (g : AdelicGL2 (𝓞 L) L) : trSum s f g = ∑ b ∈ s, f (g * adelicFinGLIncl L b) := by
  simp only [trSum, Finset.sum_apply, rightTranslate_apply]

private theorem continuous_trSum (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hf : Continuous f) : Continuous (trSum s f) := by
  have h : trSum s f = fun g => ∑ b ∈ s, f (g * adelicFinGLIncl L b) := funext (trSum_apply s f)
  rw [h]
  exact continuous_finsetSum s fun b _ => hf.comp (continuous_mul_const (adelicFinGLIncl L b))

private theorem trSum_add (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) (f f' : AdelicGL2 (𝓞 L) L → ℂ) :
    trSum s (f + f') = trSum s f + trSum s f' := by
  funext g
  simp only [trSum_apply, Pi.add_apply, Finset.sum_add_distrib]

private theorem trSum_smul (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) (a : ℂ) (f : AdelicGL2 (𝓞 L) L → ℂ) :
    trSum s (a • f) = a • trSum s f := by
  funext g
  simp only [trSum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

private theorem trSum_zero (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :
    trSum s (0 : AdelicGL2 (𝓞 L) L → ℂ) = 0 := by
  funext g
  simp only [trSum_apply, Pi.zero_apply, Finset.sum_const_zero]

private theorem trSum_sum_smul
    {ι : Type} (s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) (t : Finset ι) (c : ι → ℂ)
    (F : ι → AdelicGL2 (𝓞 L) L → ℂ) : trSum s (∑ i ∈ t, c i • F i) = ∑ i ∈ t, c i • trSum s (F i) := by
  funext g
  simp only [trSum_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

private def RightInv (N : Ideal (𝓞 L)) (f : AdelicGL2 (𝓞 L) L → ℂ) : Prop :=
  ∀ u ∈ AdelicLevel.finiteLevelOne (𝓞 L) L N, ∀ y, f (y * adelicFinGLIncl L u) = f y

private theorem rightInv_convOp_piece (N : Ideal (𝓞 L)) (θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (r : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (f : AdelicGL2 (𝓞 L) L → ℂ) :
    RightInv N (convOp L (piece N θa r) f) := by
  intro u hu y
  rw [convOp_apply, rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
  have hmem : (adelicFinGLIncl L u)⁻¹ ∈ AdelicLevel.levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
    inv_mem (adelicFinGLIncl_mem L hu)
  have hfun : (fun x : AdelicGL2 (𝓞 L) L => piece N θa r ((adelicFinGLIncl L u)⁻¹ * x)) = piece N θa r :=
    funext fun x => (isBiInvariantUnder_piece N θa r _ hmem x).1
  rw [hfun]

private structure SysAt
    (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L)) (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) where
  s : Finset (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
  pure : ∀ b ∈ s, IsPure {w} b
  mem : ∀ b ∈ s, b ∈ finDoubleCoset N (partOn {w} a)
  disj : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' →
    Disjoint (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
      (b' • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
  dec : ∀ y, (finDoubleCoset N (partOn {w} a)).indicator (fun _ => (1 : ℂ)) y =
    ∑ b ∈ s, (b • (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator
      (fun _ => (1 : ℂ)) y

private theorem isCompact_finDoubleCoset (N : Ideal (𝓞 L)) (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    IsCompact (finDoubleCoset N a) := by
  show IsCompact ((AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) * {a} *
    (AdelicLevel.finiteLevelOne (𝓞 L) L N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))))
  exact ((AdelicLevel.isCompact_finiteLevelOne (𝓞 L) L (N := N)).mul isCompact_singleton).mul
    (AdelicLevel.isCompact_finiteLevelOne (𝓞 L) L (N := N))

private theorem nonempty_sysAt {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) (w : HeightOneSpectrum (𝓞 L))
    (a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Nonempty (SysAt N w a) := by
  have h₀ := exists_finset_indicator_eq_sum_indicator_smul_coset
    (AdelicLevel.finiteLevelOne (𝓞 L) L N) (AdelicLevel.isOpen_finiteLevelOne (𝓞 L) L hN)
    (isCompact_finDoubleCoset N (partOn {w} a))
    (fun x hx h hh => (mem_finDoubleCoset_mul_iff hh (partOn {w} a) x).mpr hx)
  obtain ⟨s₀, h₁, h₂, h₃⟩ := h₀
  have h₄ := exists_pure_system {w} a s₀ h₁ h₂
  obtain ⟨s, hpure, hmem, hdisj, hU, -⟩ := h₄
  exact ⟨⟨s, hpure, hmem, hdisj, fun y => (h₃ y).trans (hU y).symm⟩⟩

namespace SysAt

variable {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)} {a : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (sys : SysAt N w a)

private theorem isCosetSystem :
    IsCosetSystem (AdelicLevel.finiteLevelOne (𝓞 L) L N) (finDoubleCoset N (partOn {w} a)) sys.s :=
  isCosetSystem_of_exists (AdelicLevel.finiteLevelOne (𝓞 L) L N) sys.mem sys.dec

private theorem mem_loc : ∀ b ∈ sys.s,
    b ∈ finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) ((AdelicLevel.finComponent (𝓞 L) L w) a)) := by
  rw [← Descent.partOn_singleton_eq w a]
  exact sys.mem

private theorem dec_loc : ∀ y,
    (finDoubleCoset N ((AdelicDock.localEmbed (𝓞 L) L w) ((AdelicLevel.finComponent (𝓞 L) L w) a))).indicator
        (fun _ => (1 : ℂ)) y =
      ∑ b ∈ sys.s,
        (b • ((AdelicLevel.finiteLevelOne (𝓞 L) L N) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)))).indicator
          (fun _ => (1 : ℂ)) y := by
  rw [← Descent.partOn_singleton_eq w a]
  exact sys.dec

end SysAt

private theorem trSum_trSum_comm_of_ne {N : Ideal (𝓞 L)} {w w' : HeightOneSpectrum (𝓞 L)} (hww' : w ≠ w')
    {a a' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (sys : SysAt N w a) (sys' : SysAt N w' a')
    (f : AdelicGL2 (𝓞 L) L → ℂ) : trSum sys.s (trSum sys'.s f) = trSum sys'.s (trSum sys.s f) := by
  funext g
  simp only [trSum_apply]
  exact CrossCommutation.double_sum_comm_of_ne hww' f g sys.pure sys'.pure

private theorem trSum_trSum_comm_same {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hmaxw : AdelicLevel.idealBound (𝓞 L) N w = 1) {a a' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (sys : SysAt N w a)
    (sys' : SysAt N w a') {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : RightInv N f) :
    trSum sys.s (trSum sys'.s f) = trSum sys'.s (trSum sys.s f) := by
  funext g
  simp only [trSum_apply]
  exact LocalCommutation.double_sum_comm w (fun x u hu => hf u hu x) ((AdelicLevel.finComponent (𝓞 L) L w) a)
    ((AdelicLevel.finComponent (𝓞 L) L w) a') sys.pure sys.mem_loc sys.disj sys.dec_loc sys'.pure sys'.mem_loc
    sys'.disj sys'.dec_loc hmaxw g

section Concrete

variable {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) {SK : Finset (HeightOneSpectrum (𝓞 K))}
  (hmaxK : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → ∀ w : v.Extension (𝓞 L), AdelicLevel.idealBound (𝓞 L) N w.1 = 1)

include hmaxK in

private theorem convOp_trSum_eq_trSum_convOp {w' : HeightOneSpectrum (𝓞 L)} (hw' : w'.under (𝓞 K) ∉ SK)
    {a' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (sys' : SysAt N w' a') {ψ : AdelicGL2 (𝓞 L) L → ℂ}
    (hψ : IsUnitFactorizableAbove K L (AdelicLevel.levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK ψ)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f)
    (hfi : RightInv N f) : convOp L ψ (trSum sys'.s f) = trSum sys'.s (convOp L ψ f) :=
  UnitCommutation.convOp_sum_rightTranslate_eq_sum_rightTranslate_convOp N sys'.s hψc hψs hf hfi
    (fun x hx => PureSplitting.exists_split_of_isPure {w'} N sys'.s sys'.pure x
      (PureSplitting.partOn_singleton_glFin_mem_finiteLevelOne hψ hw'
        (hmaxK _ hw' (toExt w') : AdelicLevel.idealBound (𝓞 L) N w' = 1) hx))
    (fun _ hk _ hF => sum_mul_left_eq_sum_of_isCosetSystem sys'.isCosetSystem
      (fun x => mul_mem_finDoubleCoset_iff hk (partOn {w'} a') x) hF)

include hN hmaxK in

private noncomputable def mkInterface {θa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} (hθa : IsArchTestFactor L θa)
    {w' : HeightOneSpectrum (𝓞 L)} (hw' : w'.under (𝓞 K) ∉ SK) {a' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (sys' : SysAt N w' a') :
    Recursion.Interface (AdelicGL2 (𝓞 L) L) (HeightOneSpectrum (𝓞 L)) (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) where
  Cont := Continuous
  Inv := RightInv N
  R := fun r => convOp L (piece N θa r)
  B := badFinset SK N hmaxK
  R_cont := fun r _ hf => continuous_convOp_piece hN hθa r hf
  R_inv := fun r f _ => rightInv_convOp_piece N θa r f
  T := trSum sys'.s
  T_cont := fun _ hf => continuous_trSum sys'.s hf
  step := by
    intro r hr
    obtain ⟨w₀, hw₀⟩ := hr
    have hmaxw₀ : AdelicLevel.idealBound (𝓞 L) N w₀ = 1 := hmaxK _ ((mem_badFinset hmaxK).mp hw₀).1 (toExt w₀)
    obtain ⟨sys₀⟩ := nonempty_sysAt hN w₀ r
    refine ⟨dropOn {w₀} r, trSum sys₀.s, card_badFinset_dropOn_lt hmaxK hw₀, fun f hf => ?_, fun f _ hfi => ?_⟩
    · exact PieceTranslates.convOp_piece_eq_sum_rightTranslate_convOp_piece N θa r (dropOn {w₀} r) sys₀.s
        (fun x => indicator_doubleCoset_eq_sum {w₀} r sys₀.pure sys₀.dec x) (continuous_piece hN hθa _)
        (hasCompactSupport_piece hN hθa _) hf
    · by_cases hw : w₀ = w'
      · subst hw
        exact trSum_trSum_comm_same hmaxw₀ sys' sys₀ hfi
      · exact trSum_trSum_comm_of_ne (Ne.symm hw) sys' sys₀ f
  base := fun r hr f hf hfi =>
    (convOp_trSum_eq_trSum_convOp hmaxK hw' sys' (isUnitFactorizableAbove_piece_of_badFinset_eq_empty hmaxK hN hθa hr)
      (continuous_piece hN hθa r) (hasCompactSupport_piece hN hθa r) hf hfi).symm

include hN hmaxK in

private theorem trSum_convOp_eq_convOp_trSum {w' : HeightOneSpectrum (𝓞 L)} (hw' : w'.under (𝓞 K) ∉ SK)
    {a' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (sys' : SysAt N w' a') {χ : AdelicGL2 (𝓞 L) L → ℂ}
    (hχf : IsFactorizableTestFn L χ)
    (hχbi : ∀ k ∈ AdelicLevel.levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, ∀ x, χ (k * x) = χ x ∧ χ (x * k) = χ x)
    {z : AdelicGL2 (𝓞 L) L → ℂ} (hz : Continuous z) (hzi : RightInv N z) :
    trSum sys'.s (convOp L χ z) = convOp L χ (trSum sys'.s z) := by
  obtain ⟨fa, ff, hfa, hff, hχeq⟩ := hχf
  by_cases h0 : ∃ ginf, fa ginf ≠ 0
  · obtain ⟨ginf, hg⟩ := h0
    have hbi := finFactor_biInvariant (N := N) hχbi hχeq hg
    obtain ⟨s, hs⟩ := exists_finset_eq_sum_smul_piece_of_factor hN fa hff.2 hbi
    have hχ : χ = ∑ r ∈ s, ff r • piece N fa r := by
      rw [← hs]
      funext g
      exact hχeq g
    rw [hχ, convOp_sum_smul_piece hN hfa s ff hz, convOp_sum_smul_piece hN hfa s ff (continuous_trSum sys'.s hz),
      trSum_sum_smul]
    refine Finset.sum_congr rfl fun r _ => ?_
    have key : trSum sys'.s (convOp L (piece N fa r) z) = convOp L (piece N fa r) (trSum sys'.s z) :=
      Recursion.T_comm_R (mkInterface hN hmaxK hfa hw' sys') r z hz hzi
    rw [key]
  · have hfa0 : ∀ ginf, fa ginf = 0 := fun ginf => Classical.byContradiction fun hne => h0 ⟨ginf, hne⟩
    have hχ0 : χ = 0 := funext fun g => by rw [hχeq g, hfa0, zero_mul, Pi.zero_apply]
    rw [hχ0, convOp_zero_test, convOp_zero_test, trSum_zero]

end Concrete

private theorem mapsTo_span_range {X : Type} (Good : (X → ℂ) → Prop) (S : (X → ℂ) → (X → ℂ))
    (v : (X → ℂ) → (X → ℂ) → (X → ℂ)) (y : X → ℂ) (hadd : ∀ f g, S (f + g) = S f + S g)
    (hsmul : ∀ (a : ℂ) f, S (a • f) = a • S f) (hzero : S 0 = 0) (hcomm : ∀ φ, Good φ → S (v φ y) = v φ (S y))
    (lam : ℂ) (hlam : S y = lam • y) (hgens : ∀ φ, Good φ → v φ (lam • y) = lam • v φ y) :
    ∀ g ∈ Submodule.span ℂ (Set.range fun φ : {φ : X → ℂ // Good φ} => v φ.1 y),
      S g ∈ Submodule.span ℂ (Set.range fun φ : {φ : X → ℂ // Good φ} => v φ.1 y) := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    show S (v φ.1 y) ∈ _
    rw [hcomm φ.1 φ.2, hlam, hgens φ.1 φ.2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨φ, rfl⟩)
  | zero => rw [hzero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [hadd]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [hsmul]; exact Submodule.smul_mem _ _ hf

variable (K L) in

private def InputClass (NK : Ideal (𝓞 K)) (tys : ArchTypeFamily L) (χ : AdelicGL2 (𝓞 L) L → ℂ) : Prop :=
  IsFactorizableTestFn L χ ∧ Continuous χ ∧ HasCompactSupport χ ∧ IsArchBiFinite L tys χ ∧
    ∀ k ∈ AdelicLevel.levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
      ∀ x, χ (k * x) = χ x ∧ χ (x * k) = χ x

variable (K L) in

private def GoodTest (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (tys : ArchTypeFamily L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) : Prop :=
  IsUnitFactorizableAboveOfType K L tys
      (AdelicLevel.levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
    Continuous φ ∧ HasCompactSupport φ

private theorem pieces_of_pins (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ) {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)} (hV : IsCuspConstituent L pins ξ V)
    (hU : pins.U (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) =
      AdelicLevel.levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L)
    [FiniteDimensional ℂ
      ↥(V ⊓ levelInvariantSubmodule L pins (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ archCutSubmodule L tys)]
    {y : AdelicGL2 (𝓞 L) L → ℂ}
    (hy : y ∈ V ⊓ levelInvariantSubmodule L pins (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ archCutSubmodule L tys)
    (hy0 : y ≠ 0)
    (hcyc : ∀ v ∈ V ⊓ levelInvariantSubmodule L pins (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ archCutSubmodule L tys,
      v ≠ 0 → y ∈ Submodule.span ℂ
        (Set.range fun χ : {χ : AdelicGL2 (𝓞 L) L → ℂ // InputClass K L NK tys χ} => convOp L χ.1 v))
    (θ : AdelicGL2 (𝓞 L) L → ℂ) (hθf : IsFactorizableTestFn L θ) (hθbf : IsArchBiFinite L tys θ)
    (hθbi : ∀ k ∈ AdelicLevel.levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
      ∀ x, θ (k * x) = θ x ∧ θ (x * k) = θ x) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, GoodTest K L NK SK tys φ) ∧ convOp L θ y = ∑ φ ∈ s, a φ • convOp L φ y := by
  have hN : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥ := aux_map_algebraMap_ne_bot K L hNK
  have hmaxK := aux_idealBound_map_eq_one_of_not_mem K L hNK hNS

  have hEc : ∀ z ∈ V ⊓ levelInvariantSubmodule L pins (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ archCutSubmodule L tys,
      Continuous z := by
    intro z hz
    obtain ⟨⟨hzV, -⟩, -⟩ := hz
    exact aux_continuous_of_mem_of_isCuspConstituent L pins ξ hV hzV
  have hEi : ∀ z ∈ V ⊓ levelInvariantSubmodule L pins (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ archCutSubmodule L tys,
      RightInv (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) z := by
    intro z hz
    obtain ⟨⟨-, hzU⟩, -⟩ := hz
    have hzU' : ∀ x : AdelicGL2 (𝓞 L) L, ∀ u' ∈ pins.U (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK), z (x * u') = z x := hzU
    intro u hu x
    exact hzU' x _ (by rw [hU]; exact adelicFinGLIncl_mem L hu)
  obtain ⟨fa, ff, hfa, hff, hθeq⟩ := hθf
  by_cases hθ0 : ∃ g, θ g ≠ 0
  · obtain ⟨g₀, hg₀⟩ := hθ0
    have hfa0 : fa (AdelicLevel.glArch (𝓞 L) L g₀) ≠ 0 := fun h => hg₀ (by rw [hθeq g₀, h, zero_mul])
    have hff0 : ff (AdelicLevel.glFin (𝓞 L) L g₀) ≠ 0 := fun h => hg₀ (by rw [hθeq g₀, h, mul_zero])
    have hbi := finFactor_biInvariant (N := Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) hθbi hθeq hfa0
    obtain ⟨s, hs⟩ := exists_finset_eq_sum_smul_piece_of_factor hN fa hff.2 hbi
    have hθ : θ = ∑ r ∈ s, ff r • piece (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) fa r := by
      rw [← hs]
      funext g
      exact hθeq g

    let J : Recursion.InterfaceE (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (AdelicGL2 (𝓞 L) L → ℂ)
        (HeightOneSpectrum (𝓞 L)) :=
      { Ry := fun r => convOp L (piece (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) fa r) y
        B := badFinset SK (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) hmaxK
        W := Submodule.span ℂ
          (Set.range fun φ : {φ : AdelicGL2 (𝓞 L) L → ℂ // GoodTest K L NK SK tys φ} => convOp L φ.1 y)
        base_mem := fun r hr =>
          have hgood : GoodTest K L NK SK tys (piece (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) fa r) :=
            ⟨⟨isUnitFactorizableAbove_piece_of_badFinset_eq_empty hmaxK hN hfa hr,
              ArchTypePieces.isArchBiFinite_piece hθeq hff0 hθbf _ r⟩,
              continuous_piece hN hfa r, hasCompactSupport_piece hN hfa r⟩
          Submodule.subset_span ⟨⟨_, hgood⟩, rfl⟩
        stepE := by
          intro r hr
          obtain ⟨w₀, hw₀⟩ := hr
          have hw₀' : w₀.under (𝓞 K) ∉ SK := ((mem_badFinset hmaxK).mp hw₀).1
          obtain ⟨sys₀⟩ := nonempty_sysAt hN w₀ r
          refine ⟨dropOn {w₀} r, trSum sys₀.s, card_badFinset_dropOn_lt hmaxK hw₀, ?_, ?_⟩
          · exact PieceTranslates.convOp_piece_eq_sum_rightTranslate_convOp_piece _ fa r (dropOn {w₀} r) sys₀.s
              (fun x => indicator_doubleCoset_eq_sum {w₀} r sys₀.pure sys₀.dec x) (continuous_piece hN hfa _)
              (hasCompactSupport_piece hN hfa _) (hEc y hy)
          ·
            obtain ⟨lam, hlam⟩ := TranslateEigenvector.exists_sum_rightTranslate_eq_smul
              (V ⊓ levelInvariantSubmodule L pins (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ archCutSubmodule L tys)
              sys₀.s (fun z hz => CutStability.sum_rightTranslate_mem pins ξ hV.1 hU tys sys₀.isCosetSystem hz)
              (InputClass K L NK tys)
              (fun χ hχ z hz => by
                obtain ⟨hχf, -, -, -, hχbi⟩ := hχ
                exact trSum_convOp_eq_convOp_trSum hN hmaxK hw₀' sys₀ hχf hχbi (hEc z hz) (hEi z hz))
              hy hy0 hcyc
            exact mapsTo_span_range (GoodTest K L NK SK tys) (trSum sys₀.s) (fun φ => convOp L φ) y (trSum_add sys₀.s)
              (trSum_smul sys₀.s) (trSum_zero sys₀.s)
              (fun φ hφ => by
                obtain ⟨hφu, hφc, hφs⟩ := hφ
                exact (convOp_trSum_eq_trSum_convOp hmaxK hw₀' sys₀ hφu.1 hφc hφs (hEc y hy) (hEi y hy)).symm)
              lam hlam (fun φ _ => convOp_smul L φ lam y) }

    have hW : convOp L θ y ∈ Submodule.span ℂ
        (Set.range fun φ : {φ : AdelicGL2 (𝓞 L) L → ℂ // GoodTest K L NK SK tys φ} => convOp L φ.1 y) := by
      rw [hθ, convOp_sum_smul_piece hN hfa s ff (hEc y hy)]
      exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Recursion.Ry_mem_W J r)
    exact Assembly.exists_finset_of_mem_span_range (GoodTest K L NK SK tys) (fun φ => convOp L φ y) hW
  · have h0 : ∀ g, θ g = 0 := fun g => Classical.byContradiction fun hne => hθ0 ⟨g, hne⟩
    have hθz : θ = 0 := by
      funext g
      exact h0 g
    refine ⟨∅, fun _ => 0, fun φ hφ => absurd hφ (Finset.notMem_empty φ), ?_⟩
    rw [hθz, convOp_zero_test, Finset.sum_empty]

end LevelPieces.PieceDecomposition

section Conclusion

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm AutomorphicForm.CuspidalConstituent

private theorem LevelPieces.PieceDecomposition.pieces_of_key
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (hNK : NK ≠ ⊥) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent L
      (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ V)
    (y : AdelicGL2 (𝓞 L) L → ℂ)
    (hy : y ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) (hy0 : y ≠ 0)
    (hcyc : ∀ v ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys,
      v ≠ 0 → y ∈ Submodule.span ℂ (Set.range fun χ : {χ : AdelicGL2 (𝓞 L) L → ℂ //
        LevelPieces.PieceDecomposition.InputClass K L NK tys χ} => convOp L χ.1 v)) :
    ∀ θ : AdelicGL2 (𝓞 L) L → ℂ, IsFactorizableTestFn L θ → Continuous θ → HasCompactSupport θ →
      IsArchBiFinite L tys θ →
      (∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        ∀ x, θ (k * x) = θ x ∧ θ (x * k) = θ x) →
      ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
        (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
            (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
          Continuous φ ∧ HasCompactSupport φ) ∧
        convOp L θ y = ∑ φ ∈ s, a φ • convOp L φ y := by
  haveI := finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent L c u d₁ d₂ T hd
    hcov ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) (aux_map_algebraMap_ne_bot K L hNK) tys V hV
  intro θ hθf _ _ hθbf hθbi
  exact pieces_of_pins _ ξ hNK SK hNS tys hV rfl hy hy0 hcyc θ hθf hθbf hθbi

end Conclusion

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel
open AutomorphicForm AutomorphicForm.CuspidalConstituent

namespace LevelPieces

section Core

variable (F : Type) [Field F] [NumberField F]

private def IsTest (θ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsFactorizableTestFn F θ ∧ Continuous θ ∧ HasCompactSupport θ

private noncomputable def convSpan (y : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ {z | ∃ θ, IsTest F θ ∧ z = rightConv F y θ}

private theorem rightConv_mem_convSpan (y : AdelicGL2 (𝓞 F) F → ℂ) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsTest F θ) :
    rightConv F y θ ∈ convSpan F y :=
  Submodule.subset_span ⟨θ, hθ, rfl⟩

private theorem isTest_of_isFactorizableTestFn
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) : IsTest F f :=
  ⟨hf, (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf).1,
    (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf).2⟩

private theorem isTest_comp_inv_mul {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsTest F θ) (t : AdelicGL2 (𝓞 F) F) :
    IsTest F (fun x => θ (t⁻¹ * x)) :=
  ⟨AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn F θ hθ.1 t,
    hθ.2.1.comp (continuous_const.mul continuous_id),
    hθ.2.2.comp_homeomorph (Homeomorph.mulLeft t⁻¹)⟩

private theorem rightTranslate_rightTranslate (t g : AdelicGL2 (𝓞 F) F) (w : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F t (rightTranslate F g w) = rightTranslate F (t * g) w := by
  funext x
  simp only [rightTranslate_apply, mul_assoc]

private theorem rightTranslate_one (w : AdelicGL2 (𝓞 F) F → ℂ) : rightTranslate F 1 w = w := by
  funext x
  simp only [rightTranslate_apply, mul_one]

private theorem rightTranslate_rightConv (w f : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F) :
    rightTranslate F t (rightConv F w f) = rightConv F w (fun x => f (t⁻¹ * x)) := by
  funext g
  rw [rightTranslate_apply]
  exact AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F w f g t

private theorem continuous_and_rightConv_sum_smul {ι : Type} (s : Finset ι) (b : ι → ℂ) (v : ι → AdelicGL2 (𝓞 F) F → ℂ)
    {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : Continuous θ) (hθc : HasCompactSupport θ) :
    (∀ i ∈ s, Continuous (v i)) →
      Continuous (∑ i ∈ s, b i • v i) ∧
        rightConv F (∑ i ∈ s, b i • v i) θ = ∑ i ∈ s, b i • rightConv F (v i) θ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact ⟨continuous_zero, rightConv_zero_left F θ⟩
  · intro i r hir ih hv
    obtain ⟨ihc, ihe⟩ := ih fun j hj => hv j (Finset.mem_insert_of_mem hj)
    have hci : Continuous (b i • v i) := (hv i (Finset.mem_insert_self i r)).const_smul (b i)
    simp only [Finset.sum_insert hir]
    refine ⟨hci.add ihc, ?_⟩
    rw [rightConv_add_left F hci ihc hθ hθc, ihe]
    congr 1
    exact convOp_smul F θ (b i) (v i)

private def transZ
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hVc : ∀ w ∈ V, Continuous w) (y : AdelicGL2 (𝓞 F) F → ℂ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {w | w ∈ V ∧ ∀ (t : AdelicGL2 (𝓞 F) F) (θ : AdelicGL2 (𝓞 F) F → ℂ), IsTest F θ →
    rightConv F (rightTranslate F t w) θ ∈ convSpan F y}
  zero_mem' := by
    refine ⟨V.zero_mem, fun t θ _ => ?_⟩
    rw [rightTranslate_zero]
    have h0 : rightConv F 0 θ = 0 := rightConv_zero_left F θ
    rw [h0]
    exact (convSpan F y).zero_mem
  add_mem' := by
    intro w₁ w₂ h₁ h₂
    refine ⟨V.add_mem h₁.1 h₂.1, fun t θ hθ => ?_⟩
    rw [rightTranslate_add, rightConv_add_left F (continuous_rightTranslate F (hVc w₁ h₁.1) t)
      (continuous_rightTranslate F (hVc w₂ h₂.1) t) hθ.2.1 hθ.2.2]
    exact (convSpan F y).add_mem (h₁.2 t θ hθ) (h₂.2 t θ hθ)
  smul_mem' := by
    intro a w h
    refine ⟨V.smul_mem a h.1, fun t θ hθ => ?_⟩
    rw [rightTranslate_smul]
    have hs : rightConv F (a • rightTranslate F t w) θ = a • rightConv F (rightTranslate F t w) θ :=
      convOp_smul F θ a (rightTranslate F t w)
    rw [hs]
    exact (convSpan F y).smul_mem a (h.2 t θ hθ)

private theorem mem_transZ {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} {hVc : ∀ w ∈ V, Continuous w}
    {y w : AdelicGL2 (𝓞 F) F → ℂ} :
    w ∈ transZ F V hVc y ↔ w ∈ V ∧ ∀ (t : AdelicGL2 (𝓞 F) F) (θ : AdelicGL2 (𝓞 F) F → ℂ), IsTest F θ →
      rightConv F (rightTranslate F t w) θ ∈ convSpan F y :=
  Iff.rfl

private theorem mem_convSpan_of_isCuspConstituent (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hV : IsCuspConstituent F pins ξ V)
    (hVc : ∀ w ∈ V, Continuous w)
    {y y' : AdelicGL2 (𝓞 F) F → ℂ} (hyV : y ∈ V) (hy0 : y ≠ 0) (hy'V : y' ∈ V)
    (s : Finset (AdelicGL2 (𝓞 F) F → ℂ)) (a : (AdelicGL2 (𝓞 F) F → ℂ) → ℂ) (hs : ∀ φ ∈ s, IsTest F φ)
    (hyu : ∑ φ ∈ s, a φ • convOp F φ y = y) (hy'u : ∑ φ ∈ s, a φ • convOp F φ y' = y')
    (estar : ∀ φ ψ : AdelicGL2 (𝓞 F) F → ℂ, IsTest F φ → IsTest F ψ → ∃ χ, IsTest F χ ∧
      ∀ w : AdelicGL2 (𝓞 F) F → ℂ, Continuous w → rightConv F (rightConv F w φ) ψ = rightConv F w χ) :
    y' ∈ convSpan F y := by

  have hZle : transZ F V hVc y ≤ V := fun w hw => ((mem_transZ F).mp hw).1
  have hZsub : IsCuspSubrep F pins ξ (transZ F V hVc y) :=
    { le := fun w hw => hV.1.le (hZle hw)
      rightTranslate_fin_mem := by
        intro g hg w hw
        obtain ⟨hwV, hwt⟩ := (mem_transZ F).mp hw
        refine (mem_transZ F).mpr ⟨hV.1.rightTranslate_fin_mem g hg w hwV, fun t θ hθ => ?_⟩
        rw [rightTranslate_rightTranslate]
        exact hwt (t * g) θ hθ
      rightTranslate_arch_mem := by
        intro v k w hw
        obtain ⟨hwV, hwt⟩ := (mem_transZ F).mp hw
        refine (mem_transZ F).mpr ⟨hV.1.rightTranslate_arch_mem v k w hwV, fun t θ hθ => ?_⟩
        rw [rightTranslate_rightTranslate]
        exact hwt (t * rowIsometryInclAt₀ F v k) θ hθ
      rightConv_mem := by
        intro f tys hf hbf w hw
        obtain ⟨hwV, hwt⟩ := (mem_transZ F).mp hw
        refine (mem_transZ F).mpr ⟨hV.1.rightConv_mem f tys hf hbf w hwV, fun t θ hθ => ?_⟩
        rw [rightTranslate_rightConv]
        obtain ⟨χ, hχ, hop⟩ := estar _ θ (isTest_comp_inv_mul F (isTest_of_isFactorizableTestFn F hf) t) hθ
        rw [hop w (hVc w hwV)]
        have h1 := hwt 1 χ hχ
        rwa [rightTranslate_one] at h1 }

  have hyZ : y ∈ transZ F V hVc y := by
    refine (mem_transZ F).mpr ⟨hyV, fun t θ hθ => ?_⟩
    have h1 : rightTranslate F t y = ∑ φ ∈ s, a φ • rightConv F y (fun x => φ (t⁻¹ * x)) := by
      conv_lhs => rw [← hyu]
      funext x
      simp only [rightTranslate_apply, Finset.sum_apply, Pi.smul_apply, convOp_apply]
      refine Finset.sum_congr rfl fun φ _ => ?_
      rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F y φ x t]
    rw [h1, (continuous_and_rightConv_sum_smul F s a _ hθ.2.1 hθ.2.2 fun φ hφ =>
      (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F y (hVc y hyV) _
        (isTest_comp_inv_mul F (hs φ hφ) t).1).1).2]
    refine (convSpan F y).sum_mem fun φ hφ => (convSpan F y).smul_mem _ ?_
    obtain ⟨χ, hχ, hop⟩ := estar _ θ (isTest_comp_inv_mul F (hs φ hφ) t) hθ
    rw [hop y (hVc y hyV)]
    exact rightConv_mem_convSpan F y hχ

  have hZV : transZ F V hVc y = V := by
    rcases hV.2.2 _ hZsub hZle with h | h
    · exfalso
      rw [h] at hyZ
      exact hy0 ((Submodule.mem_bot ℂ).mp hyZ)
    · exact h
  have hy'Z : y' ∈ transZ F V hVc y := by
    rw [hZV]
    exact hy'V

  have key : (∑ φ ∈ s, a φ • convOp F φ y') ∈ convSpan F y := by
    refine (convSpan F y).sum_mem fun φ hφ => (convSpan F y).smul_mem _ ?_
    rw [convOp_apply]
    have h1 := ((mem_transZ F).mp hy'Z).2 1 φ (hs φ hφ)
    rwa [rightTranslate_one] at h1
  rwa [hy'u] at key

end Core

end LevelPieces

private theorem LevelPieces.mem_convSpan_of_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (hNK : NK ≠ ⊥) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent L
      (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ V)
    (y y' : AdelicGL2 (𝓞 L) L → ℂ)
    (hy : y ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) (hy0 : y ≠ 0)
    (hy' : y' ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) :
    y' ∈ LevelPieces.convSpan L y := by
  obtain ⟨s, a, hs, hsum⟩ := AutomorphicForm.exists_finset_sum_convOp_eq_self_of_isCuspConstituent K L c u d₁ d₂ T
    hd hcov ξ NK hNK SK hNS tys V hV
  have hyV : y ∈ V := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).1).1
  have hy'V : y' ∈ V := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy').1).1
  refine LevelPieces.mem_convSpan_of_isCuspConstituent L _ ξ hV (fun w hw => ?_) hyV hy0 hy'V s a (fun φ hφ => ?_)
    (hsum y hy) (hsum y' hy') (fun φ ψ hφ hψ => ?_)
  ·
    exact aux_continuous_of_mem_of_isCuspConstituent L _ ξ hV hw
  ·
    obtain ⟨hφt, hφc, hφs⟩ := hs φ hφ
    obtain ⟨φa, φf, φS, h₁, h₂, -, -, -, h₆⟩ := hφt.1.2
    exact ⟨⟨φa, φf, h₁, h₂, h₆⟩, hφc, hφs⟩
  ·
    have h := AutomorphicForm.convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul K L ⊥ ∅ φ ψ hφ hψ _ rfl
    refine ⟨_, h.1, fun w hw => ?_⟩
    have h2 := h.2.1 w hw
    simpa only [convOp_apply] using h2

private theorem LevelPieces.mem_span_convOp_of_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (hNK : NK ≠ ⊥) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent L
      (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ V)
    (y y' : AdelicGL2 (𝓞 L) L → ℂ)
    (hy : y ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) (hy0 : y ≠ 0)
    (hy' : y' ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) :
    y' ∈ Submodule.span ℂ (Set.range fun χ : {χ : AdelicGL2 (𝓞 L) L → ℂ //
        IsFactorizableTestFn L χ ∧ Continuous χ ∧ HasCompactSupport χ ∧ IsArchBiFinite L tys χ ∧
          ∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
            ∀ x, χ (k * x) = χ x ∧ χ (x * k) = χ x} => convOp L χ.1 y) := by
  classical

  have hVc : ∀ w ∈ V, Continuous w := fun w hw => aux_continuous_of_mem_of_isCuspConstituent L _ ξ hV hw
  have hyV : y ∈ V := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).1).1
  have hyc : Continuous y := hVc y hyV

  obtain ⟨se, ae, hse, hunit⟩ :=
    AutomorphicForm.exists_finset_sum_convOp_eq_self_of_isCuspConstituent K L c u d₁ d₂ T hd hcov ξ NK hNK SK
      hNS tys V hV

  have htest : ∀ φ ∈ se, LevelPieces.IsTest L φ := fun φ hφ => by
    obtain ⟨hφt, hφc, hφs⟩ := hse φ hφ
    obtain ⟨φa, φf, φS, h₁, h₂, -, -, -, h₆⟩ := hφt.1.2
    exact ⟨⟨φa, φf, h₁, h₂, h₆⟩, hφc, hφs⟩
  have hbi : ∀ φ ∈ se, ∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
      ∀ x, φ (k * x) = φ x ∧ φ (x * k) = φ x := fun φ hφ => (hse φ hφ).1.1.1

  have hconvc : ∀ w : AdelicGL2 (𝓞 L) L → ℂ, Continuous w → ∀ φ ∈ se, Continuous (convOp L φ w) :=
    fun w hw φ hφ =>
      (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn L w hw φ (htest φ hφ).1).1

  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ), W = Submodule.span ℂ (Set.range
      fun χ : {χ : AdelicGL2 (𝓞 L) L → ℂ //
        IsFactorizableTestFn L χ ∧ Continuous χ ∧ HasCompactSupport χ ∧ IsArchBiFinite L tys χ ∧
          ∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
            ∀ x, χ (k * x) = χ x ∧ χ (x * k) = χ x} => convOp L χ.1 y) := ⟨_, rfl⟩
  rw [← hW]

  have hgenW : ∀ χ : AdelicGL2 (𝓞 L) L → ℂ, IsFactorizableTestFn L χ → Continuous χ → HasCompactSupport χ →
      IsArchBiFinite L tys χ →
      (∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        ∀ x, χ (k * x) = χ x ∧ χ (x * k) = χ x) → convOp L χ y ∈ W := by
    intro χ h₁ h₂ h₃ h₄ h₅
    rw [hW]
    exact Submodule.subset_span ⟨⟨χ, h₁, h₂, h₃, h₄, h₅⟩, rfl⟩

  have hsand : ∀ e ∈ se, ∀ e' ∈ se, ∀ θ : AdelicGL2 (𝓞 L) L → ℂ, LevelPieces.IsTest L θ →
      convOp L e (convOp L θ (convOp L e' y)) ∈ W := by
    intro e he e' he' θ hθ

    have hin := AutomorphicForm.convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul K L
      (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK e' θ (htest e' he')
      hθ _ rfl
    have hχr := hin.2.2.2.1 fun k hk x => (hbi e' he' k hk x).2

    have hχd := hin.2.2.2.2.2.1 tys (hse e' he').1.2.2

    have hout := AutomorphicForm.convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul K L
      (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK _ e hin.1 (htest e he)
      _ rfl
    have hχl' := hout.2.2.1 fun k hk x => (hbi e he k hk x).1
    have hχr' := hout.2.2.2.1 hχr

    have hχi' := hout.2.2.2.2.1 tys (hse e he).1.2.1
    have hχd' := hout.2.2.2.2.2.1 tys hχd
    rw [hin.2.1 y hyc, hout.2.1 y hyc]
    exact hgenW _ hout.1.1 hout.1.2.1 hout.1.2.2 ⟨hχi', hχd'⟩ fun k hk x => ⟨hχl' k hk x, hχr' k hk x⟩

  rw [← hunit y' hy']
  refine Submodule.sum_mem _ fun e he => Submodule.smul_mem _ _ ?_
  have hec : Continuous e := (htest e he).2.1
  have hes : HasCompactSupport e := (htest e he).2.2

  have hspan : y' ∈ Submodule.span ℂ {z | ∃ θ, LevelPieces.IsTest L θ ∧ z = rightConv L y θ} :=
    LevelPieces.mem_convSpan_of_mem K L c u d₁ d₂ T hd hcov ξ NK hNK SK hNS tys V hV y y' hy hy0 hy'
  refine (Submodule.span_induction (p := fun z _ => Continuous z ∧ convOp L e z ∈ W) ?_ ?_ ?_ ?_ hspan).2
  · rintro z ⟨θ, hθ, rfl⟩
    refine ⟨(AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn L y hyc θ hθ.1).1, ?_⟩

    have h1 : convOp L θ y = ∑ φ ∈ se, ae φ • convOp L θ (convOp L φ y) := by
      conv_lhs => rw [← hunit y hy]
      exact (LevelPieces.continuous_and_rightConv_sum_smul L se ae (fun φ => convOp L φ y) hθ.2.1 hθ.2.2
        (hconvc y hyc)).2
    have h2 : convOp L e (∑ φ ∈ se, ae φ • convOp L θ (convOp L φ y)) =
        ∑ φ ∈ se, ae φ • convOp L e (convOp L θ (convOp L φ y)) :=
      (LevelPieces.continuous_and_rightConv_sum_smul L se ae (fun φ => convOp L θ (convOp L φ y)) hec hes
        fun φ hφ => (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn L _
          (hconvc y hyc φ hφ) θ hθ.1).1).2
    show convOp L e (convOp L θ y) ∈ W
    rw [h1, h2]
    exact Submodule.sum_mem _ fun φ hφ => Submodule.smul_mem _ _ (hsand e he φ hφ θ hθ)
  · exact ⟨continuous_zero, by rw [convOp_zero]; exact W.zero_mem⟩
  · intro z₁ z₂ _ _ h₁ h₂
    exact ⟨h₁.1.add h₂.1, by rw [convOp_add L hec hes h₁.1 h₂.1]; exact W.add_mem h₁.2 h₂.2⟩
  · intro r z _ hz
    exact ⟨hz.1.const_smul r, by rw [convOp_smul L e r z]; exact W.smul_mem r hz.2⟩

private theorem LevelPieces.exists_finset_convOp_eq_of_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (hNK : NK ≠ ⊥) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent L
      (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ V)
    (y y' : AdelicGL2 (𝓞 L) L → ℂ)
    (hy : y ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) (hy0 : y ≠ 0)
    (hy' : y' ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ χ ∈ s, IsFactorizableTestFn L χ ∧ Continuous χ ∧ HasCompactSupport χ ∧ IsArchBiFinite L tys χ ∧
          ∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
            ∀ x, χ (k * x) = χ x ∧ χ (x * k) = χ x) ∧
        y' = ∑ χ ∈ s, a χ • convOp L χ y :=
  LevelPieces.Assembly.exists_finset_of_mem_span_range _ (fun χ => convOp L χ y)
    (LevelPieces.mem_span_convOp_of_mem K L c u d₁ d₂ T hd hcov ξ NK hNK SK hNS tys V hV y y' hy hy0 hy')

private theorem LevelPieces.rho2_assembled
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (hNK : NK ≠ ⊥) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent L
      (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ V)
    (y y' : AdelicGL2 (𝓞 L) L → ℂ)
    (hy : y ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) (hy0 : y ≠ 0)
    (hy' : y' ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys)
    (hdecomp : ∀ θ : AdelicGL2 (𝓞 L) L → ℂ, IsFactorizableTestFn L θ → Continuous θ → HasCompactSupport θ →
      IsArchBiFinite L tys θ →
      (∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        ∀ x, θ (k * x) = θ x ∧ θ (x * k) = θ x) →
      ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
        (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
            (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
          Continuous φ ∧ HasCompactSupport φ) ∧
        convOp L θ y = ∑ φ ∈ s, a φ • convOp L φ y) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
        y' = ∑ φ ∈ s, a φ • convOp L φ y := by

  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ), W = Submodule.span ℂ (Set.range
      fun φ : {φ : AdelicGL2 (𝓞 L) L → ℂ // IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
          Continuous φ ∧ HasCompactSupport φ} => convOp L φ.1 y) := ⟨_, rfl⟩
  suffices hmem : y' ∈ W by
    subst hW
    exact LevelPieces.Assembly.exists_finset_of_mem_span_range _ (fun φ => convOp L φ y) hmem

  refine (Submodule.span_le.mpr ?_)
    (LevelPieces.mem_span_convOp_of_mem K L c u d₁ d₂ T hd hcov ξ NK hNK SK hNS tys V hV y y' hy hy0 hy')
  rintro _ ⟨⟨χ, h₁, h₂, h₃, h₄, h₅⟩, rfl⟩
  obtain ⟨s, a, hs, hsum⟩ := hdecomp χ h₁ h₂ h₃ h₄ h₅
  show convOp L χ y ∈ W
  rw [hsum, hW]
  exact Submodule.sum_mem _ fun φ hφ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨φ, hs φ hφ⟩, rfl⟩)

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (hNK : NK ≠ ⊥) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L)
    (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent L
      (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ V)
    (y y' : AdelicGL2 (𝓞 L) L → ℂ)
    (hy : y ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) (hy0 : y ≠ 0)
    (hy' : y' ∈ V ⊓ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
        ⊓ archCutSubmodule L tys) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
        y' = ∑ φ ∈ s, a φ • convOp L φ y :=
  LevelPieces.rho2_assembled K L c u d₁ d₂ T hd hcov ξ NK hNK SK hNS tys V hV y y' hy hy0 hy'
    (LevelPieces.PieceDecomposition.pieces_of_key K L c u d₁ d₂ T hd hcov ξ NK hNK SK hNS tys V hV y hy hy0
      fun v hv hv0 => by
        unfold LevelPieces.PieceDecomposition.InputClass
        exact LevelPieces.mem_span_convOp_of_mem K L c u d₁ d₂ T hd hcov ξ NK hNK SK hNS tys V hV v y hv hv0 hy)

end S_AutomorphicForm_exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero (solution)
