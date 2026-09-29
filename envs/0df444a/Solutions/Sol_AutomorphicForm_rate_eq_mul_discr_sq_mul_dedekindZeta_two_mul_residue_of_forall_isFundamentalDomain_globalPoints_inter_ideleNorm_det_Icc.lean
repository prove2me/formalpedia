-- Prove2me | solution 1 for AutomorphicForm.rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_globalPoints_inter_ideleNorm_det_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6d392bd0-2643-575b-89bb-2187bdeaedca

import Theorems.Thm_AutomorphicForm_rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one
import Theorems.Thm_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div
import Theorems.Thm_NumberField_AdelicBox_measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
import Theorems.Thm_NumberField_TateGlobal_exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_globalPoints_inter_ideleNorm_det_Icc
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "AutomorphicForm.cpowChar_apply_val AutomorphicForm.whittakerCoefficient_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "ContinuousAddEquiv.preimage_mulLeft_smul NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc globalPoints unipotentGL2 measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one glBorelOf localIntegralSet isCompact_localIntegralSet localGLBorel borelSpace_localGLBorel adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain"
namespace MassGL2Reduce
p2m_open "AutomorphicForm"

section InvInvariant

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem isInvInvariant_of_isMulRightInvariant (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    μ.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h3 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h4 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h3
  have h5 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h4
  rw [hc, h5, one_smul]

end InvInvariant

section FD

variable {G : Type*} [Group G] [MeasurableSpace G]

theorem isFundamentalDomain_inv_of_op [MeasurableInv G] (Γ : Subgroup G) (D : Set G) (μ : Measure G)
    [μ.IsInvInvariant] (h : IsFundamentalDomain Γ.op D μ) :
    IsFundamentalDomain Γ D⁻¹ μ := by
  have hf : Measure.QuasiMeasurePreserving (Inv.inv : G → G) μ μ :=
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving
  let e : Γ.op → Γ := fun g => ⟨(MulOpposite.unop (g : Gᵐᵒᵖ))⁻¹, by
    have hg : (g : Gᵐᵒᵖ) ∈ Γ.op := g.2
    rw [Subgroup.mem_op] at hg
    exact Γ.inv_mem hg⟩
  have he : Function.Bijective e := by
    constructor
    · intro g₁ g₂ h12
      have : (MulOpposite.unop (g₁ : Gᵐᵒᵖ))⁻¹ = (MulOpposite.unop (g₂ : Gᵐᵒᵖ))⁻¹ := congrArg Subtype.val h12
      have : MulOpposite.unop (g₁ : Gᵐᵒᵖ) = MulOpposite.unop (g₂ : Gᵐᵒᵖ) := inv_injective this
      exact Subtype.ext (MulOpposite.unop_injective this)
    · intro γ
      refine ⟨⟨MulOpposite.op ((γ : G)⁻¹), by rw [Subgroup.mem_op, MulOpposite.unop_op]; exact Γ.inv_mem γ.2⟩, ?_⟩
      apply Subtype.ext
      simp [e]
  have hef : ∀ g : Γ.op, Function.Semiconj (Inv.inv : G → G) (fun x => e g • x) (fun x => g • x) := by
    intro g x
    show (e g • x)⁻¹ = g • x⁻¹
    rw [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, MulOpposite.smul_eq_mul_unop, mul_inv_rev]
    simp [e]
  have := h.preimage_of_equiv hf he hef
  simpa only [Set.inv_preimage] using this

end FD

section Discrete

variable (K : Type) [Field K] [NumberField K]

theorem exists_isOpen_forall_algebraMap_mem_eq_zero :
    ∃ U : Set (AdeleRing (𝓞 K) K), IsOpen U ∧ (0 : AdeleRing (𝓞 K) K) ∈ U ∧
      ∀ ξ : K, algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ U → ξ = 0 := by
  obtain ⟨C, hC, h0C⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 K) K)
  have hfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hC
  set S : Set K := {ξ : K | algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ C} with hS
  set T : Set (AdeleRing (𝓞 K) K) := (algebraMap K (AdeleRing (𝓞 K) K)) '' (S \ {0}) with hT
  have hTfin : T.Finite := (hfin.subset Set.diff_subset).image _
  have hTclosed : IsClosed T := hTfin.isClosed
  refine ⟨interior C \ T, isOpen_interior.sdiff hTclosed, ⟨mem_interior_iff_mem_nhds.2 h0C, ?_⟩, ?_⟩
  · rintro ⟨ξ, ⟨hξS, hξ0⟩, hξ⟩
    have hinj := NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)
    have : ξ = 0 := hinj (by rw [hξ, map_zero])
    exact hξ0 this
  · intro ξ hξ
    by_contra hne
    have hξC : algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ C := interior_subset hξ.1
    exact hξ.2 ⟨ξ, ⟨hξC, hne⟩, rfl⟩

theorem discreteTopology_globalPoints_range :
    DiscreteTopology ((AutomorphicForm.globalPoints (𝓞 K) K).range) := by
  obtain ⟨U, hUo, h0U, hU⟩ := exists_isOpen_forall_algebraMap_mem_eq_zero K
  let V : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
    {g | ∀ i j : Fin 2, (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
      (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ U}
  have hVo : IsOpen V := by
    have : V = ⋂ i : Fin 2, ⋂ j : Fin 2, (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) =>
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) ⁻¹' U := by
      ext g; simp [V]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hUo.preimage ?_
    have hc : Continuous fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) =>
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j :=
      (Continuous.matrix_elem Units.continuous_val i j)
    exact hc.sub continuous_const
  apply discreteTopology_of_isOpen_singleton_one
  have hpre : ((↑) : (AutomorphicForm.globalPoints (𝓞 K) K).range → GL (Fin 2) (AdeleRing (𝓞 K) K)) ⁻¹' V =
      {1} := by
    ext ⟨γ, γ₀, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hV
      have hγ₀ : γ₀ = 1 := by
        ext i j
        have h1 := hV i j
        have hval : ((AutomorphicForm.globalPoints (𝓞 K) K γ₀ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
            algebraMap K (AdeleRing (𝓞 K) K) ((γ₀ : Matrix (Fin 2) (Fin 2) K) i j) := rfl
        rw [hval] at h1
        have h1' : algebraMap K (AdeleRing (𝓞 K) K)
            ((γ₀ : Matrix (Fin 2) (Fin 2) K) i j - (1 : Matrix (Fin 2) (Fin 2) K) i j) ∈ U := by
          rw [map_sub]
          convert h1 using 2
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [Matrix.one_apply_ne hij]
        have := hU _ h1'
        rw [sub_eq_zero] at this
        simpa using this
      subst hγ₀
      exact Subtype.ext (map_one _)
    · intro h1
      have : γ₀ = 1 := by
        have h1' : (AutomorphicForm.globalPoints (𝓞 K) K γ₀ : GL (Fin 2) (AdeleRing (𝓞 K) K)) = 1 :=
          congrArg Subtype.val h1
        have hinj : Function.Injective (AutomorphicForm.globalPoints (𝓞 K) K) := by
          intro a b hab
          ext i j
          have := congrArg (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) =>
            (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) hab
          exact NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K) this
        exact hinj (by rw [h1', map_one])
      subst this
      intro i j
      simp only [map_one, Units.val_one, sub_self]
      exact h0U
  rw [← hpre]
  exact hVo.preimage continuous_subtype_val

end Discrete

section Slab

variable (K : Type) [Field K] [NumberField K]

theorem ideleNorm_det_inv (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g⁻¹) =
      (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g))⁻¹ := by
  rw [map_inv]
  have hpos := NumberField.TateGlobal.ideleNorm_pos (F := K) (Matrix.GeneralLinearGroup.det g)
  have hmul := NumberField.TateGlobal.ideleNorm_mul (F := K) (Matrix.GeneralLinearGroup.det g)⁻¹
    (Matrix.GeneralLinearGroup.det g)
  rw [inv_mul_cancel] at hmul
  have h1 : NumberField.TateGlobal.ideleNorm K 1 = 1 := by
    have := NumberField.TateGlobal.ideleNorm_mul (F := K) 1 1
    rw [one_mul] at this
    have hp := NumberField.TateGlobal.ideleNorm_pos (F := K) 1
    field_simp at this
    linarith [this]
  rw [h1] at hmul
  field_simp
  linarith [hmul]

theorem inv_slab (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    {t : GL (Fin 2) (AdeleRing (𝓞 K) K) |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det t) ∈ Set.Icc a b}⁻¹ =
      {t : GL (Fin 2) (AdeleRing (𝓞 K) K) |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det t) ∈ Set.Icc b⁻¹ a⁻¹} := by
  ext t
  simp only [Set.mem_inv, Set.mem_setOf_eq, Set.mem_Icc, ideleNorm_det_inv]
  have hpos := NumberField.TateGlobal.ideleNorm_pos (F := K) (Matrix.GeneralLinearGroup.det t)
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [inv_le_comm₀ hb hpos]; exact h2
    · rw [le_inv_comm₀ hpos ha]; exact h1
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_inv_comm₀ ha hpos]; exact h2
    · rw [inv_le_comm₀ hpos hb]; exact h1

end Slab

section Arithmetic

variable (K : Type) [Field K] [NumberField K]

theorem two_pow_ennreal (k : ℕ) : (2 : ℝ≥0∞) ^ k = ENNReal.ofReal ((2 : ℝ) ^ k) := by
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  simp

theorem inv_two_pow_ennreal (k : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ k = ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) := by
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
  simp

theorem constant_identity (ζ : ℝ) :
    (2 : ℝ≥0∞) ^ (4 * NumberField.InfinitePlace.nrComplexPlaces K + NumberField.InfinitePlace.nrRealPlaces K) *
        ENNReal.ofReal ((2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K) *
        ENNReal.ofReal ζ *
      ENNReal.ofReal ((NumberField.classNumber K : ℝ) * NumberField.Units.regulator K /
        (2 ^ NumberField.InfinitePlace.nrComplexPlaces K * (NumberField.Units.torsionOrder K : ℝ))) *
      ((2 : ℝ≥0∞)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
          ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|)) ^ 3 =
    ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * ζ * NumberField.dedekindZeta_residue K) := by
  set r₁ := NumberField.InfinitePlace.nrRealPlaces K
  set r₂ := NumberField.InfinitePlace.nrComplexPlaces K
  set h : ℝ := (NumberField.classNumber K : ℝ)
  set R : ℝ := NumberField.Units.regulator K
  set w : ℝ := (NumberField.Units.torsionOrder K : ℝ)
  set d : ℝ := (NumberField.discr K : ℝ)
  have hRpos : 0 < R := NumberField.Units.regulator_pos K
  have hhpos : 0 < h := by
    have := NumberField.classNumber_pos (K := K)
    positivity
  have hwpos : 0 < w := by
    have := NumberField.Units.torsionOrder_pos (K := K)
    positivity
  have hd0 : d ≠ 0 := Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)
  have hdabs : 0 < |d| := abs_pos.mpr hd0
  have hsq : 0 < Real.sqrt |d| := Real.sqrt_pos_of_pos hdabs
  have hres : NumberField.dedekindZeta_residue K = (2 ^ r₁ * (2 * Real.pi) ^ r₂ * R * h) / (w * Real.sqrt |d|) :=
    NumberField.dedekindZeta_residue_def K
  rcases le_or_gt 0 ζ with hζ | hζ
  ·
    rw [two_pow_ennreal, inv_two_pow_ennreal, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hres]
    set A : ℝ := (2 : ℝ) ^ r₂ with hA
    set q : ℝ := Real.sqrt |d| with hq
    have hApos : 0 < A := by positivity
    have hsq2 : q ^ 2 = |d| := Real.sq_sqrt hdabs.le
    have hd2 : d ^ 2 = q ^ 4 := by
      rw [← sq_abs d, ← hsq2]; ring
    have h24 : (2 : ℝ) ^ (4 * r₂ + r₁) = A ^ 4 * 2 ^ r₁ := by
      rw [pow_add, mul_comm 4 r₂, pow_mul, hA]
    have hhalf : (2⁻¹ : ℝ) ^ r₂ = A⁻¹ := by
      rw [inv_pow, hA]
    rw [hd2, h24, hhalf]
    field_simp
  ·
    have h0 : ENNReal.ofReal ζ = 0 := ENNReal.ofReal_eq_zero.2 hζ.le
    rw [h0, mul_zero, zero_mul, zero_mul]
    symm
    apply ENNReal.ofReal_eq_zero.2
    have hρ : 0 < NumberField.dedekindZeta_residue K := NumberField.dedekindZeta_residue_pos K
    have : d ^ 2 * ζ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg d) hζ.le
    exact mul_nonpos_of_nonpos_of_nonneg this hρ.le

end Arithmetic

end AutomorphicForm.MassGL2Reduce

end

open AutomorphicForm.MassGL2Reduce in
attribute [local instance] NumberField.AdelicHaar.glBorel in
theorem solution
    (K : Type) [Field K] [NumberField K]

    (τa : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hτa : @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (hτf : ∀ v, @Measure.IsHaarMeasure (GL (Fin 2) (v.adicCompletion K)) _ _
      (AutomorphicForm.localGLBorel K v) (τf v))

    (n : ℕ) (e : Fin n → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
      LinearIndependent ℝ e ∧
        Submodule.span ℝ (Set.range e) = ⊤ ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) τa =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                  Algebra.trace ℝ (InfiniteAdeleRing K) (Matrix.trace (e i * e j))).det|)) •
                Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)| ^ 2)⁻¹))

    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure) (cτ : ℝ) (hcτ : 0 < cτ)
    (hτprod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] Wa τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (WS v) (τf v)) →
        (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cτ * (∫ x, Wa x ∂τa) * ∏ v ∈ S, ∫ y, WS v y ∂(τf v))

    (R : ENNReal)
    (hD : ∀ D : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)),
      IsFundamentalDomain ((AutomorphicForm.globalPoints (𝓞 K) K).range).op D τ →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det t) ∈ Set.Icc a b}) =
          R * ENNReal.ofReal (Real.log (b / a))) :
    R = ENNReal.ofReal cτ * s * (∏ v ∈ S₀, τf v (AutomorphicForm.localIntegralSet K v)) *
      ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
        NumberField.dedekindZeta_residue K) := by
  classical

  letI mA : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  letI mI : MeasurableSpace (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.ideleBorel K
  haveI : BorelSpace (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.borelSpace_ideleBorel K
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) := NumberField.AdelicHaar.borelSpace_glBorel _ _ _
  haveI := hτ
  haveI : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  set μ₀ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K)) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ₀def
  haveI hμ₀ : μ₀.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI hμ₀r : μ₀.IsMulRightInvariant := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K

  have hτsm : τ = τ.haarScalarFactor μ₀ • μ₀ := Measure.isMulLeftInvariant_eq_smul τ μ₀
  haveI hτr : τ.IsMulRightInvariant := by
    rw [hτsm]; infer_instance
  haveI hμ₀inv : μ₀.IsInvInvariant := isInvInvariant_of_isMulRightInvariant μ₀

  set Γ : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)) := (AutomorphicForm.globalPoints (𝓞 K) K).range with hΓ
  have hdisc : DiscreteTopology Γ := discreteTopology_globalPoints_range K
  obtain ⟨D₀, hD₀m, -, hD₀all⟩ :=
    MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology Γ hdisc
  have hD₀τ : IsFundamentalDomain Γ.op D₀ τ := hD₀all τ
  have hD₀μ : IsFundamentalDomain Γ.op D₀ μ₀ := hD₀all μ₀

  have hRtop : R ≠ ⊤ := by
    set slab : ℝ → ℝ → Set (GL (Fin 2) (AdeleRing (𝓞 K) K)) := fun a b =>
      {t | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det t) ∈ Set.Icc a b} with hslab
    have h12 := hD D₀ hD₀τ 1 2 one_pos (by norm_num)

    have hleft : IsFundamentalDomain Γ D₀⁻¹ μ₀ := isFundamentalDomain_inv_of_op Γ D₀ μ₀ hD₀μ
    have hleft' : IsFundamentalDomain Γ D₀⁻¹ (μ₀.restrict (slab 2⁻¹ 1)) :=
      hleft.mono Measure.restrict_le_self.absolutelyContinuous
    have hfin : μ₀ (D₀⁻¹ ∩ slab 2⁻¹ 1) < ⊤ :=
      AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K 2⁻¹ 1
        (by norm_num) (by norm_num) D₀⁻¹ hleft'
    have hset : (D₀ ∩ slab 1 2)⁻¹ = D₀⁻¹ ∩ slab 2⁻¹ 1 := by
      rw [Set.inter_inv, hslab]
      simp only
      rw [inv_slab K 1 2 one_pos two_pos, inv_one]
    have hμfin : μ₀ (D₀ ∩ slab 1 2) < ⊤ := by
      rw [← Measure.measure_inv μ₀ (D₀ ∩ slab 1 2), hset]; exact hfin
    have hτfin : τ (D₀ ∩ slab 1 2) < ⊤ := by
      rw [hτsm, Measure.smul_apply]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top hμfin
    have hlog : ENNReal.ofReal (Real.log (2 / 1)) ≠ 0 := by
      rw [div_one]; exact (ENNReal.ofReal_pos.2 (Real.log_pos one_lt_two)).ne'
    intro hR
    rw [hR, ENNReal.top_mul hlog] at h12
    exact (lt_irrefl _) (h12 ▸ hτfin)

  obtain ⟨Ω₀, hΩ₀m, hΩ₀all⟩ :=
    NumberField.TateGlobal.exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap K

  set μA : Measure (AdeleRing (𝓞 K) K) := adelicAddHaar (𝓞 K) K with hμAdef
  haveI hμA : μA.IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  set ν : Measure (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.idelicHaar K with hνdef
  haveI hν : ν.IsHaarMeasure := NumberField.Idele.isHaarMeasure_idelicHaar K
  obtain ⟨ha0, hatop, hbox⟩ :=
    NumberField.AdelicBox.measure_adelicBox_eq_measure_unitCubeBox_mul_inv_two_pow_mul_sqrt_discr K μA hμA
  obtain ⟨hV0, hVtop, hrateI⟩ :=
    NumberField.TateGlobal.measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div
      K ν hν
  obtain ⟨hs, hF⟩ :=
    AutomorphicForm.measure_pow_three_mul_measure_mul_lintegral_mul_apply_col_det_eq_mul_dedekindZeta_two_mul_lintegral_of_forall_lintegral_mul_unipotentGL2_eq_one
      K τa hτa τf hτf n e s harch S₀ τ hτ cτ hcτ hτprod μA hμA ν hν

  set a : ℝ≥0∞ := μA {x | ((∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
          x.2 ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K} with hadef
  set V : ℝ≥0∞ := ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} with hVdef
  set P : ℝ≥0∞ := ∏ v ∈ S₀, τf v (AutomorphicForm.localIntegralSet K v) with hPdef
  set Z : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (4 * NumberField.InfinitePlace.nrComplexPlaces K +
        NumberField.InfinitePlace.nrRealPlaces K) *
      ENNReal.ofReal ((2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K) *
      ENNReal.ofReal (NumberField.dedekindZeta K 2).re with hZdef
  set Kc : ℝ≥0∞ := ENNReal.ofReal cτ * s * P * Z with hKcdef
  set CI : ℝ≥0∞ := V * ENNReal.ofReal ((NumberField.classNumber K : ℝ) * NumberField.Units.regulator K /
      (2 ^ NumberField.InfinitePlace.nrComplexPlaces K * (NumberField.Units.torsionOrder K : ℝ))) with hCIdef
  set Bx : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
      ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) with hBxdef

  have hPtop : P ≠ ⊤ := by
    rw [hPdef]
    refine ENNReal.prod_ne_top fun v _ => ?_
    letI := AutomorphicForm.localGLBorel K v
    haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.borelSpace_localGLBorel K v
    haveI := hτf v
    exact ((AutomorphicForm.isCompact_localIntegralSet K v).measure_lt_top (μ := τf v)).ne
  have hZtop : Z ≠ ⊤ := by
    rw [hZdef]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hKctop : Kc ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs) hPtop) hZtop
  have haV0 : a ^ 3 * V ≠ 0 := mul_ne_zero (pow_ne_zero _ ha0) hV0
  have haVtop : a ^ 3 * V ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hatop) hVtop

  set κ : ℝ≥0∞ := (a ^ 3 * V)⁻¹ * Kc with hκdef
  have hκtop : κ ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 haV0) hKctop
  have hfib : ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ≥0∞)
      (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞),
      Measurable w → Measurable Ψ →
      (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μA = 1) →
      ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
          Matrix.GeneralLinearGroup.det g) ∂τ =
        κ * ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
          ∂(Measure.pi fun _ : Fin 2 => μA) := by
    intro w Ψ hw hΨ hw1
    have h := hF w Ψ hw hΨ hw1

    set L := ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
          Matrix.GeneralLinearGroup.det g) ∂τ with hL
    set Rr := ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
          ∂(Measure.pi fun _ : Fin 2 => μA) with hRr
    change a ^ 3 * V * L = Kc * Rr at h
    calc L = (a ^ 3 * V)⁻¹ * (a ^ 3 * V * L) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel haV0 haVtop, one_mul]
      _ = κ * Rr := by rw [h, hκdef]; ring

  have hW :=
    AutomorphicForm.rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc
      K τ hτ hτr μA hμA ν hν κ hκtop hfib R hRtop hD D₀ hD₀m hD₀τ CI
      (ENNReal.mul_ne_top hVtop ENNReal.ofReal_ne_top) hrateI Ω₀ hΩ₀m (hΩ₀all ν)
      (NumberField.AdelicBox.adelicBox K) (NumberField.AdelicBox.measurableSet_adelicBox K)
      (NumberField.AdelicBox.isAddFundamentalDomain_adelicBox K μA)

  rw [hW, hbox]
  change (a ^ 3 * V)⁻¹ * (ENNReal.ofReal cτ * s * P * Z) * (V * _) * (a * Bx) ^ 3 = ENNReal.ofReal cτ * s * P * _
  have hcancel : (a ^ 3 * V)⁻¹ * (V * a ^ 3) = 1 := by
    rw [mul_comm V, ENNReal.inv_mul_cancel haV0 haVtop]
  calc (a ^ 3 * V)⁻¹ * (ENNReal.ofReal cτ * s * P * Z) *
        (V * ENNReal.ofReal ((NumberField.classNumber K : ℝ) * NumberField.Units.regulator K /
          (2 ^ NumberField.InfinitePlace.nrComplexPlaces K * (NumberField.Units.torsionOrder K : ℝ)))) *
        (a * Bx) ^ 3
        = ENNReal.ofReal cτ * s * P *
          (Z * ENNReal.ofReal ((NumberField.classNumber K : ℝ) * NumberField.Units.regulator K /
            (2 ^ NumberField.InfinitePlace.nrComplexPlaces K * (NumberField.Units.torsionOrder K : ℝ))) *
            Bx ^ 3) * ((a ^ 3 * V)⁻¹ * (V * a ^ 3)) := by ring
    _ = ENNReal.ofReal cτ * s * P *
          ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
            NumberField.dedekindZeta_residue K) := by
          rw [hcancel, mul_one, hZdef, hBxdef, constant_identity K]

end S_AutomorphicForm_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_globalPoints_inter_ideleNorm_det_Icc
end P2MW
export P2MW.S_AutomorphicForm_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_globalPoints_inter_ideleNorm_det_Icc (solution)
