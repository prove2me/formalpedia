-- Prove2me | solution 1 for AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6272ce50-f472-52a5-9dbc-c0bd64253065

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay
import Theorems.Thm_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite
import Theorems.Thm_AutomorphicForm_exists_sum_prod_mul_of_rightTranslatesSpanFinite
import Theorems.Thm_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Theorems.Thm_MeasureTheory_Measure_exists_eq_prod_of_forall_map_add_left
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply
import Theorems.Thm_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply
import Theorems.Thm_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

open scoped ENNReal NNReal Pointwise

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsGlobalAddChar AdelicGL2 IsUnitaryChar unipotentGL2 unipotentGL2_coe IsInducedSection inducedSectionSubmodule mem_borelSubgroup_iff borelDiagFst borelDiagSnd borelDiagFst_apply_val borelDiagSnd_apply_val adelicBorel cpowChar_apply_val etaFst etaSnd etaFst_apply etaSnd_apply gl2Weyl gl2Weyl_val gl2Weyl_inv adelicWeyl archRowIsometrySubgroup IsArchKFinite archMatrixPiEquiv archMatrixUpdate archMatrixPiEquiv_archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne archMatrixInclHom archGLIncl adelicMatrixProdEquiv adelicArchGLIncl adelicArchGLInclAt WindowedSiegel.rowIsometrySubgroup weylIntertwiningIntegrand_integrable_of_re_gt_half ComplexIwasawa.weyl_mul_unipotent_mul_eq_borel_mul_kC ComplexIwasawa.botP ComplexIwasawa.botQ ComplexIwasawa.radC ComplexIwasawa.kC ComplexIwasawa.kC_mem_specialUnitaryGroup ComplexIwasawa.norm_fourierIntegral_cpow_radC_mul_le_polyDecay exists_sum_prod_mul_of_rightTranslatesSpanFinite RealIwasawa.norm_fourierIntegral_cpow_rad_mul_le_polyDecay ComplexIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kC_apply RealIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kR_apply weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half"
namespace WeylIntegrable
p2m_open "AutomorphicForm"

section ModFin

variable (F : Type) [Field F] [NumberField F]

private def intLattice : AddSubgroup (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) where
  carrier := integralFiniteAdeles (𝓞 F) F
  zero_mem' := fun _ => zero_mem _
  add_mem' hx hy := fun v => add_mem (hx v) (hy v)
  neg_mem' hx := fun v => neg_mem (hx v)

@[scoped simp] private theorem coe_intLattice : (intLattice F : Set (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) = integralFiniteAdeles (𝓞 F) F := rfl

private def dilate (y : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : AddSubgroup (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) := (intLattice F).map (DistribSMul.toAddMonoidHom (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) (y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)))

private theorem coe_dilate (y : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : (dilate F y : Set (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) = (y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) • integralFiniteAdeles (𝓞 F) F := by
  ext z; simp [dilate, Set.mem_smul_set]
end ModFin

section Lattices

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

private theorem fa_mul_apply (a b : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : (a * b) v = a v * b v := rfl

private theorem mem_intLattice_iff (t : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) : t ∈ intLattice F ↔ ∀ v, Valued.v (t v) ≤ 1 := Iff.rfl

private theorem mem_integralFiniteAdeles_iff' (t : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) : t ∈ integralFiniteAdeles (𝓞 F) F ↔ ∀ v, Valued.v (t v) ≤ 1 := Iff.rfl

private theorem valued_ne_zero_of_unit (y : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : Valued.v ((y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v) ≠ 0 := by
  intro h
  have h1 : Valued.v (((y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) * ((y⁻¹ : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))) v) = 1 := by rw [Units.mul_inv]; exact map_one _
  rw [fa_mul_apply, map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem apply_ne_zero_of_unit (y : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : (y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v ≠ 0 := fun h =>
  valued_ne_zero_of_unit F y v (by rw [h, map_zero])

private theorem mem_dilate_iff (y : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) (t : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) : t ∈ dilate F y ↔ ∀ v, Valued.v (t v) ≤ Valued.v ((y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v) := by
  rw [← SetLike.mem_coe, coe_dilate, Set.mem_smul_set]
  constructor
  · rintro ⟨s, hs, rfl⟩ v
    rw [smul_eq_mul, fa_mul_apply, map_mul]
    exact mul_le_of_le_one_right' ((mem_integralFiniteAdeles_iff' F s).mp hs v)
  · intro h
    refine ⟨((y⁻¹ : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) * t, (mem_integralFiniteAdeles_iff' F _).mpr fun v => ?_, ?_⟩
    · rw [fa_mul_apply, map_mul]
      have hy := valued_ne_zero_of_unit F y v
      have hyv : (y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v * ((y⁻¹ : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v = 1 := by rw [← fa_mul_apply, Units.mul_inv]; rfl
      have hinv : Valued.v (((y⁻¹ : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v) = (Valued.v ((y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))⁻¹ := by
        rw [← inv_eq_of_mul_eq_one_right hyv, map_inv₀]
      rw [hinv]
      calc (Valued.v ((y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))⁻¹ * Valued.v (t v) ≤ (Valued.v ((y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))⁻¹ * Valued.v ((y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v) :=
            mul_le_mul' le_rfl (h v)
        _ = 1 := inv_mul_cancel₀ hy
    · show (y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) * (((y⁻¹ : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) * t) = t
      rw [← mul_assoc, Units.mul_inv, one_mul]

private theorem intLattice_le_dilate {y : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ} (hy : ∀ v, 1 ≤ Valued.v ((y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v)) : intLattice F ≤ dilate F y := fun t ht =>
  (mem_dilate_iff F y t).mpr fun v => (((mem_intLattice_iff F t).mp ht v).trans (hy v))

private theorem isCompact_dilate (y : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : IsCompact (dilate F y : Set (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) := by
  rw [coe_dilate]
  exact (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

private theorem relIndex_dilate_ne_zero (y : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : (intLattice F).relIndex (dilate F y) ≠ 0 := by
  haveI : CompactSpace (dilate F y) := isCompact_iff_compactSpace.mp (isCompact_dilate F y)
  have hopen : IsOpen (((intLattice F).addSubgroupOf (dilate F y) : AddSubgroup (dilate F y)) : Set (dilate F y)) :=
    (isOpen_integralFiniteAdeles F).preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact AddSubgroup.index_ne_zero_of_finite

private def unif (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : F := Classical.choose (v.valuation_exists_uniformizer F)

private theorem valuation_unif (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : v.valuation F (unif F v) = exp (-1 : ℤ) := Classical.choose_spec (v.valuation_exists_uniformizer F)

private theorem valued_unif (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : Valued.v ((unif F v : F) : v.adicCompletion F) = exp (-1 : ℤ) := by
  rw [valuedAdicCompletion_eq_valuation', valuation_unif]

private theorem unif_coe_ne_zero (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : ((unif F v : F) : v.adicCompletion F) ≠ 0 := fun h => by
  have := valued_unif F v; rw [h, map_zero] at this; exact exp_ne_zero this.symm

private def unifFun (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : v.adicCompletion F := ((unif F v : F) : v.adicCompletion F) ^ (-(k v : ℤ))

private theorem valued_unifFun (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : Valued.v (unifFun F k v) = exp (k v : ℤ) := by
  rw [unifFun, map_zpow₀, valued_unif, ← exp_zsmul]; congr 1; ring

private theorem unifFun_of_notMem (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) {v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))} (hv : v ∉ k.support) : unifFun F k v = 1 := by
  rw [unifFun, Finsupp.notMem_support_iff.mp hv]; simp

private def unifIdele (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ where
  val := RestrictedProduct.mk (unifFun F k) (Filter.eventually_cofinite.mpr
    ((k.support.finite_toSet).subset fun v hv => by
      by_contra h; exact hv (by rw [unifFun_of_notMem F k h]; exact one_mem _)))
  inv := RestrictedProduct.mk (fun v => (unifFun F k v)⁻¹) (Filter.eventually_cofinite.mpr
    ((k.support.finite_toSet).subset fun v hv => by
      by_contra h; exact hv (by rw [unifFun_of_notMem F k h, inv_one]; exact one_mem _)))
  val_inv := Subtype.ext (funext fun v => mul_inv_cancel₀ (zpow_ne_zero _ (unif_coe_ne_zero F v)))
  inv_val := Subtype.ext (funext fun v => inv_mul_cancel₀ (zpow_ne_zero _ (unif_coe_ne_zero F v)))

private theorem unifIdele_apply (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : ((unifIdele F k : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v = unifFun F k v := rfl

private theorem valued_unifIdele (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : Valued.v (((unifIdele F k : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v) = exp (k v : ℤ) :=
  valued_unifFun F k v

private def latt (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) : AddSubgroup (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) := dilate F (unifIdele F k)

private theorem mem_latt_iff (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) (t : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) : t ∈ latt F k ↔ ∀ v, Valued.v (t v) ≤ exp (k v : ℤ) := by
  rw [latt, mem_dilate_iff]; simp only [valued_unifIdele]

private theorem one_le_valued_unifIdele (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) (v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) : 1 ≤ Valued.v (((unifIdele F k : ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))ˣ) : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v) := by
  rw [valued_unifIdele, ← exp_zero, exp_le_exp]; exact_mod_cast Nat.zero_le _

private theorem intLattice_le_latt (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) : intLattice F ≤ latt F k := intLattice_le_dilate F (one_le_valued_unifIdele F k)

private theorem latt_mono {k k' : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ} (h : k ≤ k') : latt F k ≤ latt F k' := fun t ht =>
  (mem_latt_iff F k' t).mpr fun v => ((mem_latt_iff F k t).mp ht v).trans (exp_le_exp.mpr (by exact_mod_cast h v))

private theorem relIndex_latt_ne_zero (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) : (intLattice F).relIndex (latt F k) ≠ 0 := relIndex_dilate_ne_zero F _

private theorem isCompact_latt (k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ) : IsCompact (latt F k : Set (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) := isCompact_dilate F _
end Lattices

end AutomorphicForm.WeylIntegrable
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable"
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm"

namespace WeylUnipotentDecay

section Cover

variable (F : Type) [Field F] [NumberField F]

open AutomorphicForm.WeylIntegrable

private theorem exists_mem_latt (t : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) : ∃ k : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ, t ∈ latt F k := by
  classical
  have hfin : {v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) | ¬ Valued.v (t v) ≤ 1}.Finite := by
    refine ((show RestrictedProduct (fun v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from t).eventually).subset
      fun v hv => ?_
    intro hint
    exact hv ((mem_adicCompletionIntegers _ _ _).mp hint)
  let f : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → ℕ := fun v => (log (Valued.v (t v))).toNat
  have hsupp : f.support ⊆ {v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) | ¬ Valued.v (t v) ≤ 1} := fun v hv h1 => by
    apply hv
    show (log (Valued.v (t v))).toNat = 0
    rcases eq_or_ne (Valued.v (t v)) 0 with h0 | h0
    · rw [h0, log_zero, Int.toNat_zero]
    · exact Int.toNat_of_nonpos ((log_le_iff_le_exp h0).mpr (by rwa [exp_zero]))
  refine ⟨Finsupp.ofSupportFinite f (hfin.subset hsupp), (mem_latt_iff F _ t).mpr fun v => ?_⟩
  simp only [Finsupp.ofSupportFinite_coe]
  exact le_exp_log.trans (exp_le_exp.mpr (Int.self_le_toNat _))

private theorem countable_ideal : Countable (Ideal (𝓞 F)) := by
  have h : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
    ext I; simp
  rw [← Set.countable_univ_iff, h]
  exact Set.countable_iUnion fun n => (Ideal.finite_setOf_absNorm_eq n).countable

private theorem countable_heightOneSpectrum : Countable (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) := by
  haveI := countable_ideal F
  exact Function.Injective.countable (f := fun v : (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) => v.asIdeal) fun v w h => HeightOneSpectrum.ext h

private theorem exists_latt_seq : ∃ e : ℕ → ((IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ), Function.Surjective e := by
  haveI := countable_heightOneSpectrum F
  exact exists_surjective_nat ((IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →₀ ℕ)

end Cover
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable"

section Core

private theorem cast_eq_prod_of_forall_map_add_left
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure]
    {Y : Type*} [MeasurableSpace Y]
    {m : MeasurableSpace (G × Y)} (hm : m = Prod.instMeasurableSpace)
    (ν : @Measure (G × Y) m)
    (hinv : ∀ a : G, @Measure.map (G × Y) (G × Y) m m (fun p : G × Y => (a + p.1, p.2)) ν = ν)
    (hfin : ∃ B : ℕ → Set Y, (∀ n, MeasurableSet (B n)) ∧ (⋃ n, B n) = Set.univ ∧
      ∀ n (K : Set G), IsCompact K → ν (K ×ˢ B n) < ⊤) :
    ∃ σ : Measure Y, SigmaFinite σ ∧ (hm ▸ ν : @Measure (G × Y) Prod.instMeasurableSpace) = μ.prod σ := by
  subst hm
  exact MeasureTheory.Measure.exists_eq_prod_of_forall_map_add_left μ ν hinv hfin

end Core
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable"

section Adelic

variable (F : Type) [Field F] [NumberField F]

open AutomorphicForm.WeylIntegrable

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private def adeleOf (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (a, b)

@[scoped simp] private theorem adeleOf_fst (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : (adeleOf F a b).1 = a := rfl
@[scoped simp] private theorem adeleOf_snd (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : (adeleOf F a b).2 = b := rfl

private theorem adelicAddHaar_eq_prod
    [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    [SecondCountableTopology (InfiniteAdeleRing F)]
    (μ : Measure (InfiniteAdeleRing F)) [μ.IsAddHaarMeasure]
    (hmeq : adeleBorel (𝓞 F) F =
      (Prod.instMeasurableSpace : MeasurableSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))) :
    ∃ σ : Measure (FiniteAdeleRing (𝓞 F) F), SigmaFinite σ ∧
      (hmeq ▸ adelicAddHaar (𝓞 F) F :
        @Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) Prod.instMeasurableSpace) = μ.prod σ := by
  classical
  refine cast_eq_prod_of_forall_map_add_left μ hmeq (adelicAddHaar (𝓞 F) F) (fun a => ?_) ?_
  ·
    have hfun : (fun p : AdeleRing (𝓞 F) F => adeleOf F (a + p.1) p.2) = fun p => adeleOf F a 0 + p := by
      funext p
      exact Prod.ext rfl (zero_add p.2).symm
    show Measure.map (fun p : AdeleRing (𝓞 F) F => adeleOf F (a + p.1) p.2) (adelicAddHaar (𝓞 F) F)
        = adelicAddHaar (𝓞 F) F
    rw [hfun]
    exact map_add_left_eq_self _ _
  ·
    obtain ⟨e, he⟩ := exists_latt_seq F
    refine ⟨fun n => (latt F (e n) : Set (FiniteAdeleRing (𝓞 F) F)), fun n => ?_, ?_, fun n K hK => ?_⟩
    · exact (isCompact_latt F (e n)).isClosed.measurableSet
    · refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.mpr ?_
      obtain ⟨k, hk⟩ := exists_mem_latt F t
      obtain ⟨n, rfl⟩ := he k
      exact ⟨n, hk⟩
    ·
      have hc : @IsCompact (AdeleRing (𝓞 F) F) _ (K ×ˢ (latt F (e n) : Set (FiniteAdeleRing (𝓞 F) F))) :=
        hK.prod (isCompact_latt F (e n))
      show (adelicAddHaar (𝓞 F) F) (K ×ˢ (latt F (e n) : Set (FiniteAdeleRing (𝓞 F) F))) < ⊤
      exact hc.measure_lt_top

private theorem integral_cast_measurableSpace {X : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m₁ m₂ : MeasurableSpace X} (h : m₁ = m₂) (ν : @Measure X m₁) (f : X → E) :
    ∫ x, f x ∂(h ▸ ν : @Measure X m₂) = ∫ x, f x ∂ν := by
  subst h
  rfl

private theorem integrable_cast_measurableSpace_iff {X : Type*} {E : Type*} [NormedAddCommGroup E]
    {m₁ m₂ : MeasurableSpace X} (h : m₁ = m₂) (ν : @Measure X m₁) (f : X → E) :
    Integrable f (h ▸ ν : @Measure X m₂) ↔ Integrable f ν := by
  subst h
  exact Iff.rfl

end Adelic
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable"

section SigmaProps

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem cast_measure_apply {X : Type*} {m₁ m₂ : MeasurableSpace X} (h : m₁ = m₂) (ν : @Measure X m₁)
    (s : Set X) : (h ▸ ν : @Measure X m₂) s = ν s := by
  subst h
  rfl

variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]

omit [BorelSpace (InfiniteAdeleRing F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

private theorem measure_mul_sigma_eq (μ : Measure (InfiniteAdeleRing F)) (σ : Measure (FiniteAdeleRing (𝓞 F) F))
    [SFinite σ]
    (hmeq : adeleBorel (𝓞 F) F =
      (Prod.instMeasurableSpace : MeasurableSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)))
    (hρ : (hmeq ▸ adelicAddHaar (𝓞 F) F :
        @Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) Prod.instMeasurableSpace) = μ.prod σ)
    (K : Set (InfiniteAdeleRing F)) (B : Set (FiniteAdeleRing (𝓞 F) F)) :
    μ K * σ B = adelicAddHaar (𝓞 F) F (K ×ˢ B) :=
  calc μ K * σ B = μ.prod σ (K ×ˢ B) := (Measure.prod_prod K B).symm
    _ = (hmeq ▸ adelicAddHaar (𝓞 F) F :
          @Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) Prod.instMeasurableSpace) (K ×ˢ B) :=
        (congrArg (fun ν : @Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) Prod.instMeasurableSpace =>
          ν (K ×ˢ B)) hρ).symm
    _ = adelicAddHaar (𝓞 F) F (K ×ˢ B) := cast_measure_apply hmeq _ _

omit [BorelSpace (InfiniteAdeleRing F)] in
private theorem sigma_isAddLeftInvariant (μ : Measure (InfiniteAdeleRing F)) [μ.IsAddHaarMeasure]
    (σ : Measure (FiniteAdeleRing (𝓞 F) F)) [SFinite σ]
    (hmeq : adeleBorel (𝓞 F) F =
      (Prod.instMeasurableSpace : MeasurableSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)))
    (hρ : (hmeq ▸ adelicAddHaar (𝓞 F) F :
        @Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) Prod.instMeasurableSpace) = μ.prod σ) :
    σ.IsAddLeftInvariant := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : InfiniteAdeleRing F)
  have hKpos : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have hKtop : μ K ≠ ⊤ := hK.measure_lt_top.ne
  refine (forall_measure_preimage_add_iff σ).mp fun c A _hA => ?_
  refine (ENNReal.mul_right_inj hKpos hKtop).mp ?_
  rw [measure_mul_sigma_eq F μ σ hmeq hρ, measure_mul_sigma_eq F μ σ hmeq hρ]
  have hset : (K ×ˢ ((fun h => c + h) ⁻¹' A) : Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
      = (fun x : AdeleRing (𝓞 F) F => adeleOf F 0 c + x) ⁻¹'
          (K ×ˢ A : Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨show (0 : InfiniteAdeleRing F) + x.1 ∈ K by rwa [zero_add], h2⟩
    · rintro ⟨h1, h2⟩
      have h1' : (0 : InfiniteAdeleRing F) + x.1 ∈ K := h1
      rw [zero_add] at h1'
      exact ⟨h1', h2⟩
  rw [hset]
  exact measure_preimage_add _ _ _

omit [BorelSpace (InfiniteAdeleRing F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
private theorem sigma_isFiniteMeasureOnCompacts (μ : Measure (InfiniteAdeleRing F)) [μ.IsAddHaarMeasure]
    (σ : Measure (FiniteAdeleRing (𝓞 F) F)) [SFinite σ]
    (hmeq : adeleBorel (𝓞 F) F =
      (Prod.instMeasurableSpace : MeasurableSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)))
    (hρ : (hmeq ▸ adelicAddHaar (𝓞 F) F :
        @Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) Prod.instMeasurableSpace) = μ.prod σ) :
    IsFiniteMeasureOnCompacts σ := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : InfiniteAdeleRing F)
  have hKpos : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  refine ⟨?_⟩
  intro C hC
  have h := measure_mul_sigma_eq F μ σ hmeq hρ K C
  have hc : @IsCompact (AdeleRing (𝓞 F) F) _ (K ×ˢ C) := hK.prod hC
  have hlt : adelicAddHaar (𝓞 F) F (K ×ˢ C) < ⊤ := hc.measure_lt_top
  exact ENNReal.lt_top_of_mul_ne_top_right (h.trans_lt hlt).ne hKpos

omit [BorelSpace (InfiniteAdeleRing F)] in
private theorem sigma_isAddHaarMeasure (μ : Measure (InfiniteAdeleRing F)) [μ.IsAddHaarMeasure]
    (σ : Measure (FiniteAdeleRing (𝓞 F) F)) [SFinite σ]
    (hmeq : adeleBorel (𝓞 F) F =
      (Prod.instMeasurableSpace : MeasurableSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)))
    (hρ : (hmeq ▸ adelicAddHaar (𝓞 F) F :
        @Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) Prod.instMeasurableSpace) = μ.prod σ) :
    σ.IsAddHaarMeasure := by
  haveI := sigma_isAddLeftInvariant F μ σ hmeq hρ
  haveI := sigma_isFiniteMeasureOnCompacts F μ σ hmeq hρ
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : InfiniteAdeleRing F)
  have hZc : IsCompact (integralFiniteAdeles (𝓞 F) F) := isCompact_integralFiniteAdeles F
  have hZo : IsOpen (integralFiniteAdeles (𝓞 F) F) := isOpen_integralFiniteAdeles F
  have hZ0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
    (AutomorphicForm.WeylIntegrable.intLattice F).zero_mem
  have hZne : (interior (integralFiniteAdeles (𝓞 F) F)).Nonempty := ⟨0, by rw [hZo.interior_eq]; exact hZ0⟩
  refine Measure.isAddHaarMeasure_of_isCompact_nonempty_interior σ _ hZc hZne (fun h0 => ?_)
    hZc.measure_lt_top.ne
  have h := measure_mul_sigma_eq F μ σ hmeq hρ (interior K) (integralFiniteAdeles (𝓞 F) F)
  rw [h0, mul_zero] at h
  have hopen : @IsOpen (AdeleRing (𝓞 F) F) _ (interior K ×ˢ integralFiniteAdeles (𝓞 F) F) :=
    isOpen_interior.prod hZo
  have hne : (interior K ×ˢ integralFiniteAdeles (𝓞 F) F :
      Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)).Nonempty :=
    ⟨(0, 0), mem_interior_iff_mem_nhds.mpr hK0, hZ0⟩
  exact (hopen.measure_pos (adelicAddHaar (𝓞 F) F) hne).ne' h.symm

end SigmaProps
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay"

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace IsDedekindDomain

namespace InfiniteAdeleHaar

variable (F : Type) [Field F] [NumberField F]

@[reducible] private def placeBorel (w : InfinitePlace F) : MeasurableSpace (w.Completion) := borel _

attribute [local instance] placeBorel

private scoped instance placeBorelSpace (w : InfinitePlace F) : BorelSpace (w.Completion) := ⟨rfl⟩

variable {F}

private def placeMeasureReal {w : InfinitePlace F} (hw : w.IsReal) : Measure (w.Completion) :=
  (volume : Measure ℝ).map (Completion.ringEquivRealOfIsReal hw).symm

private def placeMeasureComplex {w : InfinitePlace F} (hw : w.IsComplex) : Measure (w.Completion) :=
  (volume : Measure ℂ).map (Completion.ringEquivComplexOfIsComplex hw).symm

variable (F) in
open Classical in

private def placeMeasure (w : InfinitePlace F) : Measure (w.Completion) :=
  if hw : w.IsReal then placeMeasureReal hw
  else placeMeasureComplex (not_isReal_iff_isComplex.mp hw)

private scoped instance isAddHaarMeasure_placeMeasureReal {w : InfinitePlace F} (hw : w.IsReal) :
    (placeMeasureReal hw).IsAddHaarMeasure := by
  unfold placeMeasureReal
  exact AddEquiv.isAddHaarMeasure_map _
    ((Completion.ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toAddEquiv
    (Completion.isometryEquivRealOfIsReal hw).symm.continuous
    (Completion.isometryEquivRealOfIsReal hw).continuous

private scoped instance isAddHaarMeasure_placeMeasureComplex {w : InfinitePlace F} (hw : w.IsComplex) :
    (placeMeasureComplex hw).IsAddHaarMeasure := by
  unfold placeMeasureComplex
  exact AddEquiv.isAddHaarMeasure_map _
    ((Completion.ringEquivComplexOfIsComplex hw).symm : ℂ ≃+* w.Completion).toAddEquiv
    (Completion.isometryEquivComplexOfIsComplex hw).symm.continuous
    (Completion.isometryEquivComplexOfIsComplex hw).continuous

private scoped instance secondCountable_completion (w : InfinitePlace F) :
    SecondCountableTopology (w.Completion) := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact (Completion.isometryEquivRealOfIsReal hw).toHomeomorph.isEmbedding.secondCountableTopology
  · exact (Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isEmbedding.secondCountableTopology

private scoped instance isAddHaarMeasure_placeMeasure (w : InfinitePlace F) :
    (placeMeasure F w).IsAddHaarMeasure := by
  unfold placeMeasure
  split
  · exact isAddHaarMeasure_placeMeasureReal _
  · exact isAddHaarMeasure_placeMeasureComplex _

private scoped instance sigmaCompact_completion (w : InfinitePlace F) : SigmaCompactSpace (w.Completion) :=
  inferInstance

private scoped instance sigmaFinite_placeMeasure (w : InfinitePlace F) : SigmaFinite (placeMeasure F w) :=
  inferInstance

variable (F) in

private def archMeasure : Measure ((w : InfinitePlace F) → w.Completion) :=
  Measure.pi (fun w => placeMeasure F w)

private scoped instance isFiniteMeasureOnCompacts_archMeasure : IsFiniteMeasureOnCompacts (archMeasure F) := by
  unfold archMeasure; infer_instance

private scoped instance isOpenPosMeasure_archMeasure : (archMeasure F).IsOpenPosMeasure := by
  unfold archMeasure; infer_instance

private scoped instance sigmaFinite_archMeasure : SigmaFinite (archMeasure F) := by
  unfold archMeasure; infer_instance

private scoped instance isAddLeftInvariant_archMeasure : (archMeasure F).IsAddLeftInvariant := by
  constructor
  intro a
  have hmeas : Measurable (fun x : (w : InfinitePlace F) → w.Completion => a + x) :=
    measurable_const.add measurable_id
  refine Eq.symm (Measure.pi_eq fun B hB => ?_)
  have hpre : (fun x : (w : InfinitePlace F) → w.Completion => a + x) ⁻¹' Set.pi Set.univ B
      = Set.pi Set.univ (fun w => (fun t => a w + t) ⁻¹' B w) := by
    ext x
    simp [Set.mem_pi, Pi.add_apply]
  unfold archMeasure
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hB), hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  exact measure_preimage_add (placeMeasure F w) (a w) (B w)

private scoped instance isAddHaarMeasure_archMeasure : (archMeasure F).IsAddHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := inferInstance
    toIsAddLeftInvariant := inferInstance
    toIsOpenPosMeasure := inferInstance }

end InfiniteAdeleHaar
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"
end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm"
open scoped NNReal

namespace WeylUnipotentIntegrable

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private def haarModulus : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

private theorem adelicWeyl_inv : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]

private theorem integrable_weyl_unipotent_mul (hα : ∀ x, 0 < ((haarModulus F x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (s : ℂ) (hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ (haarModulus F) hα s) (etaSnd ν (haarModulus F) hα s) φ)
    (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun y : AdeleRing (𝓞 F) F => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g))
      (adelicAddHaar (𝓞 F) F) := by
  have h := AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν
    hμ hν s hs φ hφ hφc g
  simpa only [adelicWeyl_inv] using h

end WeylUnipotentIntegrable
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section PlaceCommute
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm NumberField"
variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in

private theorem WeylUnipotentDecay.commute_archGLIncl_of_ne {v w : InfinitePlace F} (hvw : v ≠ w)
    (x : GL (Fin 2) v.Completion) (y : GL (Fin 2) w.Completion) :
    Commute (archGLIncl F v x) (archGLIncl F w y) := by
  classical
  refine Units.ext ?_
  show archMatrixInclHom F v (x : Matrix (Fin 2) (Fin 2) v.Completion)
      * archMatrixInclHom F w (y : Matrix (Fin 2) (Fin 2) w.Completion)
    = archMatrixInclHom F w (y : Matrix (Fin 2) (Fin 2) w.Completion)
      * archMatrixInclHom F v (x : Matrix (Fin 2) (Fin 2) v.Completion)
  apply (archMatrixPiEquiv F).injective
  simp only [map_mul, archMatrixInclHom, MonoidHom.coe_mk, OneHom.coe_mk,
    archMatrixPiEquiv_archMatrixUpdate]
  funext u
  rcases eq_or_ne u v with rfl | huv
  · simp [Function.update_of_ne hvw]
  · rcases eq_or_ne u w with rfl | huw
    · simp [Function.update_of_ne huv]
    · simp [Function.update_of_ne huv, Function.update_of_ne huw]

private theorem WeylUnipotentDecay.commute_archRowIsometrySubgroup_of_ne {v w : InfinitePlace F} (hvw : v ≠ w)
    {x : AdelicGL2 (𝓞 F) F} (hx : x ∈ archRowIsometrySubgroup F v)
    {y : AdelicGL2 (𝓞 F) F} (hy : y ∈ archRowIsometrySubgroup F w) :
    Commute x y := by
  rcases hx with ⟨x₀, _hx₀, rfl⟩
  rcases hy with ⟨y₀, _hy₀, rfl⟩
  show adelicArchGLInclAt F v x₀ * adelicArchGLInclAt F w y₀
      = adelicArchGLInclAt F w y₀ * adelicArchGLInclAt F v x₀
  rw [adelicArchGLInclAt, adelicArchGLInclAt, MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← map_mul, ← map_mul, WeylUnipotentDecay.commute_archGLIncl_of_ne F hvw x₀ y₀]

end PlaceCommute
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm IsDedekindDomain"
open scoped NNReal

noncomputable section

namespace WeylUnipotentDecay

open AutomorphicForm.WindowedSiegel Matrix
open ComplexConjugate

private theorem mem_unitaryGroup_of_isRowIsometry {k : GL (Fin 2) ℂ} (hk : IsRowIsometry k) :
    (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  obtain ⟨-, h⟩ := hk
  have H1 := h 1 0
  have H2 := h 0 1
  have H3 := h 1 1
  have H4 := h 1 Complex.I
  simp only [one_mul, zero_mul, add_zero, zero_add, norm_one, norm_zero, Complex.norm_I, one_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_sub, add_zero, zero_add] at H1 H2 H3 H4
  rw [Matrix.mem_unitaryGroup_iff, ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), RCLike.star_def, Complex.ext_iff, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
    Complex.zero_re, Complex.zero_im, mul_neg, sub_neg_eq_add]
  repeat' constructor
  all_goals linarith [H1, H2, H3, H4]

private theorem mem_orthogonalGroup_of_isRowIsometry {k : GL (Fin 2) ℝ} (hk : IsRowIsometry k) :
    (k : Matrix (Fin 2) (Fin 2) ℝ) ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  obtain ⟨-, h⟩ := hk
  have H1 := h 1 0
  have H2 := h 0 1
  have H3 := h 1 1
  simp only [one_mul, zero_mul, add_zero, zero_add, norm_one, norm_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Real.norm_eq_abs, sq_abs] at H1 H2 H3
  rw [Matrix.mem_unitaryGroup_iff, ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, star_trivial,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  repeat' constructor
  all_goals linarith [H1, H2, H3]

private theorem isRowIsometry_of_mem_unitaryGroup {k : GL (Fin 2) ℂ}
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) : IsRowIsometry k := by
  refine ⟨CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hk), fun x y => ?_⟩
  have h := Matrix.mem_unitaryGroup_iff.mp hk
  have e : ∀ i j, ((k : Matrix (Fin 2) (Fin 2) ℂ) * star (k : Matrix (Fin 2) (Fin 2) ℂ)) i j
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j => by rw [h]
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Fin.isValue,
    Complex.star_def] at h00 h01 h10 h11
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, ← Complex.ofReal_inj]
  push_cast
  simp only [← Complex.mul_conj, map_add, map_mul]
  linear_combination (x * conj x) * h00 + (y * conj y) * h11 + (x * conj y) * h01 + (y * conj x) * h10

private theorem isRowIsometry_of_mem_orthogonalGroup {k : GL (Fin 2) ℝ}
    (hk : (k : Matrix (Fin 2) (Fin 2) ℝ) ∈ Matrix.orthogonalGroup (Fin 2) ℝ) : IsRowIsometry k := by
  refine ⟨CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hk), fun x y => ?_⟩
  have h := Matrix.mem_unitaryGroup_iff.mp hk
  have e : ∀ i j, ((k : Matrix (Fin 2) (Fin 2) ℝ) * star (k : Matrix (Fin 2) (Fin 2) ℝ)) i j
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := fun i j => by rw [h]
  have h00 := e 0 0
  have h01 := e 0 1
  have h11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, star_trivial, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Fin.isValue] at h00 h01 h11
  simp only [Real.norm_eq_abs, sq_abs]
  linear_combination (x ^ 2) * h00 + (y ^ 2) * h11 + (2 * x * y) * h01

section Transport

variable {K L : Type*} [NormedField K] [NormedField L]

private def _root_.WeylUnipotentDecay.glMapRingEquiv (e : K ≃+* L) : GL (Fin 2) K →* GL (Fin 2) L :=
  Units.map (e.toRingHom.mapMatrix : Matrix (Fin 2) (Fin 2) K →+* Matrix (Fin 2) (Fin 2) L).toMonoidHom

p2m_export "WeylUnipotentDecay" "glMapRingEquiv"
private theorem glMapRingEquiv_coe_apply (e : K ≃+* L) (k : GL (Fin 2) K) (i j : Fin 2) :
    ((glMapRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = e ((k : Matrix (Fin 2) (Fin 2) K) i j) := rfl

private theorem glMapRingEquiv_symm_apply (e : K ≃+* L) (k : GL (Fin 2) K) :
    glMapRingEquiv e.symm (glMapRingEquiv e k) = k :=
  Units.ext (Matrix.ext fun _ _ => e.symm_apply_apply _)

private theorem glMapRingEquiv_apply_symm (e : K ≃+* L) (k : GL (Fin 2) L) :
    glMapRingEquiv e (glMapRingEquiv e.symm k) = k :=
  Units.ext (Matrix.ext fun _ _ => e.apply_symm_apply _)

namespace IsRowIsometry

private theorem _root_.WeylUnipotentDecay.IsRowIsometry.glMapRingEquiv (e : K ≃+* L) (he : ∀ x, ‖e x‖ = ‖x‖) {k : GL (Fin 2) K}
    (hk : IsRowIsometry k) : IsRowIsometry (glMapRingEquiv e k) := by
  obtain ⟨hdet, h⟩ := hk
  refine ⟨?_, fun x y => ?_⟩
  · show ‖(e.toRingHom.mapMatrix (k : Matrix (Fin 2) (Fin 2) K)).det‖ = 1
    rw [← RingHom.map_det]
    exact (he _).trans hdet
  · obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    have hxy := h x y
    show ‖e x * e ((k : Matrix (Fin 2) (Fin 2) K) 0 0) + e y * e ((k : Matrix (Fin 2) (Fin 2) K) 1 0)‖ ^ 2
        + ‖e x * e ((k : Matrix (Fin 2) (Fin 2) K) 0 1) + e y * e ((k : Matrix (Fin 2) (Fin 2) K) 1 1)‖ ^ 2
      = ‖e x‖ ^ 2 + ‖e y‖ ^ 2
    rw [← map_mul, ← map_mul, ← map_add, ← map_mul, ← map_mul, ← map_add, he, he, he, he]
    exact hxy

end IsRowIsometry
p2m_export "WeylUnipotentDecay" "IsRowIsometry.glMapRingEquiv"
end Transport
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section Place

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F]

private theorem norm_ringEquivComplexOfIsComplex {w : InfinitePlace F} (hw : w.IsComplex) (x : w.Completion) :
    ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (AddMonoidHomClass.isometry_iff_norm (extensionEmbedding w)).mp (isometry_extensionEmbedding w) x

private theorem norm_ringEquivComplexOfIsComplex_symm {w : InfinitePlace F} (hw : w.IsComplex) (z : ℂ) :
    ‖(ringEquivComplexOfIsComplex hw).symm z‖ = ‖z‖ := by
  conv_rhs => rw [← (ringEquivComplexOfIsComplex hw).apply_symm_apply z]
  exact (norm_ringEquivComplexOfIsComplex hw _).symm

private theorem norm_ringEquivRealOfIsReal {v : InfinitePlace F} (hv : v.IsReal) (x : v.Completion) :
    ‖ringEquivRealOfIsReal hv x‖ = ‖x‖ :=
  (AddMonoidHomClass.isometry_iff_norm (extensionEmbeddingOfIsReal hv)).mp (isometry_extensionEmbeddingOfIsReal hv) x

private theorem norm_ringEquivRealOfIsReal_symm {v : InfinitePlace F} (hv : v.IsReal) (r : ℝ) :
    ‖(ringEquivRealOfIsReal hv).symm r‖ = ‖r‖ := by
  conv_rhs => rw [← (ringEquivRealOfIsReal hv).apply_symm_apply r]
  exact (norm_ringEquivRealOfIsReal hv _).symm

private def unitaryToGL (u : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : GL (Fin 2) ℂ :=
  ⟨u, star (u : Matrix (Fin 2) (Fin 2) ℂ), Matrix.mem_unitaryGroup_iff.mp u.2, Matrix.mem_unitaryGroup_iff'.mp u.2⟩

private def orthogonalToGL (u : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : GL (Fin 2) ℝ :=
  ⟨u, star (u : Matrix (Fin 2) (Fin 2) ℝ), Matrix.mem_unitaryGroup_iff.mp u.2, Matrix.mem_unitaryGroup_iff'.mp u.2⟩

private def rowIsometryEquivUnitary {w : InfinitePlace F} (hw : w.IsComplex) :
    ↥(rowIsometrySubgroup w.Completion) ≃* ↥(Matrix.unitaryGroup (Fin 2) ℂ) where
  toFun k := ⟨(glMapRingEquiv (ringEquivComplexOfIsComplex hw) k.1 : Matrix (Fin 2) (Fin 2) ℂ),
    mem_unitaryGroup_of_isRowIsometry
      (IsRowIsometry.glMapRingEquiv _ (norm_ringEquivComplexOfIsComplex hw) (k.2 : IsRowIsometry k.1))⟩
  invFun u := ⟨glMapRingEquiv (ringEquivComplexOfIsComplex hw).symm (unitaryToGL u),
    IsRowIsometry.glMapRingEquiv _ (norm_ringEquivComplexOfIsComplex_symm hw)
      (isRowIsometry_of_mem_unitaryGroup (k := unitaryToGL u) u.2)⟩
  left_inv k := Subtype.ext (Units.ext (Matrix.ext fun i j =>
    show (ringEquivComplexOfIsComplex hw).symm (ringEquivComplexOfIsComplex hw
        (((k.1 : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j)) = _ from
      (ringEquivComplexOfIsComplex hw).symm_apply_apply _))
  right_inv u := Subtype.ext (by
    show ((glMapRingEquiv (ringEquivComplexOfIsComplex hw)
        (glMapRingEquiv (ringEquivComplexOfIsComplex hw).symm (unitaryToGL u)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = u
    rw [glMapRingEquiv_apply_symm]
    rfl)
  map_mul' a b := Subtype.ext (congrArg Units.val (map_mul (glMapRingEquiv (ringEquivComplexOfIsComplex hw)) a.1 b.1))

private theorem coe_rowIsometryEquivUnitary {w : InfinitePlace F} (hw : w.IsComplex) (k : ↥(rowIsometrySubgroup w.Completion))
    (i j : Fin 2) :
    ((rowIsometryEquivUnitary hw k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) i j
      = ringEquivComplexOfIsComplex hw (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) := rfl

private theorem coe_rowIsometryEquivUnitary_symm {w : InfinitePlace F} (hw : w.IsComplex) (u : ↥(Matrix.unitaryGroup (Fin 2) ℂ))
    (i j : Fin 2) :
    ((((rowIsometryEquivUnitary hw).symm u : ↥(rowIsometrySubgroup w.Completion)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j
      = (ringEquivComplexOfIsComplex hw).symm ((u : Matrix (Fin 2) (Fin 2) ℂ) i j) := rfl

private theorem continuous_rowIsometryEquivUnitary {w : InfinitePlace F} (hw : w.IsComplex) :
    Continuous (rowIsometryEquivUnitary hw) := by
  refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
  show Continuous fun k : ↥(rowIsometrySubgroup w.Completion) =>
    ringEquivComplexOfIsComplex hw (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j)
  have hval : Continuous fun k : ↥(rowIsometrySubgroup w.Completion) =>
      ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_val.comp continuous_subtype_val
  exact (isometry_extensionEmbedding w).continuous.comp (hval.matrix_elem i j)

private theorem continuous_rowIsometryEquivUnitary_symm {w : InfinitePlace F} (hw : w.IsComplex) :
    Continuous (rowIsometryEquivUnitary hw).symm := by
  have hsymm : Continuous (ringEquivComplexOfIsComplex hw).symm := (isometryEquivComplexOfIsComplex hw).symm.continuous
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩) _
  · show Continuous fun u : ↥(Matrix.unitaryGroup (Fin 2) ℂ) =>
      (ringEquivComplexOfIsComplex hw).symm ((u : Matrix (Fin 2) (Fin 2) ℂ) i j)
    exact hsymm.comp (continuous_subtype_val.matrix_elem i j)
  · show Continuous fun u : ↥(Matrix.unitaryGroup (Fin 2) ℂ) =>
      (ringEquivComplexOfIsComplex hw).symm (star ((u : Matrix (Fin 2) (Fin 2) ℂ) j i))
    exact hsymm.comp ((continuous_subtype_val.matrix_elem j i).star)

private def rowIsometryEquivOrthogonal {v : InfinitePlace F} (hv : v.IsReal) :
    ↥(rowIsometrySubgroup v.Completion) ≃* ↥(Matrix.orthogonalGroup (Fin 2) ℝ) where
  toFun k := ⟨(glMapRingEquiv (ringEquivRealOfIsReal hv) k.1 : Matrix (Fin 2) (Fin 2) ℝ),
    mem_orthogonalGroup_of_isRowIsometry
      (IsRowIsometry.glMapRingEquiv _ (norm_ringEquivRealOfIsReal hv) (k.2 : IsRowIsometry k.1))⟩
  invFun u := ⟨glMapRingEquiv (ringEquivRealOfIsReal hv).symm (orthogonalToGL u),
    IsRowIsometry.glMapRingEquiv _ (norm_ringEquivRealOfIsReal_symm hv)
      (isRowIsometry_of_mem_orthogonalGroup (k := orthogonalToGL u) u.2)⟩
  left_inv k := Subtype.ext (Units.ext (Matrix.ext fun i j =>
    show (ringEquivRealOfIsReal hv).symm (ringEquivRealOfIsReal hv
        (((k.1 : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j)) = _ from
      (ringEquivRealOfIsReal hv).symm_apply_apply _))
  right_inv u := Subtype.ext (by
    show ((glMapRingEquiv (ringEquivRealOfIsReal hv)
        (glMapRingEquiv (ringEquivRealOfIsReal hv).symm (orthogonalToGL u)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = u
    rw [glMapRingEquiv_apply_symm]
    rfl)
  map_mul' a b := Subtype.ext (congrArg Units.val (map_mul (glMapRingEquiv (ringEquivRealOfIsReal hv)) a.1 b.1))

private theorem coe_rowIsometryEquivOrthogonal {v : InfinitePlace F} (hv : v.IsReal) (k : ↥(rowIsometrySubgroup v.Completion))
    (i j : Fin 2) :
    ((rowIsometryEquivOrthogonal hv k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = ringEquivRealOfIsReal hv (((k : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j) := rfl

private theorem coe_rowIsometryEquivOrthogonal_symm {v : InfinitePlace F} (hv : v.IsReal) (u : ↥(Matrix.orthogonalGroup (Fin 2) ℝ))
    (i j : Fin 2) :
    ((((rowIsometryEquivOrthogonal hv).symm u : ↥(rowIsometrySubgroup v.Completion)) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion) i j
      = (ringEquivRealOfIsReal hv).symm ((u : Matrix (Fin 2) (Fin 2) ℝ) i j) := rfl

private theorem continuous_rowIsometryEquivOrthogonal {v : InfinitePlace F} (hv : v.IsReal) :
    Continuous (rowIsometryEquivOrthogonal hv) := by
  refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
  show Continuous fun k : ↥(rowIsometrySubgroup v.Completion) =>
    ringEquivRealOfIsReal hv (((k : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j)
  have hval : Continuous fun k : ↥(rowIsometrySubgroup v.Completion) =>
      ((k : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) :=
    Units.continuous_val.comp continuous_subtype_val
  exact (isometry_extensionEmbeddingOfIsReal hv).continuous.comp (hval.matrix_elem i j)

private theorem continuous_rowIsometryEquivOrthogonal_symm {v : InfinitePlace F} (hv : v.IsReal) :
    Continuous (rowIsometryEquivOrthogonal hv).symm := by
  have hsymm : Continuous (ringEquivRealOfIsReal hv).symm := (isometryEquivRealOfIsReal hv).symm.continuous
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩) _
  · show Continuous fun u : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) =>
      (ringEquivRealOfIsReal hv).symm ((u : Matrix (Fin 2) (Fin 2) ℝ) i j)
    exact hsymm.comp (continuous_subtype_val.matrix_elem i j)
  · show Continuous fun u : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) =>
      (ringEquivRealOfIsReal hv).symm (star ((u : Matrix (Fin 2) (Fin 2) ℝ) j i))
    exact hsymm.comp ((continuous_subtype_val.matrix_elem j i).star)

end Place
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

open scoped ContDiff

noncomputable section

namespace WeylUnipotentDecay

section SmoothBdd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private def SmoothBdd (P : E → V) : Prop :=
  ContDiff ℝ ∞ P ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv ℝ n P x‖ ≤ C

private theorem SmoothBdd.contDiff {P : E → V} (hP : SmoothBdd P) : ContDiff ℝ ∞ P := hP.1

private theorem SmoothBdd.contDiffAt {P : E → V} (hP : SmoothBdd P) (n : ℕ) (x : E) : ContDiffAt ℝ n P x :=
  hP.1.contDiffAt.of_le (mod_cast le_top)

private theorem SmoothBdd.bound_pos {P : E → V} (hP : SmoothBdd P) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n P x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hP.2 n
  exact ⟨max C 1, lt_max_of_lt_right one_pos, fun x => (hC x).trans (le_max_left _ _)⟩

private theorem SmoothBdd.const (c : V) : SmoothBdd (fun _ : E => c) := by
  refine ⟨contDiff_const, fun n => ⟨‖c‖, fun x => ?_⟩⟩
  rcases eq_or_ne n 0 with rfl | hn
  · rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hn]
    simp

private theorem SmoothBdd.add {P Q : E → V} (hP : SmoothBdd P) (hQ : SmoothBdd Q) : SmoothBdd (fun x => P x + Q x) := by
  refine ⟨hP.1.add hQ.1, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hP.2 n
  obtain ⟨D, hD⟩ := hQ.2 n
  refine ⟨C + D, fun x => ?_⟩
  have h := iteratedFDeriv_add_apply (hP.contDiffAt n x) (hQ.contDiffAt n x)
  calc ‖iteratedFDeriv ℝ n (fun x => P x + Q x) x‖ = ‖iteratedFDeriv ℝ n (P + Q) x‖ := rfl
    _ = ‖iteratedFDeriv ℝ n P x + iteratedFDeriv ℝ n Q x‖ := by rw [h]
    _ ≤ C + D := (norm_add_le _ _).trans (add_le_add (hC x) (hD x))

private theorem SmoothBdd.clm_comp {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W) {P : E → V}
    (hP : SmoothBdd P) : SmoothBdd (fun x => L (P x)) := by
  refine ⟨L.contDiff.comp hP.1, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hP.2 n
  refine ⟨‖L‖ * C, fun x => ?_⟩
  have h := L.norm_iteratedFDeriv_comp_left (f := P) (x := x) (n := n) (hP.1.contDiffAt) (mod_cast le_top)
  exact h.trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))

private theorem SmoothBdd.mul {P Q : E → ℂ} (hP : SmoothBdd P) (hQ : SmoothBdd Q) : SmoothBdd (fun x => P x * Q x) := by
  refine ⟨hP.1.mul hQ.1, fun n => ?_⟩
  choose C hC using hP.2
  choose D hD using hQ.2
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i * D (n - i), fun x => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hP.1 hQ.1 x (n := n) (mod_cast le_top)).trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 := hC i x
  have h2 := hD (n - i) x
  have hC0 : 0 ≤ C i := (norm_nonneg _).trans h1
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hC0)

private theorem SmoothBdd.const_mul (c : ℂ) {P : E → ℂ} (hP : SmoothBdd P) : SmoothBdd (fun x => c * P x) :=
  (SmoothBdd.const c).mul hP

private theorem SmoothBdd.smul (c : ℂ) {P : E → ℂ} (hP : SmoothBdd P) : SmoothBdd (c • P) :=
  (SmoothBdd.const c).mul hP

end SmoothBdd
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]

private def singleCLM (i j : Fin 2) : R →L[ℝ] Matrix (Fin 2) (Fin 2) R :=
  ⟨Matrix.singleLinearMap ℝ i j, by
    refine continuous_matrix fun i' j' => ?_
    show Continuous fun c : R => (Matrix.single i j c : Matrix (Fin 2) (Fin 2) R) i' j'
    by_cases h : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := h
      simp only [Matrix.single_apply_same]
      exact continuous_id
    · simp only [Matrix.single_apply_of_ne _ _ _ _ _ h]
      exact continuous_const⟩

private theorem singleCLM_apply (i j : Fin 2) (c : R) : singleCLM i j c = Matrix.single i j c := rfl

private theorem clm_apply_eq_sum (φ : Matrix (Fin 2) (Fin 2) R →L[ℝ] ℂ) (m : Matrix (Fin 2) (Fin 2) R) :
    φ m = ∑ i, ∑ j, (φ.comp (singleCLM i j)) (m i j) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single m]
  simp only [map_sum, ContinuousLinearMap.comp_apply, singleCLM_apply]

private theorem SmoothBdd.clm_matrix (φ : Matrix (Fin 2) (Fin 2) R →L[ℝ] ℂ) {k : E → Matrix (Fin 2) (Fin 2) R}
    (hk : ∀ i j, SmoothBdd (fun x => k x i j)) : SmoothBdd (fun x => φ (k x)) := by
  have h : (fun x => φ (k x)) = fun x => ((φ.comp (singleCLM 0 0)) (k x 0 0) + (φ.comp (singleCLM 0 1)) (k x 0 1))
      + ((φ.comp (singleCLM 1 0)) (k x 1 0) + (φ.comp (singleCLM 1 1)) (k x 1 1)) := by
    funext x
    rw [clm_apply_eq_sum φ (k x)]
    simp only [Fin.sum_univ_two]
  rw [h]
  exact (((hk 0 0).clm_comp _).add ((hk 0 1).clm_comp _)).add (((hk 1 0).clm_comp _).add ((hk 1 1).clm_comp _))

private theorem SmoothBdd.listProd_clm_matrix (l : List (Matrix (Fin 2) (Fin 2) R →L[ℝ] ℂ))
    {k : E → Matrix (Fin 2) (Fin 2) R} (hk : ∀ i j, SmoothBdd (fun x => k x i j)) :
    SmoothBdd (fun x => (l.map (fun φ => φ (k x))).prod) := by
  induction l with
  | nil => simpa using SmoothBdd.const (E := E) (1 : ℂ)
  | cons φ l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (SmoothBdd.clm_matrix φ hk).mul ih

private theorem SmoothBdd.comp_of_mem_span_listProd {k : E → Matrix (Fin 2) (Fin 2) R} (hk : ∀ i j, SmoothBdd (fun x => k x i j))
    {F : Matrix (Fin 2) (Fin 2) R → ℂ}
    (hF : F ∈ Submodule.span ℂ
      {F : Matrix (Fin 2) (Fin 2) R → ℂ |
        ∃ l : List (Matrix (Fin 2) (Fin 2) R →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod}) :
    SmoothBdd (fun x => F (k x)) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨l, rfl⟩ := hF
      exact SmoothBdd.listProd_clm_matrix l hk
  | zero => simpa using SmoothBdd.const (E := E) (0 : ℂ)
  | add F F' _ _ hF hF' => simpa only [Pi.add_apply] using hF.add hF'
  | smul c F _ hF => simpa only [Pi.smul_apply, smul_eq_mul] using hF.const_mul c

private theorem contDiff_and_bound_comp_of_mem_span_listProd {k : E → Matrix (Fin 2) (Fin 2) R}
    (hkC : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun x => k x i j))
    (hkB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (x : E), ‖iteratedFDeriv ℝ n (fun x => k x i j) x‖ ≤ C)
    {F : Matrix (Fin 2) (Fin 2) R → ℂ}
    (hF : F ∈ Submodule.span ℂ
      {F : Matrix (Fin 2) (Fin 2) R → ℂ |
        ∃ l : List (Matrix (Fin 2) (Fin 2) R →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod}) :
    ContDiff ℝ ∞ (fun x => F (k x)) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (fun x => F (k x)) x‖ ≤ C := by
  have hk : ∀ i j, SmoothBdd (fun x => k x i j) := fun i j =>
    ⟨hkC i j, fun n => let ⟨C, _, hC⟩ := hkB n; ⟨C, fun x => hC i j x⟩⟩
  have h := SmoothBdd.comp_of_mem_span_listProd hk hF
  exact ⟨h.1, h.bound_pos⟩

end Matrix
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section
namespace WeylUnipotentDecay
private noncomputable def realIwasawaK (g : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ •
    (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0); g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem realIwasawaK_apply (g : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) (i j : Fin 2) :
    realIwasawaK g x i j = (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ *
      (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0); g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j :=
  rfl
end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"
end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section

namespace WeylUnipotentDecay

section Transport

variable {G H : Type*} [Group G] [Group H]

private theorem exists_finset_span_comp_monoidHom (ι : H →* G) (S : Subgroup G) (hι : ∀ k : H, ι k ∈ S) (a : G → ℂ)
    (hfin : ∃ t : Finset (G → ℂ), ∀ k' ∈ S, (fun g => a (g * k')) ∈ Submodule.span ℂ (t : Set (G → ℂ))) :
    ∃ s : Finset (H → ℂ), ∀ k : H, (fun x => a (ι (x * k))) ∈ Submodule.span ℂ (s : Set (H → ℂ)) := by
  classical
  obtain ⟨t, ht⟩ := hfin
  refine ⟨t.image (fun f => f ∘ ι), fun k => ?_⟩
  have heq : (fun x => a (ι (x * k))) = (fun g => a (g * ι k)) ∘ ι := by
    funext x
    simp [map_mul]
  rw [heq, Finset.coe_image]
  exact Submodule.apply_mem_span_image_of_mem_span (LinearMap.funLeft ℂ ℂ ι) (ht (ι k) (hι k))

end Transport
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section ArchInclLocal

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm IsDedekindDomain"

variable (F : Type) [Field F]

private theorem continuous_archMatrixUpdate (w : InfinitePlace F) : Continuous (archMatrixUpdate F w) := by
  refine continuous_matrix fun i j => ?_
  refine continuous_pi fun v => ?_
  by_cases hvw : v = w
  · subst hvw
    simp only [archMatrixUpdate_apply_self]
    exact (continuous_apply j).comp (continuous_apply i)
  · simp only [archMatrixUpdate_apply_of_ne F w _ i j hvw]
    exact continuous_const

private theorem continuous_archGLIncl (w : InfinitePlace F) : Continuous (archGLIncl F w) :=
  Continuous.units_map (archMatrixInclHom F w) (continuous_archMatrixUpdate F w)

end ArchInclLocal
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section ArchIncl

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm IsDedekindDomain"

variable (F : Type) [Field F] [NumberField F]

private theorem continuous_adelicMatrixProdEquiv_symm : Continuous (adelicMatrixProdEquiv F).symm := by
  refine continuous_matrix fun i j => ?_
  exact (continuous_fst.matrix_elem i j).prodMk (continuous_snd.matrix_elem i j)

private theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  have h1 : Continuous (MonoidHom.prod (MonoidHom.id (GL (Fin 2) (InfiniteAdeleRing F)))
      (1 : GL (Fin 2) (InfiniteAdeleRing F) →* GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    continuous_id.prodMk continuous_const
  have h2 : Continuous (MulEquiv.prodUnits.symm :
      GL (Fin 2) (InfiniteAdeleRing F) × GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ≃*
        (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))ˣ) :=
    Homeomorph.prodUnits.symm.continuous
  have h3 : Continuous (Units.mapEquiv (adelicMatrixProdEquiv F).symm.toMulEquiv) :=
    Continuous.units_map (adelicMatrixProdEquiv F).symm.toMulEquiv.toMonoidHom (continuous_adelicMatrixProdEquiv_symm F)
  unfold adelicArchGLIncl
  exact h3.comp (h2.comp h1)

private theorem continuous_adelicArchGLInclAt (w : InfinitePlace F) : Continuous (adelicArchGLInclAt F w) := by
  unfold adelicArchGLInclAt
  exact (continuous_adelicArchGLIncl F).comp (continuous_archGLIncl F w)

end ArchIncl
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section

namespace WeylUnipotentDecay

section RealDecay

private theorem rpow_negNat_pos {t : ℝ} (ht : 0 ≤ t) (N : ℕ) : 0 < (1 + t) ^ (-(N : ℝ)) :=
  Real.rpow_pos_of_pos (by linarith) _

private theorem rpow_negNat_le_one {t : ℝ} (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ (-(N : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simp)

private theorem rpow_negNat_antitone {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) (N : ℕ) :
    (1 + u) ^ (-(N : ℝ)) ≤ (1 + t) ^ (-(N : ℝ)) :=
  Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by simp)

private theorem rpow_negNat_one_add_mul_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (N : ℕ) :
    (1 + c * t) ^ (-(N : ℝ)) ≤ max 1 (c ^ (-(N : ℝ))) * (1 + t) ^ (-(N : ℝ)) := by
  rcases le_or_gt 1 c with hc1 | hc1
  · calc (1 + c * t) ^ (-(N : ℝ)) ≤ (1 + t) ^ (-(N : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) (by nlinarith) (by simp)
      _ ≤ max 1 (c ^ (-(N : ℝ))) * (1 + t) ^ (-(N : ℝ)) :=
          le_mul_of_one_le_left (rpow_negNat_pos ht N).le (le_max_left _ _)
  · have h1 : c * (1 + t) ≤ 1 + c * t := by nlinarith
    calc (1 + c * t) ^ (-(N : ℝ)) ≤ (c * (1 + t)) ^ (-(N : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by simp)
      _ = c ^ (-(N : ℝ)) * (1 + t) ^ (-(N : ℝ)) := Real.mul_rpow hc.le (by linarith)
      _ ≤ max 1 (c ^ (-(N : ℝ))) * (1 + t) ^ (-(N : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (rpow_negNat_pos ht N).le

private theorem prod_le_apply_of_nonneg_of_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) (i₀ : ι) : ∏ i, f i ≤ f i₀ := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i₀)]
  exact mul_le_of_le_one_right (h0 i₀) (Finset.prod_le_one (fun i _ => h0 i) (fun i _ => h1 i))

end RealDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section Mixed

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

private theorem prod_rpow_negNat_normAtPlace_le (x : mixedSpace K) (N : ℕ) :
    ∏ w : InfinitePlace K, (1 + normAtPlace w x) ^ (-(N : ℝ)) ≤ (1 + ‖x‖) ^ (-(N : ℝ)) := by
  classical
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun w : InfinitePlace K => normAtPlace w x)
  have hnorm : ‖x‖ = normAtPlace w₀ x := by
    rw [norm_eq_sup'_normAtPlace, hw₀]
  rw [hnorm]
  exact prod_le_apply_of_nonneg_of_le_one (fun w => (1 + normAtPlace w x) ^ (-(N : ℝ)))
    (fun w => (rpow_negNat_pos (normAtPlace_nonneg w x) N).le)
    (fun w => rpow_negNat_le_one (normAtPlace_nonneg w x) N) w₀

private theorem prod_rpow_negNat_mul_apply_le (ξ : K) (N : ℕ) (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w) :
    ∏ w : InfinitePlace K, (1 + c w * w ξ) ^ (-(N : ℝ)) ≤
      (∏ w : InfinitePlace K, max 1 (c w ^ (-(N : ℝ)))) * (1 + ‖mixedEmbedding K ξ‖) ^ (-(N : ℝ)) := by
  have hξ : ∀ w : InfinitePlace K, 0 ≤ w ξ := fun w => apply_nonneg w ξ
  calc ∏ w : InfinitePlace K, (1 + c w * w ξ) ^ (-(N : ℝ))
      ≤ ∏ w : InfinitePlace K, (max 1 (c w ^ (-(N : ℝ))) * (1 + w ξ) ^ (-(N : ℝ))) :=
        Finset.prod_le_prod (fun w _ => (Real.rpow_pos_of_pos (by nlinarith [hc w, hξ w]) _).le)
          (fun w _ => rpow_negNat_one_add_mul_le (hc w) (hξ w) N)
    _ = (∏ w : InfinitePlace K, max 1 (c w ^ (-(N : ℝ)))) * ∏ w : InfinitePlace K, (1 + w ξ) ^ (-(N : ℝ)) :=
        Finset.prod_mul_distrib
    _ ≤ (∏ w : InfinitePlace K, max 1 (c w ^ (-(N : ℝ)))) * (1 + ‖mixedEmbedding K ξ‖) ^ (-(N : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun w _ => le_max_of_le_left zero_le_one)
        simpa only [normAtPlace_apply] using prod_rpow_negNat_normAtPlace_le K (mixedEmbedding K ξ) N

end Mixed
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section

namespace WeylUnipotentDecay

open MeasureTheory

section Generic

variable {α β E : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
  [MeasurableSpace β] [TopologicalSpace β] [BorelSpace β] [NormedAddCommGroup E]

private theorem integral_map_homeomorph [NormedSpace ℝ E] (s : α ≃ₜ β) (μ : Measure α) (f : β → E) :
    ∫ y, f y ∂(μ.map s) = ∫ x, f (s x) ∂μ := by
  rw [← Homeomorph.toMeasurableEquiv_coe]
  exact integral_map_equiv s.toMeasurableEquiv f

private theorem integrable_map_homeomorph_iff (s : α ≃ₜ β) (μ : Measure α) (f : β → E) :
    Integrable f (μ.map s) ↔ Integrable (fun x => f (s x)) μ := by
  rw [← Homeomorph.toMeasurableEquiv_coe]
  exact integrable_map_equiv s.toMeasurableEquiv f

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section Places

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type*} [Field K] {E : Type*} [NormedAddCommGroup E]

private theorem integral_volume_map_ringEquivComplexOfIsComplex_symm {w : InfinitePlace K} (hw : w.IsComplex)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion] [NormedSpace ℝ E] (f : w.Completion → E) :
    ∫ y, f y ∂((volume : Measure ℂ).map (ringEquivComplexOfIsComplex hw).symm) =
      ∫ z : ℂ, f ((ringEquivComplexOfIsComplex hw).symm z) :=
  integral_map_homeomorph (isometryEquivComplexOfIsComplex hw).toHomeomorph.symm volume f

private theorem integrable_volume_map_ringEquivComplexOfIsComplex_symm_iff {w : InfinitePlace K} (hw : w.IsComplex)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion] (f : w.Completion → E) :
    Integrable f ((volume : Measure ℂ).map (ringEquivComplexOfIsComplex hw).symm) ↔
      Integrable (fun z : ℂ => f ((ringEquivComplexOfIsComplex hw).symm z)) :=
  integrable_map_homeomorph_iff (isometryEquivComplexOfIsComplex hw).toHomeomorph.symm volume f

private theorem integral_volume_map_ringEquivRealOfIsReal_symm {v : InfinitePlace K} (hv : v.IsReal)
    [MeasurableSpace v.Completion] [BorelSpace v.Completion] [NormedSpace ℝ E] (f : v.Completion → E) :
    ∫ y, f y ∂((volume : Measure ℝ).map (ringEquivRealOfIsReal hv).symm) =
      ∫ x : ℝ, f ((ringEquivRealOfIsReal hv).symm x) :=
  integral_map_homeomorph (isometryEquivRealOfIsReal hv).toHomeomorph.symm volume f

private theorem integrable_volume_map_ringEquivRealOfIsReal_symm_iff {v : InfinitePlace K} (hv : v.IsReal)
    [MeasurableSpace v.Completion] [BorelSpace v.Completion] (f : v.Completion → E) :
    Integrable f ((volume : Measure ℝ).map (ringEquivRealOfIsReal hv).symm) ↔
      Integrable (fun x : ℝ => f ((ringEquivRealOfIsReal hv).symm x)) :=
  integrable_map_homeomorph_iff (isometryEquivRealOfIsReal hv).toHomeomorph.symm volume f

end Places
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section

namespace WeylUnipotentDecay

section Lists

private theorem prod_ofFn_ite_eq {M : Type*} [Monoid M] {n : ℕ} (i : Fin n) (a : M) :
    (List.ofFn fun j : Fin n => if j = i then a else 1).prod = a := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons]
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rw [if_pos rfl]
        have h : (List.ofFn fun j : Fin n => if (j.succ : Fin (n + 1)) = 0 then a else 1) = List.ofFn fun _ : Fin n => (1 : M) :=
          List.ofFn_inj.mpr (funext fun j => if_neg (Fin.succ_ne_zero j))
        rw [h]
        simp
      · rw [if_neg (Ne.symm (Fin.succ_ne_zero i')), one_mul]
        have h : (List.ofFn fun j : Fin n => if (j.succ : Fin (n + 1)) = i'.succ then a else 1) =
            List.ofFn fun j : Fin n => if j = i' then a else 1 :=
          List.ofFn_inj.mpr (funext fun j => by simp only [Fin.succ_inj])
        rw [h, ih i']

end Lists
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section PlaceGrain

p2m_open "NumberField NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm IsDedekindDomain"

variable (F : Type) [Field F] [NumberField F]

private theorem adelicGL2_ext {g₁ g₂ : AdelicGL2 (𝓞 F) F}
    (harch : ∀ w : InfinitePlace F, archComponent F w (glArch (𝓞 F) F g₁) = archComponent F w (glArch (𝓞 F) F g₂))
    (hfin : glFin (𝓞 F) F g₁ = glFin (𝓞 F) F g₂) : g₁ = g₂ := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun w => ?_) ?_)
  · exact congrArg (fun g : GL (Fin 2) w.Completion => (g : Matrix (Fin 2) (Fin 2) w.Completion) i j) (harch w)
  · exact congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) hfin

private theorem archComponent_glArch_unipotentGL2 (w : InfinitePlace F) (p : AdeleRing (𝓞 F) F) :
    archComponent F w (glArch (𝓞 F) F (unipotentGL2 p)) = unipotentGL2 (p.1 w) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> rfl

private theorem glFin_unipotentGL2 (p : AdeleRing (𝓞 F) F) : glFin (𝓞 F) F (unipotentGL2 p) = unipotentGL2 p.2 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> rfl

private theorem archComponent_glArch_adelicWeyl (w : InfinitePlace F) :
    archComponent F w (glArch (𝓞 F) F (adelicWeyl (𝓞 F) F)) = gl2Weyl := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show archEval F w (adeleArch (𝓞 F) F
      (algebraMap F (AdeleRing (𝓞 F) F) (((gl2Weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j))) =
    ((gl2Weyl : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
  fin_cases i <;> fin_cases j <;> simp [gl2Weyl]

private theorem glFin_adelicWeyl_coe :
    ((glFin (𝓞 F) F (adelicWeyl (𝓞 F) F) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = !![0, 1; 1, 0] := by
  refine Matrix.ext fun i j => ?_
  show adeleFin (𝓞 F) F
      (algebraMap F (AdeleRing (𝓞 F) F) (((gl2Weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j)) =
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
  fin_cases i <;> fin_cases j <;> simp [gl2Weyl]

private theorem archComponent_glArch_adelicArchGLInclAt_self (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    archComponent F w (glArch (𝓞 F) F (adelicArchGLInclAt F w k)) = k := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j w = (k : Matrix (Fin 2) (Fin 2) w.Completion) i j
  exact archMatrixUpdate_apply_self F w _ i j

private theorem archComponent_glArch_adelicArchGLInclAt_of_ne {w w' : InfinitePlace F} (hww' : w ≠ w')
    (k : GL (Fin 2) w'.Completion) :
    archComponent F w (glArch (𝓞 F) F (adelicArchGLInclAt F w' k)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show archMatrixUpdate F w' (k : Matrix (Fin 2) (Fin 2) w'.Completion) i j w = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j
  exact archMatrixUpdate_apply_of_ne F w' _ i j hww'

private theorem glFin_adelicArchGLInclAt (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 F) F (adelicArchGLInclAt F w k) = 1 :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem archComponent_glArch_prod_adelicArchGLInclAt {n : ℕ} (e : Fin n → InfinitePlace F) (he : Function.Injective e)
    (k : ∀ j : Fin n, GL (Fin 2) (e j).Completion) (i : Fin n) :
    archComponent F (e i) (glArch (𝓞 F) F (List.ofFn fun j => adelicArchGLInclAt F (e j) (k j)).prod) = k i := by
  rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
  have h : (List.ofFn ((archComponent F (e i)) ∘ (glArch (𝓞 F) F) ∘ fun j => adelicArchGLInclAt F (e j) (k j))) =
      List.ofFn fun j : Fin n => if j = i then k i else 1 := by
    refine List.ofFn_inj.mpr (funext fun j => ?_)
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      exact archComponent_glArch_adelicArchGLInclAt_self F (e j) (k j)
    · rw [if_neg hj]
      exact archComponent_glArch_adelicArchGLInclAt_of_ne F (fun h => hj (he h).symm) (k j)
  rw [h, prod_ofFn_ite_eq]

private theorem glFin_prod_adelicArchGLInclAt {n : ℕ} (e : Fin n → InfinitePlace F) (k : ∀ j : Fin n, GL (Fin 2) (e j).Completion) :
    glFin (𝓞 F) F (List.ofFn fun j => adelicArchGLInclAt F (e j) (k j)).prod = 1 := by
  rw [map_list_prod, List.map_ofFn]
  have h : (List.ofFn ((glFin (𝓞 F) F) ∘ fun j => adelicArchGLInclAt F (e j) (k j))) = List.ofFn fun _ : Fin n => (1 : _) :=
    List.ofFn_inj.mpr (funext fun j => glFin_adelicArchGLInclAt F (e j) (k j))
  rw [h]
  simp

end PlaceGrain
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section

namespace WeylUnipotentDecay

section TracePi

private theorem trace_pi_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {S : ι → Type*}
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Module.Basis (κ i) R (S i)) (x : ∀ i, S i) :
    Algebra.trace R (∀ i, S i) x = ∑ i, Algebra.trace R (S i) (x i) := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b) x, Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i) (x i), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply, Pi.mul_apply,
    Pi.single_eq_same]

private theorem trace_pi_real_apply {ι : Type*} [Fintype ι] (x : ι → ℝ) : Algebra.trace ℝ (ι → ℝ) x = ∑ i, x i := by
  classical
  rw [trace_pi_apply (fun _ => Module.Basis.singleton Unit ℝ) x]
  simp only [Algebra.trace_self_apply]

private theorem trace_pi_complex_apply {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    Algebra.trace ℝ (ι → ℂ) z = ∑ i, 2 * (z i).re := by
  classical
  rw [trace_pi_apply (fun _ => Complex.basisOneI) z]
  simp only [Algebra.trace_complex_apply]

end TracePi
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section Mixed

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

private theorem trace_mixedSpace_apply (x : mixedSpace K) :
    Algebra.trace ℝ (mixedSpace K) x =
      (∑ w : {w : InfinitePlace K // w.IsReal}, x.1 w) + ∑ w : {w : InfinitePlace K // w.IsComplex}, 2 * (x.2 w).re := by
  classical
  rw [Algebra.trace_prod_apply, trace_pi_real_apply, trace_pi_complex_apply]

private theorem trace_ringEquiv_mixedSpace_apply (y : InfiniteAdeleRing K) :
    Algebra.trace ℝ (mixedSpace K) (InfiniteAdeleRing.ringEquiv_mixedSpace K y) =
      (∑ w : {w : InfinitePlace K // w.IsReal}, Completion.extensionEmbeddingOfIsReal w.2 (y w)) +
        ∑ w : {w : InfinitePlace K // w.IsComplex}, 2 * (Completion.extensionEmbedding w.1 (y w)).re := by
  rw [trace_mixedSpace_apply]
  rfl

end Mixed
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section Phase

open scoped FourierTransform Classical

private theorem fourierChar_sum_coe {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((𝐞 (∑ i ∈ s, f i) : Circle) : ℂ) = ∏ i ∈ s, ((𝐞 (f i) : Circle) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

private theorem fourierChar_trace_ringEquiv_mixedSpace (y : InfiniteAdeleRing K) :
    ((𝐞 (Algebra.trace ℝ (mixedSpace K) (InfiniteAdeleRing.ringEquiv_mixedSpace K y)) : Circle) : ℂ) =
      (∏ w : {w : InfinitePlace K // w.IsReal}, ((𝐞 (Completion.extensionEmbeddingOfIsReal w.2 (y w)) : Circle) : ℂ)) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          ((𝐞 (2 * (Completion.extensionEmbedding w.1 (y w)).re) : Circle) : ℂ) := by
  rw [trace_ringEquiv_mixedSpace_apply, AddChar.map_add_eq_mul, Circle.coe_mul, fourierChar_sum_coe, fourierChar_sum_coe]

private def phaseAt (w : InfinitePlace K) (z : w.Completion) : ℂ :=
  if hw : w.IsReal then ((𝐞 (Completion.extensionEmbeddingOfIsReal hw z) : Circle) : ℂ)
  else ((𝐞 (2 * (Completion.extensionEmbedding w z).re) : Circle) : ℂ)

omit [NumberField K] in
private theorem phaseAt_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (z : w.Completion) :
    phaseAt K w z = ((𝐞 (Completion.extensionEmbeddingOfIsReal hw z) : Circle) : ℂ) := dif_pos hw

omit [NumberField K] in
private theorem phaseAt_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (z : w.Completion) :
    phaseAt K w z = ((𝐞 (2 * (Completion.extensionEmbedding w z).re) : Circle) : ℂ) :=
  dif_neg (not_isReal_iff_isComplex.mpr hw)

private theorem fourierChar_trace_ringEquiv_mixedSpace_eq_prod_phaseAt (y : InfiniteAdeleRing K) :
    ((𝐞 (Algebra.trace ℝ (mixedSpace K) (InfiniteAdeleRing.ringEquiv_mixedSpace K y)) : Circle) : ℂ) =
      ∏ w : InfinitePlace K, phaseAt K w (y w) := by
  rw [fourierChar_trace_ringEquiv_mixedSpace, ← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K => w.IsReal)]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => (phaseAt_of_isReal K w.2 (y w)).symm
  · refine Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => (not_isReal_iff_isComplex (w := w)).symm) _ _ fun w => ?_
    exact (phaseAt_of_isComplex K w.2 (y w)).symm

end Phase
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section Pairing

open scoped FourierTransform ComplexConjugate

private def pairingC : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  Complex.reCLM.smulRight Complex.reCLM + Complex.imCLM.smulRight Complex.imCLM

private theorem pairingC_apply (v ξ : ℂ) : pairingC v ξ = v.re * ξ.re + v.im * ξ.im := by
  simp [pairingC]

private theorem pairingC_self (ξ : ℂ) : pairingC ξ ξ = ‖ξ‖ ^ 2 := by
  rw [pairingC_apply, Complex.sq_norm, Complex.normSq_apply]

private theorem two_mul_re_mul_eq_neg_pairingC (c z : ℂ) :
    2 * (c * z).re = -(pairingC z ((-2 : ℝ) • conj c)) := by
  simp only [pairingC_apply, Complex.mul_re, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_ofNat, neg_mul,
    Complex.neg_re, Complex.neg_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

private theorem fourierChar_two_mul_re_mul (c z : ℂ) :
    ((𝐞 (2 * (c * z).re) : Circle) : ℂ) = 𝐞 (-(pairingC z ((-2 : ℝ) • conj c))) := by
  rw [two_mul_re_mul_eq_neg_pairingC]

private theorem norm_freqC (c : ℂ) : ‖((-2 : ℝ) • conj c : ℂ)‖ = 2 * ‖c‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_two, Complex.norm_conj]

private def pairingR : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ

private theorem pairingR_apply (v ξ : ℝ) : pairingR v ξ = v * ξ := rfl

private theorem mul_eq_neg_pairingR (c x : ℝ) : c * x = -(pairingR x (-c)) := by
  rw [pairingR_apply]; ring

private theorem fourierChar_mul (c x : ℝ) : ((𝐞 (c * x) : Circle) : ℂ) = 𝐞 (-(pairingR x (-c))) := by
  rw [mul_eq_neg_pairingR]

private theorem norm_freqR (c : ℝ) : ‖(-c : ℝ)‖ = ‖c‖ := norm_neg c

end Pairing
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

namespace WeylUnipotentDecay

open MeasureTheory

private theorem integral_fintype_prod_comp_equiv_eq_prod {𝕜 ι ι' : Type*} [Fintype ι] [Fintype ι'] [RCLike 𝕜] (e : ι' ≃ ι)
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i' : ι', E (e i') → 𝕜) :
    ∫ x : (i : ι) → E i, ∏ i', f i' (x (e i')) ∂(Measure.pi μ) = ∏ i', ∫ y, f i' y ∂(μ (e i')) := by
  rw [← (measurePreserving_piCongrLeft μ e).integral_comp']
  simp_rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact integral_fintype_prod_eq_prod (fun i' => f i')

private theorem integral_const_mul_fintype_prod_comp_equiv {𝕜 ι ι' : Type*} [Fintype ι] [Fintype ι'] [RCLike 𝕜] (e : ι' ≃ ι)
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (c : 𝕜) (f : ∀ i' : ι', E (e i') → 𝕜) :
    ∫ x : (i : ι) → E i, c * ∏ i', f i' (x (e i')) ∂(Measure.pi μ) = c * ∏ i', ∫ y, f i' y ∂(μ (e i')) := by
  rw [integral_const_mul, integral_fintype_prod_comp_equiv_eq_prod]

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

namespace WeylUnipotentDecay

private theorem real_botRowNormSq_pos {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (x : ℝ) :
    0 < (g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2 := by
  rcases (add_nonneg (sq_nonneg (g 0 0 + x * g 1 0)) (sq_nonneg (g 0 1 + x * g 1 1))).lt_or_eq with h | h
  · exact h
  · exfalso
    have ha : g 0 0 + x * g 1 0 = 0 := by nlinarith [sq_nonneg (g 0 0 + x * g 1 0), sq_nonneg (g 0 1 + x * g 1 1)]
    have hb : g 0 1 + x * g 1 1 = 0 := by nlinarith [sq_nonneg (g 0 0 + x * g 1 0), sq_nonneg (g 0 1 + x * g 1 1)]
    apply hg
    rw [Matrix.det_fin_two]
    linear_combination g 1 1 * ha - g 1 0 * hb

private theorem real_weyl_mul_unipotent_mul_eq_borel_mul_smul {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (x : ℝ) :
    !![(0 : ℝ), 1; 1, 0] * !![1, x; 0, 1] * g =
      !![-g.det / Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2),
          (g 1 0 * (g 0 0 + x * g 1 0) + g 1 1 * (g 0 1 + x * g 1 1)) /
            Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2);
         0, Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2)] *
        ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ •
          (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0); g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] :
            Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hS := real_botRowNormSq_pos hg x
  have hr0 : Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  have hr : Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) ^ 2 =
      (g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2 := Real.sq_sqrt hS.le
  generalize Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) = r at hr0 hr ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Matrix.det_fin_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.isValue, Fin.mk_one, Fin.zero_eta, one_mul, zero_mul, add_zero, zero_add]
  · field_simp
    linear_combination (g 1 0) * hr
  · field_simp
    linear_combination (g 1 1) * hr
  · field_simp
  · field_simp

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section

namespace WeylUnipotentDecay

section BorelIncl

p2m_open "NumberField NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm IsDedekindDomain"

variable (F : Type) [Field F] [NumberField F]

private theorem coe_apply_fst_apply (g : AdelicGL2 (𝓞 F) F) (i j : Fin 2) (w : InfinitePlace F) :
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w =
      (archComponent F w (glArch (𝓞 F) F g) : Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl

private theorem coe_apply_snd (g : AdelicGL2 (𝓞 F) F) (i j : Fin 2) :
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 =
      (glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := rfl

variable {n : ℕ} (e : Fin n ≃ InfinitePlace F) (B : ∀ j : Fin n, GL (Fin 2) (e j).Completion)

private theorem prod_adelicArchGLInclAt_mem_adelicBorel (hB : ∀ j, (B j : Matrix (Fin 2) (Fin 2) (e j).Completion) 1 0 = 0) :
    (List.ofFn fun j => adelicArchGLInclAt F (e j) (B j)).prod ∈ adelicBorel (𝓞 F) F := by
  rw [mem_borelSubgroup_iff]
  refine Prod.ext (funext fun w => ?_) ?_
  · obtain ⟨j, rfl⟩ := e.surjective w
    rw [coe_apply_fst_apply, archComponent_glArch_prod_adelicArchGLInclAt F e e.injective B j]
    exact hB j
  · rw [coe_apply_snd, glFin_prod_adelicArchGLInclAt]
    exact Matrix.one_apply_ne (by decide)

private theorem borelDiagFst_prod_val_fst_apply (h : (List.ofFn fun j => adelicArchGLInclAt F (e j) (B j)).prod ∈ adelicBorel (𝓞 F) F)
    (j : Fin n) :
    ((borelDiagFst (⟨_, h⟩ : ↥(adelicBorel (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 (e j) =
      (B j : Matrix (Fin 2) (Fin 2) (e j).Completion) 0 0 := by
  rw [borelDiagFst_apply_val, coe_apply_fst_apply, archComponent_glArch_prod_adelicArchGLInclAt F e e.injective B j]

private theorem borelDiagFst_prod_val_snd (h : (List.ofFn fun j => adelicArchGLInclAt F (e j) (B j)).prod ∈ adelicBorel (𝓞 F) F) :
    ((borelDiagFst (⟨_, h⟩ : ↥(adelicBorel (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  rw [borelDiagFst_apply_val, coe_apply_snd, glFin_prod_adelicArchGLInclAt]
  exact Matrix.one_apply_eq 0

private theorem borelDiagSnd_prod_val_fst_apply (h : (List.ofFn fun j => adelicArchGLInclAt F (e j) (B j)).prod ∈ adelicBorel (𝓞 F) F)
    (j : Fin n) :
    ((borelDiagSnd (⟨_, h⟩ : ↥(adelicBorel (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 (e j) =
      (B j : Matrix (Fin 2) (Fin 2) (e j).Completion) 1 1 := by
  rw [borelDiagSnd_apply_val, coe_apply_fst_apply, archComponent_glArch_prod_adelicArchGLInclAt F e e.injective B j]

private theorem borelDiagSnd_prod_val_snd (h : (List.ofFn fun j => adelicArchGLInclAt F (e j) (B j)).prod ∈ adelicBorel (𝓞 F) F) :
    ((borelDiagSnd (⟨_, h⟩ : ↥(adelicBorel (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  rw [borelDiagSnd_apply_val, coe_apply_snd, glFin_prod_adelicArchGLInclAt]
  exact Matrix.one_apply_eq 1

end BorelIncl
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

namespace WeylUnipotentDecay

section PlaceBorel

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm"

variable {K L : Type*} [NormedField K] [NormedField L]

private theorem glMapRingEquiv_gl2Weyl (e : K ≃+* L) : glMapRingEquiv e (gl2Weyl : GL (Fin 2) K) = gl2Weyl := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glMapRingEquiv_coe_apply, gl2Weyl_val, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

private theorem glMapRingEquiv_unipotentGL2 (e : K ≃+* L) (y : K) : glMapRingEquiv e (unipotentGL2 y) = unipotentGL2 (e y) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glMapRingEquiv_coe_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply (e : K ≃+* L) (g k : GL (Fin 2) K) (y : K)
    (B : Matrix (Fin 2) (Fin 2) L)
    (h : !![(0 : L), 1; 1, 0] * !![1, e y; 0, 1] * ((glMapRingEquiv e g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = B * ((glMapRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) (i j : Fin 2) :
    ((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = e.symm (B i j) := by
  have hs : e (((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) = B i j := by
    rw [← glMapRingEquiv_coe_apply, map_mul, map_mul, map_mul, map_inv, glMapRingEquiv_gl2Weyl, glMapRingEquiv_unipotentGL2,
      Units.val_mul, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, gl2Weyl_val, unipotentGL2_coe, h,
      Matrix.mul_nonsing_inv_cancel_right _ B (Matrix.isUnits_det_units (glMapRingEquiv e k))]
  simpa using congrArg e.symm hs

private theorem coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_one_zero (e : K ≃+* L) (g k : GL (Fin 2) K) (y : K)
    (B : Matrix (Fin 2) (Fin 2) L)
    (h : !![(0 : L), 1; 1, 0] * !![1, e y; 0, 1] * ((glMapRingEquiv e g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = B * ((glMapRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) (hB : B 1 0 = 0) :
    ((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  rw [coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply e g k y B h, hB, map_zero]

private theorem norm_coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply (e : K ≃+* L) (he : ∀ x, ‖e x‖ = ‖x‖) (g k : GL (Fin 2) K)
    (y : K) (B : Matrix (Fin 2) (Fin 2) L)
    (h : !![(0 : L), 1; 1, 0] * !![1, e y; 0, 1] * ((glMapRingEquiv e g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = B * ((glMapRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) (i j : Fin 2) :
    ‖((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ = ‖B i j‖ := by
  rw [coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply e g k y B h, ← he, RingEquiv.apply_symm_apply]

end PlaceBorel
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"
end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

namespace WeylUnipotentDecay
section GrpSplit

variable {G M : Type*} [Group G] [Mul M]

private theorem apply_eq_mul_apply_of_inv_mul_eq {f : G → M} {b : G} {c : M} (hf : ∀ g, f (b * g) = c * f g)
    {x x' : G} (hx : b⁻¹ * x = x') : f x = c * f x' := by
  rw [← hx, ← hf, mul_inv_cancel_left]

private theorem apply_eq_mul_apply_inv_mul {f : G → M} {b : G} {c : M} (hf : ∀ g, f (b * g) = c * f g) (x : G) :
    f x = c * f (b⁻¹ * x) :=
  apply_eq_mul_apply_of_inv_mul_eq hf rfl

private theorem apply_eq_mul_apply_of_eq_mul {f : G → M} {b : G} {c : M} (hf : ∀ g, f (b * g) = c * f g)
    {x x' : G} (hx : x = b * x') : f x = c * f x' := by
  rw [hx, hf]

end GrpSplit
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"
end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

namespace WeylUnipotentDecay

section EtaArch

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm"

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (c : ℂ) : ((x : ℂ)) ^ c = Complex.exp (c * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le, mul_comm]

private theorem etaFst_one_mul_etaSnd_one_eq_prod {ι : Type*} [Fintype ι]
    (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (a d : (AdeleRing R K)ˣ)
    (m : ι → ℕ) (N D : ι → ℝ) (hN : ∀ i, 0 < N i) (hD : ∀ i, 0 < D i)
    (hαa : ((α a : ℝˣ) : ℝ) = ∏ i, (N i / D i) ^ m i) (hαd : ((α d : ℝˣ) : ℝ) = ∏ i, D i ^ m i) :
    ((etaFst 1 α hα s a : ℂˣ) : ℂ) * ((etaSnd 1 α hα s d : ℂˣ) : ℂ)
      = (∏ i, ((N i : ℝ) : ℂ) ^ ((m i : ℂ) * (s + 1 / 2))) * ∏ i, ((D i : ℝ) : ℂ) ^ (-((m i : ℂ) * (2 * s + 1))) := by
  have hpa : 0 < ∏ i, (N i / D i) ^ m i := Finset.prod_pos fun i _ => pow_pos (div_pos (hN i) (hD i)) _
  have hpd : 0 < ∏ i, D i ^ m i := Finset.prod_pos fun i _ => pow_pos (hD i) _
  have hdiv : ∀ i, Real.log (N i / D i) = Real.log (N i) - Real.log (D i) := fun i => Real.log_div (hN i).ne' (hD i).ne'
  have hR1 : ∀ i, ((N i : ℝ) : ℂ) ^ ((m i : ℂ) * (s + 1 / 2)) =
      Complex.exp (((m i : ℂ) * (s + 1 / 2)) * (Real.log (N i) : ℂ)) := fun i => ofReal_cpow_eq_exp (hN i) _
  have hR2 : ∀ i, ((D i : ℝ) : ℂ) ^ (-((m i : ℂ) * (2 * s + 1))) =
      Complex.exp ((-((m i : ℂ) * (2 * s + 1))) * (Real.log (D i) : ℂ)) := fun i => ofReal_cpow_eq_exp (hD i) _
  rw [etaFst_apply, etaSnd_apply, Units.val_mul, Units.val_mul, MonoidHom.one_apply, MonoidHom.one_apply, Units.val_one,
    one_mul, one_mul, cpowChar_apply_val, cpowChar_apply_val, hαa, hαd, ofReal_cpow_eq_exp hpa, ofReal_cpow_eq_exp hpd,
    Real.log_prod (fun i _ => (pow_pos (div_pos (hN i) (hD i)) _).ne'), Real.log_prod (fun i _ => (pow_pos (hD i) _).ne')]
  simp_rw [Real.log_pow, hdiv, hR1, hR2]
  rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end EtaArch
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section

namespace WeylUnipotentDecay

section EtaModulus

p2m_open "MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm IsDedekindDomain"
open scoped NNReal

variable (F : Type) [Field F] [NumberField F]
variable {n : ℕ} (e : Fin n ≃ InfinitePlace F) (B : ∀ j : Fin n, GL (Fin 2) (e j).Completion)

private theorem val_modulus_borelDiagFst_prod
    (h : (List.ofFn fun j => adelicArchGLInclAt F (e j) (B j)).prod ∈ adelicBorel (𝓞 F) F)
    (v : Fin n → ℝ) (hv : ∀ j, ‖(B j : Matrix (Fin 2) (Fin 2) (e j).Completion) 0 0‖ = v j) :
    (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits :
          (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
        (borelDiagFst (⟨_, h⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) = ∏ j, v j ^ (e j).mult := by
  show ((distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagFst (⟨_, h⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝ≥0) : ℝ) = _
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F _
      (borelDiagFst_prod_val_snd F e B h), ← e.prod_comp]
  exact Finset.prod_congr rfl fun j _ => by rw [borelDiagFst_prod_val_fst_apply F e B h j, hv j]

private theorem val_modulus_borelDiagSnd_prod
    (h : (List.ofFn fun j => adelicArchGLInclAt F (e j) (B j)).prod ∈ adelicBorel (𝓞 F) F)
    (v : Fin n → ℝ) (hv : ∀ j, ‖(B j : Matrix (Fin 2) (Fin 2) (e j).Completion) 1 1‖ = v j) :
    (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits :
          (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
        (borelDiagSnd (⟨_, h⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) = ∏ j, v j ^ (e j).mult := by
  show ((distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagSnd (⟨_, h⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝ≥0) : ℝ) = _
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F _
      (borelDiagSnd_prod_val_snd F e B h), ← e.prod_comp]
  exact Finset.prod_congr rfl fun j _ => by rw [borelDiagSnd_prod_val_fst_apply F e B h j, hv j]

end EtaModulus
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

namespace WeylUnipotentDecay

section PlaceEnt

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm"

private theorem radC_pos_of_det_ne_zero {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    0 < ComplexIwasawa.radC g z := by
  rw [ComplexIwasawa.radC]
  apply Real.sqrt_pos.2
  rcases (add_nonneg (Complex.normSq_nonneg (ComplexIwasawa.botP g z))
      (Complex.normSq_nonneg (ComplexIwasawa.botQ g z))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hP : Complex.normSq (ComplexIwasawa.botP g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (ComplexIwasawa.botP g z), Complex.normSq_nonneg (ComplexIwasawa.botQ g z)]
    have hQ : Complex.normSq (ComplexIwasawa.botQ g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (ComplexIwasawa.botP g z), Complex.normSq_nonneg (ComplexIwasawa.botQ g z)]
    have hP0 := Complex.normSq_eq_zero.1 hP
    have hQ0 := Complex.normSq_eq_zero.1 hQ
    rw [ComplexIwasawa.botP] at hP0
    rw [ComplexIwasawa.botQ] at hQ0
    apply hg
    rw [Matrix.det_fin_two]
    have ha : g 0 0 = -(z * g 1 0) := by linear_combination hP0
    have hb : g 0 1 = -(z * g 1 1) := by linear_combination hQ0
    rw [ha, hb]
    ring

variable {K : Type*} [NormedField K]

private theorem placeEntries_complex (e : K ≃+* ℂ) (he : ∀ x, ‖e x‖ = ‖x‖) (g k : GL (Fin 2) K) (y : K)
    (gC : Matrix (Fin 2) (Fin 2) ℂ) (hgC : ((glMapRingEquiv e g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = gC)
    (hk : ((glMapRingEquiv e k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = ComplexIwasawa.kC gC (e y)) :
    0 < ComplexIwasawa.radC gC (e y) ∧ 0 < ‖gC.det‖ ∧
      ((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      ‖((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0‖
        = ‖gC.det‖ / ComplexIwasawa.radC gC (e y) ∧
      ‖((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1‖
        = ComplexIwasawa.radC gC (e y) := by
  have hdet : gC.det ≠ 0 := by rw [← hgC]; exact Matrix.GeneralLinearGroup.det_ne_zero _
  have hr : 0 < ComplexIwasawa.radC gC (e y) := radC_pos_of_det_ne_zero hdet (e y)
  have h := ComplexIwasawa.weyl_mul_unipotent_mul_eq_borel_mul_kC hdet (e y)
  rw [← hk, ← hgC] at h
  refine ⟨hr, norm_pos_iff.2 hdet,
    coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_one_zero e g k y _ h (by simp), ?_, ?_⟩
  · rw [norm_coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply e he g k y _ h, hgC]
    show ‖-gC.det / (ComplexIwasawa.radC gC (e y) : ℂ)‖ = _
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg hr.le]
  · rw [norm_coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply e he g k y _ h, hgC]
    show ‖(ComplexIwasawa.radC gC (e y) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le]

private theorem placeEntries_real (e : K ≃+* ℝ) (he : ∀ x, ‖e x‖ = ‖x‖) (g k : GL (Fin 2) K) (y : K)
    (gR : Matrix (Fin 2) (Fin 2) ℝ) (hgR : ((glMapRingEquiv e g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = gR)
    (hk : ((glMapRingEquiv e k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = realIwasawaK gR (e y)) :
    0 < Real.sqrt ((gR 0 0 + e y * gR 1 0) ^ 2 + (gR 0 1 + e y * gR 1 1) ^ 2) ∧ 0 < |gR.det| ∧
      ((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      ‖((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0‖
        = |gR.det| / Real.sqrt ((gR 0 0 + e y * gR 1 0) ^ 2 + (gR 0 1 + e y * gR 1 1) ^ 2) ∧
      ‖((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1‖
        = Real.sqrt ((gR 0 0 + e y * gR 1 0) ^ 2 + (gR 0 1 + e y * gR 1 1) ^ 2) := by
  have hdet : gR.det ≠ 0 := by rw [← hgR]; exact Matrix.GeneralLinearGroup.det_ne_zero _
  have hr : 0 < Real.sqrt ((gR 0 0 + e y * gR 1 0) ^ 2 + (gR 0 1 + e y * gR 1 1) ^ 2) :=
    Real.sqrt_pos.2 (real_botRowNormSq_pos hdet (e y))
  have h := real_weyl_mul_unipotent_mul_eq_borel_mul_smul hdet (e y)
  change _ = _ * realIwasawaK gR (e y) at h
  rw [← hk, ← hgR] at h
  refine ⟨hr, abs_pos.2 hdet,
    coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_one_zero e g k y _ h (by simp), ?_, ?_⟩
  · rw [norm_coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply e he g k y _ h, hgR]
    show ‖-gR.det / Real.sqrt ((gR 0 0 + e y * gR 1 0) ^ 2 + (gR 0 1 + e y * gR 1 1) ^ 2)‖ = _
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hr]
  · rw [norm_coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply e he g k y _ h, hgR]
    show ‖Real.sqrt ((gR 0 0 + e y * gR 1 0) ^ 2 + (gR 0 1 + e y * gR 1 1) ^ 2)‖ = _
    rw [Real.norm_eq_abs, abs_of_pos hr]

private theorem placeValues_complex (e : K ≃+* ℂ) (g k : GL (Fin 2) K) (y : K)
    (gC : Matrix (Fin 2) (Fin 2) ℂ) (hgC : ((glMapRingEquiv e g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = gC)
    (hk : ((glMapRingEquiv e k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = ComplexIwasawa.kC gC (e y)) :
    ((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
        = e.symm (-gC.det / (ComplexIwasawa.radC gC (e y) : ℂ)) ∧
      ((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1
        = e.symm (ComplexIwasawa.radC gC (e y) : ℂ) := by
  have hdet : gC.det ≠ 0 := by rw [← hgC]; exact Matrix.GeneralLinearGroup.det_ne_zero _
  have h := ComplexIwasawa.weyl_mul_unipotent_mul_eq_borel_mul_kC hdet (e y)
  rw [← hk, ← hgC] at h
  refine ⟨?_, ?_⟩
  · rw [coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply e g k y _ h, hgC]; rfl
  · rw [coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply e g k y _ h, hgC]; rfl

private theorem placeValues_real (e : K ≃+* ℝ) (g k : GL (Fin 2) K) (y : K)
    (gR : Matrix (Fin 2) (Fin 2) ℝ) (hgR : ((glMapRingEquiv e g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = gR)
    (hk : ((glMapRingEquiv e k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = realIwasawaK gR (e y)) :
    ((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
        = e.symm (-gR.det / Real.sqrt ((gR 0 0 + e y * gR 1 0) ^ 2 + (gR 0 1 + e y * gR 1 1) ^ 2)) ∧
      ((gl2Weyl * unipotentGL2 y * g * k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1
        = e.symm (Real.sqrt ((gR 0 0 + e y * gR 1 0) ^ 2 + (gR 0 1 + e y * gR 1 1) ^ 2)) := by
  have hdet : gR.det ≠ 0 := by rw [← hgR]; exact Matrix.GeneralLinearGroup.det_ne_zero _
  have h := real_weyl_mul_unipotent_mul_eq_borel_mul_smul hdet (e y)
  change _ = _ * realIwasawaK gR (e y) at h
  rw [← hk, ← hgR] at h
  refine ⟨?_, ?_⟩
  · rw [coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply e g k y _ h, hgR]; rfl
  · rw [coe_gl2Weyl_mul_unipotentGL2_mul_mul_inv_apply e g k y _ h, hgR]; rfl

end PlaceEnt
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section

namespace WeylUnipotentDecay

section CharSplit

open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

private def archIdele : ((v : InfinitePlace F) → (v.Completion)ˣ) →* (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).comp
    (MulEquiv.piUnits (M := fun v : InfinitePlace F => v.Completion)).symm.toMonoidHom

open scoped Classical in

private def ideleAt (w : InfinitePlace F) (x : (w.Completion)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  archIdele F (Pi.mulSingle w x)

private def archUnits (a : (AdeleRing (𝓞 F) F)ˣ) : (v : InfinitePlace F) → (v.Completion)ˣ :=
  MulEquiv.piUnits (M := fun v : InfinitePlace F => v.Completion)
    (Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) a)

private theorem val_archUnits_apply (a : (AdeleRing (𝓞 F) F)ˣ) (v : InfinitePlace F) :
    ((archUnits F a v : (v.Completion)ˣ) : v.Completion) = (a : AdeleRing (𝓞 F) F).1 v := rfl

private theorem val_archIdele_snd (u : (v : InfinitePlace F) → (v.Completion)ˣ) :
    ((archIdele F u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl

private theorem archIdele_archUnits (a : (AdeleRing (𝓞 F) F)ˣ) (ha : (a : AdeleRing (𝓞 F) F).2 = 1) :
    archIdele F (archUnits F a) = a := by
  ext : 1
  refine Prod.ext (funext fun v => rfl) ?_
  rw [val_archIdele_snd, ha]

open scoped Classical in

private theorem map_eq_prod_ideleAt {M : Type*} [CommMonoid M] (χ : (AdeleRing (𝓞 F) F)ˣ →* M)
    (a : (AdeleRing (𝓞 F) F)ˣ) (ha : (a : AdeleRing (𝓞 F) F).2 = 1) :
    χ a = ∏ v, χ (ideleAt F v (archUnits F a v)) := by
  have h := map_prod (χ.comp (archIdele F)) (fun v => Pi.mulSingle v (archUnits F a v)) Finset.univ
  rw [Finset.univ_prod_mulSingle, MonoidHom.comp_apply, archIdele_archUnits F a ha] at h
  exact h

open scoped Classical in
private theorem ideleAt_mul (w : InfinitePlace F) (x y : (w.Completion)ˣ) :
    ideleAt F w (x * y) = ideleAt F w x * ideleAt F w y := by
  rw [ideleAt, ideleAt, ideleAt, Pi.mulSingle_mul, map_mul]

open scoped Classical in
private theorem ideleAt_inv (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    ideleAt F w x⁻¹ = (ideleAt F w x)⁻¹ := by
  rw [ideleAt, ideleAt, Pi.mulSingle_inv, map_inv]

open scoped Classical in
private theorem val_ideleAt (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    ((ideleAt F w x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = (Pi.mulSingle w (x : w.Completion), 1) := by
  refine Prod.ext (funext fun v => ?_) rfl
  show ((Pi.mulSingle w x : ∀ v : InfinitePlace F, (v.Completion)ˣ) v : v.Completion)
    = Pi.mulSingle w (x : w.Completion) v
  by_cases h : v = w
  · subst h; rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, Units.val_one]

open scoped Classical in
private theorem val_ideleAt_fst (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    ((ideleAt F w x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = Pi.mulSingle w (x : w.Completion) :=
  congrArg Prod.fst (val_ideleAt F w x)

open scoped Classical in

private theorem distribHaarChar_ideleAt (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    (MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) (ideleAt F w x) : ℝ) = ‖(x : w.Completion)‖ ^ w.mult := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F (ideleAt F w x)
      (val_archIdele_snd F _), val_ideleAt_fst]
  rw [Finset.prod_eq_single w (fun v _ hv => by rw [Pi.mulSingle_eq_of_ne hv, norm_one, one_pow])
    (fun h => (h (Finset.mem_univ w)).elim), Pi.mulSingle_eq_same]

private def diagGL2 (a d : (AdeleRing (𝓞 F) F)ˣ) : AdelicGL2 (𝓞 F) F where
  val := Matrix.diagonal ![(a : AdeleRing (𝓞 F) F), d]
  inv := Matrix.diagonal ![((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), ((d⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp

private theorem diagGL2_mem (a d : (AdeleRing (𝓞 F) F)ˣ) : diagGL2 F a d ∈ adelicBorel (𝓞 F) F := by
  show (Matrix.diagonal ![(a : AdeleRing (𝓞 F) F), d] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem borelDiagFst_diagGL2 (a d : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨diagGL2 F a d, diagGL2_mem F a d⟩ : ↥(adelicBorel (𝓞 F) F)) = a :=
  Units.ext (by
    rw [borelDiagFst_apply_val]
    show (Matrix.diagonal ![(a : AdeleRing (𝓞 F) F), d] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = a
    rw [Matrix.diagonal_apply_eq]; rfl)

private theorem borelDiagSnd_diagGL2 (a d : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨diagGL2 F a d, diagGL2_mem F a d⟩ : ↥(adelicBorel (𝓞 F) F)) = d :=
  Units.ext (by
    rw [borelDiagSnd_apply_val]
    show (Matrix.diagonal ![(a : AdeleRing (𝓞 F) F), d] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = d
    rw [Matrix.diagonal_apply_eq]; rfl)

private theorem continuous_diagGL2 {X : Type*} [TopologicalSpace X] {a d : X → (AdeleRing (𝓞 F) F)ˣ}
    (ha : Continuous fun x => (a x : AdeleRing (𝓞 F) F))
    (ha' : Continuous fun x => (((a x)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
    (hd : Continuous fun x => (d x : AdeleRing (𝓞 F) F))
    (hd' : Continuous fun x => (((d x)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) :
    Continuous fun x => diagGL2 F (a x) (d x) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x => Matrix.diagonal ![(a x : AdeleRing (𝓞 F) F), d x]
    refine Continuous.matrix_diagonal (continuous_pi fun k => ?_)
    fin_cases k
    · exact ha
    · exact hd
  · show Continuous fun x => Matrix.diagonal
      ![(((a x)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), (((d x)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)]
    refine Continuous.matrix_diagonal (continuous_pi fun k => ?_)
    fin_cases k
    · exact ha'
    · exact hd'

private theorem exists_forall_eq_cpow_of_continuousOn_of_norm_eq_one {χ : ℝ → ℂ}
    (hcont : ContinuousOn χ (Set.Ioi 0))
    (hmul : ∀ x y : ℝ, 0 < x → 0 < y → χ (x * y) = χ x * χ y)
    (hnorm : ∀ x : ℝ, 0 < x → ‖χ x‖ = 1) :
    ∃ t : ℝ, ∀ x : ℝ, 0 < x → χ x = (x : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hχc : Continuous fun u : ℝ => χ (Real.exp u) :=
    hcont.comp_continuous Real.continuous_exp fun u => Real.exp_pos u
  have h1 : χ 1 = 1 := by
    have hsq : χ 1 * χ 1 = χ 1 := by rw [← hmul 1 1 one_pos one_pos, one_mul]
    have hne : χ 1 ≠ 0 := fun h => by simpa [h] using hnorm 1 one_pos
    exact (mul_eq_left₀ hne).1 hsq
  let f : C(ℝ, Circle) :=
    ⟨fun u => ⟨χ (Real.exp u), mem_sphere_zero_iff_norm.2 (hnorm _ (Real.exp_pos u))⟩, hχc.subtype_mk _⟩
  have hf : ∀ u, ((f u : Circle) : ℂ) = χ (Real.exp u) := fun _ => rfl
  have hf0 : f 0 = 1 := Circle.ext (by rw [hf, Real.exp_zero, h1, Circle.coe_one])
  have hfadd : ∀ u v, f (u + v) = f u * f v := fun u v =>
    Circle.ext (by rw [Circle.coe_mul, hf, hf, hf, Real.exp_add, hmul _ _ (Real.exp_pos u) (Real.exp_pos v)])
  obtain ⟨Fl, ⟨hF0, hFlift⟩, huniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 (by rw [hf0]; exact Circle.exp_zero)
  have hFl : ∀ u, Circle.exp (Fl u) = f u := fun u => congrFun hFlift u
  have hadd : ∀ u v, Fl (u + v) = Fl u + Fl v := by
    intro u v
    let G : C(ℝ, ℝ) := ⟨fun w => Fl (w + v) - Fl v, by fun_prop⟩
    have hG : G = Fl := huniq G ⟨by simp [G], funext fun w => by
      show Circle.exp (Fl (w + v) - Fl v) = f w
      rw [Circle.exp_sub, hFl, hFl, hfadd, mul_div_cancel_right]⟩
    have := congrArg (fun H : C(ℝ, ℝ) => H u) hG
    simp only [G, ContinuousMap.coe_mk] at this
    linarith
  let Fa : ℝ →+ ℝ := { toFun := Fl, map_zero' := hF0, map_add' := hadd }
  have hlin : ∀ u, Fl u = u * Fl 1 := fun u => by
    have := map_real_smul Fa Fl.continuous u 1
    simpa [Fa, smul_eq_mul] using this
  refine ⟨Fl 1, fun x hx => ?_⟩
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  calc χ x = χ (Real.exp (Real.log x)) := by rw [Real.exp_log hx]
    _ = ((f (Real.log x) : Circle) : ℂ) := (hf _).symm
    _ = ((Circle.exp (Fl (Real.log x)) : Circle) : ℂ) := by rw [hFl]
    _ = Complex.exp (((Real.log x * Fl 1 : ℝ) : ℂ) * Complex.I) := by rw [Circle.coe_exp, hlin]
    _ = (x : ℂ) ^ ((Fl 1 : ℂ) * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
      push_cast
      ring_nf

end CharSplit
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

namespace WeylUnipotentDecay
section GrpSplit2

variable {G M : Type*} [Group G] [Mul M]

private theorem apply_mul_word_eq {f : G → M} {b : G} {c : M} (hf : ∀ g, f (b * g) = c * f g) (u v g k : G) :
    f (b * (u * v * g * k⁻¹)) = c * f (u * v * (g * k⁻¹)) := by
  rw [hf, mul_assoc (u * v) g k⁻¹]

end GrpSplit2
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"
end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section
namespace WeylUnipotentDecay

open MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ComplexConjugate ContDiff

section CplxRad

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

private def cplxBotNormSq (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Complex.normSq (g 1 0) + Complex.normSq (g 1 1)

private def cplxCenter (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  -(conj (g 1 0) * g 0 0 + conj (g 1 1) * g 0 1) / (cplxBotNormSq g : ℂ)

private theorem radC_sq_eq_normSq_add (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    radC g z ^ 2 = Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
  rw [radC, Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]

private theorem cplxBotNormSq_pos (hg : g.det ≠ 0) : 0 < cplxBotNormSq g := by
  rw [cplxBotNormSq]
  rcases (add_nonneg (Complex.normSq_nonneg (g 1 0)) (Complex.normSq_nonneg (g 1 1))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hc : Complex.normSq (g 1 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (g 1 0), Complex.normSq_nonneg (g 1 1)]
    have hd : Complex.normSq (g 1 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (g 1 0), Complex.normSq_nonneg (g 1 1)]
    apply hg
    rw [Matrix.det_fin_two, Complex.normSq_eq_zero.1 hc, Complex.normSq_eq_zero.1 hd,
      mul_zero, mul_zero, sub_zero]

private theorem radC_sq_eq_completedSquare (hg : g.det ≠ 0) (z : ℂ) :
    radC g z ^ 2 = cplxBotNormSq g * Complex.normSq (z - cplxCenter g)
      + Complex.normSq g.det / cplxBotNormSq g := by
  have hA : cplxBotNormSq g ≠ 0 := (cplxBotNormSq_pos hg).ne'
  have hAc : (cplxBotNormSq g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA
  have hz : z - cplxCenter g = ((cplxBotNormSq g : ℂ) * z + ((starRingEnd ℂ) (g 1 0) * g 0 0
      + (starRingEnd ℂ) (g 1 1) * g 0 1)) / (cplxBotNormSq g : ℂ) := by
    rw [cplxCenter]
    field_simp
    try ring
  rw [radC_sq_eq_normSq_add, hz, Complex.normSq_div, Complex.normSq_ofReal, Matrix.det_fin_two]
  field_simp
  simp only [botP, botQ, cplxBotNormSq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem contDiff_radC_of_det_ne_zero (hg : g.det ≠ 0) : ContDiff ℝ ∞ (radC g) := by
  have hnormSq : ContDiff ℝ ∞ Complex.normSq := by
    have h : (Complex.normSq : ℂ → ℝ) = fun z => z.re * z.re + z.im * z.im := by
      funext w
      exact Complex.normSq_apply w
    rw [h]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hP : ContDiff ℝ ∞ (botP g) := by
    unfold botP
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hQ : ContDiff ℝ ∞ (botQ g) := by
    unfold botQ
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hinner : ContDiff ℝ ∞ (fun z => Complex.normSq (botP g z) + Complex.normSq (botQ g z)) :=
    (hnormSq.comp hP).add (hnormSq.comp hQ)
  rw [contDiff_iff_contDiffAt]
  intro z
  have hpos : Complex.normSq (botP g z) + Complex.normSq (botQ g z) ≠ 0 := by
    rw [← radC_sq_eq_normSq_add g z]
    exact (pow_pos (radC_pos_of_det_ne_zero hg z) 2).ne'
  have h := (Real.contDiffAt_sqrt hpos).comp z hinner.contDiffAt
  simp [radC, Function.comp_def] at h
  exact h

private theorem integrable_rpow_neg_radC_of_det_ne_zero (hg : g.det ≠ 0) {κ : ℝ} (hκ : 2 < κ) :
    Integrable (fun z => radC g z ^ (-κ)) (volume : Measure ℂ) := by
  have hA : (0:ℝ) < cplxBotNormSq g := cplxBotNormSq_pos hg
  have hB : (0:ℝ) < Complex.normSq g.det / cplxBotNormSq g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  set M : ℝ := min (cplxBotNormSq g) (Complex.normSq g.det / cplxBotNormSq g)
  have hM : (0:ℝ) < M := lt_min hA hB
  have hfinr : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < κ := by
    rw [Complex.finrank_real_complex]; exact_mod_cast hκ
  have hcmp : ∀ z : ℂ, radC g z ^ (-κ)
      ≤ M ^ (-κ/2) * ((1 : ℝ) + ‖z - cplxCenter g‖ ^ 2) ^ (-κ/2) := by
    intro z
    have hrad0 : 0 < radC g z := radC_pos_of_det_ne_zero hg z
    have hlb : M * (1 + ‖z - cplxCenter g‖ ^ 2) ≤ radC g z ^ 2 := by
      rw [radC_sq_eq_completedSquare hg z, Complex.normSq_eq_norm_sq]
      nlinarith [mul_le_mul_of_nonneg_right (min_le_left (cplxBotNormSq g)
          (Complex.normSq g.det / cplxBotNormSq g)) (sq_nonneg ‖z - cplxCenter g‖),
        min_le_right (cplxBotNormSq g) (Complex.normSq g.det / cplxBotNormSq g)]
    have hMn : 0 < M * (1 + ‖z - cplxCenter g‖ ^ 2) := mul_pos hM (by positivity)
    calc radC g z ^ (-κ) = (radC g z ^ 2) ^ (-κ/2) := by
          rw [← Real.rpow_natCast (radC g z) 2, ← Real.rpow_mul hrad0.le]; ring_nf
      _ ≤ (M * (1 + ‖z - cplxCenter g‖ ^ 2)) ^ (-κ/2) :=
          Real.rpow_le_rpow_of_nonpos hMn hlb (by linarith)
      _ = M ^ (-κ/2) * ((1 : ℝ) + ‖z - cplxCenter g‖ ^ 2) ^ (-κ/2) := by
          rw [Real.mul_rpow hM.le (by positivity)]
  have hint : Integrable
      (fun z : ℂ => M ^ (-κ/2) * ((1 : ℝ) + ‖z - cplxCenter g‖ ^ 2) ^ (-κ/2)) := by
    refine Integrable.const_mul ?_ _
    exact (integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) hfinr).comp_sub_right
      (cplxCenter g)
  exact hint.mono'
    ((contDiff_radC_of_det_ne_zero hg).continuous.rpow_const
      (fun z => Or.inl (radC_pos_of_det_ne_zero hg z).ne')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (radC_pos_of_det_ne_zero hg z).le _)]; exact hcmp z)

private theorem continuous_cpow_neg_radC (hg : g.det ≠ 0) (u : ℂ) :
    Continuous (fun z => ((radC g z : ℝ) : ℂ) ^ (-u)) :=
  (Complex.continuous_ofReal.comp (contDiff_radC_of_det_ne_zero hg).continuous).cpow continuous_const
    fun z => Complex.ofReal_mem_slitPlane.2 (radC_pos_of_det_ne_zero hg z)

end CplxRad
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section RealRad

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

private def realBotNormSq (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := g 1 0 ^ 2 + g 1 1 ^ 2

private def realFoot (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := -(g 0 0 * g 1 0 + g 0 1 * g 1 1) / realBotNormSq g

private def realRad (g : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : ℝ :=
  Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2)

private theorem realBotNormSq_pos (hg : g.det ≠ 0) : 0 < realBotNormSq g := by
  rw [realBotNormSq]
  rcases (add_nonneg (sq_nonneg (g 1 0)) (sq_nonneg (g 1 1))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hc : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have hd : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    apply hg
    rw [Matrix.det_fin_two, hc, hd, mul_zero, mul_zero, sub_zero]

private theorem realRadSq_eq_completedSquare (hg : g.det ≠ 0) (x : ℝ) :
    (g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2
      = realBotNormSq g * (x - realFoot g) ^ 2 + g.det ^ 2 / realBotNormSq g := by
  have hA : realBotNormSq g ≠ 0 := (realBotNormSq_pos hg).ne'
  rw [realFoot, Matrix.det_fin_two]
  unfold realBotNormSq at hA ⊢
  field_simp
  ring

private theorem realRad_pos_of_det_ne_zero (hg : g.det ≠ 0) (x : ℝ) : 0 < realRad g x := by
  rw [realRad, realRadSq_eq_completedSquare hg x]
  apply Real.sqrt_pos.2
  have hA : 0 < realBotNormSq g := realBotNormSq_pos hg
  have h1 : 0 ≤ realBotNormSq g * (x - realFoot g) ^ 2 := mul_nonneg hA.le (sq_nonneg _)
  have h2 : 0 < g.det ^ 2 / realBotNormSq g := div_pos (by positivity) hA
  linarith

private theorem continuous_realRad (g : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (realRad g) := by
  unfold realRad
  exact Real.continuous_sqrt.comp (by fun_prop)

private theorem integrable_rpow_neg_realRad_of_det_ne_zero (hg : g.det ≠ 0) {κ : ℝ} (hκ : 1 < κ) :
    Integrable (fun x => realRad g x ^ (-κ)) (volume : Measure ℝ) := by
  have hA : (0:ℝ) < realBotNormSq g := realBotNormSq_pos hg
  have hB : (0:ℝ) < g.det ^ 2 / realBotNormSq g := div_pos (by positivity) hA
  set M : ℝ := min (realBotNormSq g) (g.det ^ 2 / realBotNormSq g)
  have hM : (0:ℝ) < M := lt_min hA hB
  have hfinr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < κ := by
    rw [Module.finrank_self]; exact_mod_cast hκ
  have hcmp : ∀ x : ℝ, realRad g x ^ (-κ)
      ≤ M ^ (-κ/2) * ((1 : ℝ) + ‖x - realFoot g‖ ^ 2) ^ (-κ/2) := by
    intro x
    have hrad0 : 0 < realRad g x := realRad_pos_of_det_ne_zero hg x
    have hsq : realRad g x ^ 2 = realBotNormSq g * (x - realFoot g) ^ 2 + g.det ^ 2 / realBotNormSq g := by
      rw [realRad, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), realRadSq_eq_completedSquare hg x]
    have hlb : M * (1 + ‖x - realFoot g‖ ^ 2) ≤ realRad g x ^ 2 := by
      rw [hsq, Real.norm_eq_abs, sq_abs]
      nlinarith [mul_le_mul_of_nonneg_right (min_le_left (realBotNormSq g)
          (g.det ^ 2 / realBotNormSq g)) (sq_nonneg (x - realFoot g)),
        min_le_right (realBotNormSq g) (g.det ^ 2 / realBotNormSq g)]
    have hMn : 0 < M * (1 + ‖x - realFoot g‖ ^ 2) := mul_pos hM (by positivity)
    calc realRad g x ^ (-κ) = (realRad g x ^ 2) ^ (-κ/2) := by
          rw [← Real.rpow_natCast (realRad g x) 2, ← Real.rpow_mul hrad0.le]; ring_nf
      _ ≤ (M * (1 + ‖x - realFoot g‖ ^ 2)) ^ (-κ/2) :=
          Real.rpow_le_rpow_of_nonpos hMn hlb (by linarith)
      _ = M ^ (-κ/2) * ((1 : ℝ) + ‖x - realFoot g‖ ^ 2) ^ (-κ/2) := by
          rw [Real.mul_rpow hM.le (by positivity)]
  have hint : Integrable
      (fun x : ℝ => M ^ (-κ/2) * ((1 : ℝ) + ‖x - realFoot g‖ ^ 2) ^ (-κ/2)) := by
    refine Integrable.const_mul ?_ _
    exact (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hfinr).comp_sub_right
      (realFoot g)
  exact hint.mono'
    ((continuous_realRad g).rpow_const
      (fun x => Or.inl (realRad_pos_of_det_ne_zero hg x).ne')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (realRad_pos_of_det_ne_zero hg x).le _)]; exact hcmp x)

end RealRad
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section IntegrableSlices

private theorem integrable_cpow_neg_radC_mul {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) {u : ℂ} (hu : 2 < u.re)
    (P : ℂ → ℂ) (hPc : Continuous P) (hPb : ∃ B, ∀ z, ‖P z‖ ≤ B) :
    Integrable (fun z => ((AutomorphicForm.ComplexIwasawa.radC g z : ℝ) : ℂ) ^ (-u) * P z) (volume : Measure ℂ) := by
  obtain ⟨B, hB⟩ := hPb
  have hint := (integrable_rpow_neg_radC_of_det_ne_zero hg hu).mul_const (max B 0)
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact ((continuous_cpow_neg_radC hg u).mul hPc).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (radC_pos_of_det_ne_zero hg z), Complex.neg_re]
    exact mul_le_mul_of_nonneg_left ((hB z).trans (le_max_left _ _))
      (Real.rpow_nonneg (radC_pos_of_det_ne_zero hg z).le _)

private theorem integrable_cpow_neg_sqrt_mul {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {u : ℂ} (hu : 1 < u.re)
    (P : ℝ → ℂ) (hPc : Continuous P) (hPb : ∃ B, ∀ x, ‖P x‖ ≤ B) :
    Integrable (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℝ) : ℂ) ^ (-u) * P x)
      (volume : Measure ℝ) := by
  obtain ⟨B, hB⟩ := hPb
  change Integrable (fun x => ((realRad g x : ℝ) : ℂ) ^ (-u) * P x) (volume : Measure ℝ)
  have hint := (integrable_rpow_neg_realRad_of_det_ne_zero hg hu).mul_const (max B 0)
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (Continuous.mul ?_ hPc).aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp (continuous_realRad g)).cpow continuous_const
      fun x => Complex.ofReal_mem_slitPlane.2 (realRad_pos_of_det_ne_zero hg x)
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (realRad_pos_of_det_ne_zero hg x), Complex.neg_re]
    exact mul_le_mul_of_nonneg_left ((hB x).trans (le_max_left _ _))
      (Real.rpow_nonneg (realRad_pos_of_det_ne_zero hg x).le _)

end IntegrableSlices
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"
end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

noncomputable section
namespace WeylUnipotentDecay

section KernelBounds

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped FourierTransform ComplexConjugate

attribute [local instance] InfiniteAdeleHaar.placeBorel

private theorem pairingC_coercive (ξ : ℂ) : ∃ v : ℂ, ‖v‖ ≤ 1 ∧ 1 * ‖ξ‖ ≤ ‖pairingC v ξ‖ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · exact ⟨0, by simp, by simp⟩
  · refine ⟨ξ / ‖ξ‖, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, norm_norm]
      exact (div_self (norm_ne_zero_iff.mpr hξ)).le
    · have hξn : (‖ξ‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hξ
      have heval : pairingC (ξ / ‖ξ‖) ξ = ξ.re * ξ.re / ‖ξ‖ + ξ.im * ξ.im / ‖ξ‖ := by
        rw [pairingC_apply, Complex.div_ofReal_re, Complex.div_ofReal_im]
        ring
      rw [one_mul, heval, Real.norm_eq_abs, ← add_div, ← Complex.normSq_apply,
        Complex.normSq_eq_norm_sq, sq, abs_div,
        abs_of_nonneg (mul_self_nonneg _), abs_of_nonneg (norm_nonneg _),
        mul_div_assoc, div_self hξn, mul_one]

private theorem pairingR_coercive (ξ : ℝ) : ∃ v : ℝ, ‖v‖ ≤ 1 ∧ 1 * ‖ξ‖ ≤ ‖pairingR v ξ‖ :=
  ⟨1, by simp, by simp [pairingR_apply]⟩

variable (F : Type) [Field F]

private theorem placeMeasure_of_isComplex {w : InfinitePlace F} (hw : w.IsComplex) :
    InfiniteAdeleHaar.placeMeasure F w = (volume : Measure ℂ).map (ringEquivComplexOfIsComplex hw).symm := by
  rw [InfiniteAdeleHaar.placeMeasure, dif_neg (not_isReal_iff_isComplex.mpr hw)]; rfl

private theorem placeMeasure_of_isReal {w : InfinitePlace F} (hw : w.IsReal) :
    InfiniteAdeleHaar.placeMeasure F w = (volume : Measure ℝ).map (ringEquivRealOfIsReal hw).symm := by
  rw [InfiniteAdeleHaar.placeMeasure, dif_pos hw]; rfl

private theorem integral_phaseAt_mul_eq_fourierIntegral_of_isComplex {w : InfinitePlace F} (hw : w.IsComplex)
    (c : w.Completion) (G : ℂ → ℂ) :
    ∫ y, phaseAt F w (c * y) * G (ringEquivComplexOfIsComplex hw y) ∂(InfiniteAdeleHaar.placeMeasure F w)
      = VectorFourier.fourierIntegral 𝐞 (volume : Measure ℂ) pairingC.toLinearMap₁₂ G
          ((-2 : ℝ) • conj (ringEquivComplexOfIsComplex hw c)) := by
  rw [placeMeasure_of_isComplex F hw, integral_volume_map_ringEquivComplexOfIsComplex_symm hw]
  unfold VectorFourier.fourierIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have key : extensionEmbedding w ((ringEquivComplexOfIsComplex hw).symm z) = z :=
    (ringEquivComplexOfIsComplex hw).apply_symm_apply z
  simp only [phaseAt_of_isComplex F hw, map_mul, key, RingEquiv.apply_symm_apply, fourierChar_two_mul_re_mul,
    Circle.smul_def, smul_eq_mul, ContinuousLinearMap.toLinearMap₁₂_apply, ringEquivComplexOfIsComplex_apply,
    LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coeLMₛₗ_apply, ContinuousLinearMap.coe_coe]

private theorem integral_phaseAt_mul_eq_fourierIntegral_of_isReal {w : InfinitePlace F} (hw : w.IsReal)
    (c : w.Completion) (G : ℝ → ℂ) :
    ∫ y, phaseAt F w (c * y) * G (ringEquivRealOfIsReal hw y) ∂(InfiniteAdeleHaar.placeMeasure F w)
      = VectorFourier.fourierIntegral 𝐞 (volume : Measure ℝ) pairingR.toLinearMap₁₂ G
          (-(ringEquivRealOfIsReal hw c)) := by
  rw [placeMeasure_of_isReal F hw, integral_volume_map_ringEquivRealOfIsReal_symm hw]
  unfold VectorFourier.fourierIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have key : extensionEmbeddingOfIsReal hw ((ringEquivRealOfIsReal hw).symm x) = x :=
    (ringEquivRealOfIsReal hw).apply_symm_apply x
  simp only [phaseAt_of_isReal F hw, map_mul, key, RingEquiv.apply_symm_apply, fourierChar_mul,
    Circle.smul_def, smul_eq_mul, ContinuousLinearMap.toLinearMap₁₂_apply, ringEquivRealOfIsReal_apply,
    LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coeLMₛₗ_apply, ContinuousLinearMap.coe_coe]

end KernelBounds
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section MainAssembly

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped FourierTransform ComplexConjugate

attribute [local instance] InfiniteAdeleHaar.placeBorel

variable (F : Type) [Field F]

variable [NumberField F] in
private theorem addChar_arch_eq_prod_phaseAt (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {a : F} (ha : a ≠ 0)
    (hψarch : ∀ x : InfiniteAdeleRing F, ψ (algebraMap F (InfiniteAdeleRing F) a * x, 0)
      = ((𝐞 (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : Circle) : ℂ))
    {n : ℕ} (e : Fin n ≃ InfinitePlace F) (ξ : F) (y : InfiniteAdeleRing F) :
    ψ (adeleOf F (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).1 * y)) 0)
      = ∏ i, phaseAt F (e i) (algebraMap F (e i).Completion (-(ξ / a)) * y (e i)) := by
  have hx : adeleOf F (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).1 * y)) 0
      = adeleOf F (algebraMap F (InfiniteAdeleRing F) a * (algebraMap F (InfiniteAdeleRing F) (-(ξ / a)) * y)) 0 := by
    congr 1
    have h1 : (algebraMap F (AdeleRing (𝓞 F) F) ξ).1 = algebraMap F (InfiniteAdeleRing F) ξ := rfl
    have h2 : a * (-(ξ / a)) = -ξ := by field_simp
    rw [h1, ← mul_assoc, ← map_mul, h2, map_neg, neg_mul]
  have h3 := hψarch (algebraMap F (InfiniteAdeleRing F) (-(ξ / a)) * y)
  rw [hx]
  refine (h3 : ψ (adeleOf F _ 0) = _).trans ?_
  rw [fourierChar_trace_ringEquiv_mixedSpace_eq_prod_phaseAt]
  refine (Fintype.prod_equiv e _ _ fun i => ?_).symm
  rfl

open scoped Classical in

private def freqScale (a : F) (w : InfinitePlace F) : ℝ := if w.IsReal then (w a)⁻¹ else 2 * (w a)⁻¹

private theorem freqScale_pos {a : F} (ha : a ≠ 0) (w : InfinitePlace F) : 0 < freqScale F a w := by
  unfold freqScale
  have hwa : 0 < w a := InfinitePlace.pos_iff.2 ha
  split_ifs
  · exact inv_pos.2 hwa
  · exact mul_pos two_pos (inv_pos.2 hwa)

private theorem algebraMap_completion_eq_coe (w : InfinitePlace F) (x : F) :
    algebraMap F w.Completion x = (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.Completion) := rfl

private theorem norm_freq_of_isReal {w : InfinitePlace F} (hv : w.IsReal) (a ξ : F) :
    ‖-(ringEquivRealOfIsReal hv (algebraMap F w.Completion (-(ξ / a))))‖ = freqScale F a w * w ξ := by
  rw [norm_neg, map_neg, map_neg, norm_neg, ringEquivRealOfIsReal_apply, algebraMap_completion_eq_coe,
    extensionEmbeddingOfIsReal_coe, norm_embedding_of_isReal, RingEquiv.apply_symm_apply, map_div₀, freqScale,
    if_pos hv, div_eq_inv_mul]

private theorem norm_freq_of_isComplex {w : InfinitePlace F} (hw : w.IsComplex) (a ξ : F) :
    ‖((-2 : ℝ) • conj (ringEquivComplexOfIsComplex hw (algebraMap F w.Completion (-(ξ / a)))) : ℂ)‖
      = freqScale F a w * w ξ := by
  rw [norm_freqC, map_neg, map_neg, norm_neg, ringEquivComplexOfIsComplex_apply, algebraMap_completion_eq_coe,
    extensionEmbedding_coe, norm_embedding_eq, RingEquiv.apply_symm_apply, map_div₀, freqScale,
    if_neg (not_isReal_iff_isComplex.mpr hw), div_eq_inv_mul, mul_assoc]

private theorem integrable_phaseAt_mul_of_isComplex {w : InfinitePlace F} (hw : w.IsComplex) (c : w.Completion)
    {G : ℂ → ℂ} (hG : Integrable G (volume : Measure ℂ)) :
    Integrable (fun y => phaseAt F w (c * y) * G (ringEquivComplexOfIsComplex hw y)) (InfiniteAdeleHaar.placeMeasure F w) := by
  rw [placeMeasure_of_isComplex F hw, integrable_volume_map_ringEquivComplexOfIsComplex_symm_iff hw]
  have key : ∀ z, extensionEmbedding w ((ringEquivComplexOfIsComplex hw).symm z) = z := fun z =>
    (ringEquivComplexOfIsComplex hw).apply_symm_apply z
  have h := (VectorFourier.fourierIntegral_convergent_iff (μ := (volume : Measure ℂ)) Real.continuous_fourierChar
    (L := pairingC.toLinearMap₁₂) pairingC.continuous₂ ((-2 : ℝ) • conj (extensionEmbedding w c))).2 hG
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [phaseAt_of_isComplex F hw, map_mul, key, RingEquiv.apply_symm_apply, fourierChar_two_mul_re_mul,
    Circle.smul_def, smul_eq_mul, ContinuousLinearMap.toLinearMap₁₂_apply,
    LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coeLMₛₗ_apply, ContinuousLinearMap.coe_coe]

private theorem integrable_phaseAt_mul_of_isReal {w : InfinitePlace F} (hw : w.IsReal) (c : w.Completion)
    {G : ℝ → ℂ} (hG : Integrable G (volume : Measure ℝ)) :
    Integrable (fun y => phaseAt F w (c * y) * G (ringEquivRealOfIsReal hw y)) (InfiniteAdeleHaar.placeMeasure F w) := by
  rw [placeMeasure_of_isReal F hw, integrable_volume_map_ringEquivRealOfIsReal_symm_iff hw]
  have key : ∀ x, extensionEmbeddingOfIsReal hw ((ringEquivRealOfIsReal hw).symm x) = x := fun x =>
    (ringEquivRealOfIsReal hw).apply_symm_apply x
  have h := (VectorFourier.fourierIntegral_convergent_iff (μ := (volume : Measure ℝ)) Real.continuous_fourierChar
    (L := pairingR.toLinearMap₁₂) pairingR.continuous₂ (-(extensionEmbeddingOfIsReal hw c))).2 hG
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [phaseAt_of_isReal F hw, map_mul, key, RingEquiv.apply_symm_apply, fourierChar_mul,
    Circle.smul_def, smul_eq_mul, ContinuousLinearMap.toLinearMap₁₂_apply,
    LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coeLMₛₗ_apply, ContinuousLinearMap.coe_coe]

private theorem integrable_fintype_prod_comp_equiv {𝕜 ι ι' : Type*} [Fintype ι] [Fintype ι'] [RCLike 𝕜] (e : ι' ≃ ι)
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)]
    {f : ∀ i' : ι', E (e i') → 𝕜} (hf : ∀ i', Integrable (f i') (μ (e i'))) :
    Integrable (fun x : (i : ι) → E i => ∏ i', f i' (x (e i'))) (Measure.pi μ) := by
  refine ((measurePreserving_piCongrLeft μ e).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 ?_
  have hcomp : ((fun x : (i : ι) → E i => ∏ i', f i' (x (e i'))) ∘ (MeasurableEquiv.piCongrLeft E e))
      = fun x' => ∏ i', f i' (x' i') := by
    funext x'
    simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [hcomp]
  exact Integrable.fintype_prod_dep hf

end MainAssembly
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"
end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

section FubiniHelpers
p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm IsDedekindDomain"

variable (F : Type) [Field F] [NumberField F]

namespace WeylUnipotentDecay

private theorem adeleOf_eq_add (y : InfiniteAdeleRing F) (t : FiniteAdeleRing (𝓞 F) F) :
    (adeleOf F y t : AdeleRing (𝓞 F) F) = adeleOf F y 0 + adeleOf F 0 t :=
  Prod.ext (add_zero y).symm (zero_add t).symm

private theorem algebraMap_adeleRing_mul_split (ξ : F) (y : InfiniteAdeleRing F)
    (t : FiniteAdeleRing (𝓞 F) F) :
    algebraMap F (AdeleRing (𝓞 F) F) ξ * adeleOf F y t
      = adeleOf F ((algebraMap F (AdeleRing (𝓞 F) F) ξ).1 * y)
          ((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t) := rfl

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end FubiniHelpers
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

private theorem WeylUnipotentDecay.continuous_const_mul_mul_const {G : Type*} [TopologicalSpace G] [Mul G]
    [ContinuousMul G] (a b : G) : Continuous fun x => a * x * b :=
  (continuous_const.mul continuous_id).mul continuous_const

namespace WeylUnipotentDecay

open scoped Matrix

private theorem realRadSq_pos {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (x : ℝ) :
    0 < (g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2 := by
  rcases (add_nonneg (sq_nonneg (g 0 0 + x * g 1 0))
    (sq_nonneg (g 0 1 + x * g 1 1))).lt_or_eq with h | h
  · exact h
  · exfalso
    have ha : g 0 0 + x * g 1 0 = 0 := by
      nlinarith [sq_nonneg (g 0 0 + x * g 1 0), sq_nonneg (g 0 1 + x * g 1 1)]
    have hb : g 0 1 + x * g 1 1 = 0 := by
      nlinarith [sq_nonneg (g 0 0 + x * g 1 0), sq_nonneg (g 0 1 + x * g 1 1)]
    apply hg
    rw [Matrix.det_fin_two]
    linear_combination g 1 1 * ha - g 1 0 * hb

private theorem rotBlock_mul_transpose (a b : ℝ) :
    (!![b, -a; a, b] : Matrix (Fin 2) (Fin 2) ℝ)
      * (!![b, -a; a, b] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ
      = (a ^ 2 + b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

private theorem realIwasawaK_mem_orthogonalGroup {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    (x : ℝ) : realIwasawaK g x ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  have hr2 := realRadSq_pos hg x
  set S := (g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2 with hS
  have hr : Real.sqrt S ≠ 0 := (Real.sqrt_pos.mpr hr2).ne'
  have hsq := Real.sq_sqrt hr2.le
  rw [Matrix.mem_orthogonalGroup_iff]
  unfold realIwasawaK
  rw [← hS, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    rotBlock_mul_transpose, smul_smul]
  have hkey : (Real.sqrt S)⁻¹ * (Real.sqrt S)⁻¹ * S = 1 := by
    rw [← mul_inv, ← sq, hsq, inv_mul_cancel₀ hr2.ne']
  rw [← hS, hkey, one_smul]

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

namespace WeylUnipotentDecay

section ArchChar

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm"

open scoped Classical in

private theorem archChar_factorization (F : Type) [Field F] [NumberField F]
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hαL : α = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μc νc : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμc : IsUnitaryChar (𝓞 F) F μc) (hνc : IsUnitaryChar (𝓞 F) F νc)
    (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μc α hα s) (etaSnd νc α hα s) φ) (hφc : Continuous φ)
    (hφ0 : ¬ ∀ x, φ x = 0)
    {nW : ℕ} (eW : Fin nW ≃ InfinitePlace F) (gwW : ∀ i, GL (Fin 2) (eW i).Completion)
    (gwR : ∀ i, (eW i).IsReal → Matrix (Fin 2) (Fin 2) ℝ)
    (hgwR : ∀ i (hv : (eW i).IsReal), ((WeylUnipotentDecay.glMapRingEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) (gwW i) : GL (Fin 2) ℝ)
        : Matrix (Fin 2) (Fin 2) ℝ) = gwR i hv)
    (gwC : ∀ i, (eW i).IsComplex → Matrix (Fin 2) (Fin 2) ℂ)
    (hgwC : ∀ i (hw : (eW i).IsComplex), ((WeylUnipotentDecay.glMapRingEquiv
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (gwW i) : GL (Fin 2) ℂ)
        : Matrix (Fin 2) (Fin 2) ℂ) = gwC i hw)
    (kRI : InfiniteAdeleRing F → ∀ i, GL (Fin 2) (eW i).Completion)
    (hkR : ∀ (y : InfiniteAdeleRing F) i (hv : (eW i).IsReal), ((WeylUnipotentDecay.glMapRingEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) (kRI y i) : GL (Fin 2) ℝ)
        : Matrix (Fin 2) (Fin 2) ℝ)
      = WeylUnipotentDecay.realIwasawaK (gwR i hv)
        ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) (y (eW i))))
    (hkC : ∀ (y : InfiniteAdeleRing F) i (hw : (eW i).IsComplex), ((WeylUnipotentDecay.glMapRingEquiv
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (kRI y i) : GL (Fin 2) ℂ)
        : Matrix (Fin 2) (Fin 2) ℂ)
      = AutomorphicForm.ComplexIwasawa.kC (gwC i hw)
        ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (y (eW i))))
    (radW : InfiniteAdeleRing F → Fin nW → ℝ)
    (hradR : ∀ y i (hv : (eW i).IsReal), radW y i =
      Real.sqrt ((gwR i hv 0 0
            + NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv (y (eW i)) * gwR i hv 1 0) ^ 2
          + (gwR i hv 0 1
            + NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv (y (eW i)) * gwR i hv 1 1) ^ 2))
    (hradC : ∀ y i (hw : (eW i).IsComplex), radW y i =
      AutomorphicForm.ComplexIwasawa.radC (gwC i hw)
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw (y (eW i))))
    (hrad : ∀ y i, 0 < radW y i)
    (bW : InfiniteAdeleRing F → ∀ i, GL (Fin 2) (eW i).Completion)
    (hbW : ∀ y i, bW y i = gl2Weyl * unipotentGL2 (y (eW i)) * gwW i * (kRI y i)⁻¹)
    (hmem : ∀ y, (List.ofFn fun i => adelicArchGLInclAt F (eW i) (bW y i)).prod
      ∈ adelicBorel (𝓞 F) F) :
    ∃ (tW : Fin nW → ℝ) (K₀ : ℂ), ∀ y : InfiniteAdeleRing F,
      ((μc (borelDiagFst (⟨_, hmem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((νc (borelDiagSnd (⟨_, hmem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
      = K₀ * ∏ i, ((radW y i : ℝ) : ℂ) ^ ((tW i : ℂ) * Complex.I) := by

  obtain ⟨emb, hemb_def⟩ : ∃ emb : ∀ i, ℝ →+* (eW i).Completion, ∀ i, emb i =
      if hv : (eW i).IsReal then (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toRingHom
      else ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv)).symm.toRingHom.comp Complex.ofRealHom) :=
    ⟨_, fun _ => rfl⟩
  have hemb_R : ∀ i (hv : (eW i).IsReal) (r : ℝ), emb i r = (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r := fun i hv r => by
    rw [hemb_def, dif_pos hv]; rfl
  have hemb_C : ∀ i (hw : (eW i).IsComplex) (r : ℝ), emb i r = (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm (r : ℂ) := fun i hw r => by
    rw [hemb_def, dif_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw)]; rfl

  have hbW_val : ∀ y i,
      ((bW y i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 0 0 * emb i (radW y i)
          = ((bW 0 i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 0 0 * emb i (radW 0 i)
      ∧ ((bW y i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 1 1 = emb i (radW y i) := by
    intro y i
    have hr : ∀ y' : InfiniteAdeleRing F, radW y' i ≠ 0 := fun y' => (hrad y' i).ne'
    by_cases hv : (eW i).IsReal
    · have hv00 : ∀ y' : InfiniteAdeleRing F, ((bW y' i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 0 0
          = (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm (-(gwR i hv).det / radW y' i) := fun y' => by
        rw [hbW]
        have h := (WeylUnipotentDecay.placeValues_real (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) (gwW i) (kRI y' i) (y' (eW i))
          (gwR i hv) (hgwR i hv) (hkR y' i hv)).1
        rw [← hradR y' i hv] at h
        exact h
      have hv11 : ((bW y i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 1 1 = (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm (radW y i) := by
        rw [hbW]
        have h := (WeylUnipotentDecay.placeValues_real (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) (gwW i) (kRI y i) (y (eW i))
          (gwR i hv) (hgwR i hv) (hkR y i hv)).2
        rw [← hradR y i hv] at h
        exact h
      refine ⟨?_, ?_⟩
      · rw [hv00 y, hv00 0, hemb_R i hv, hemb_R i hv, ← map_mul, ← map_mul, div_mul_cancel₀ _ (hr y),
          div_mul_cancel₀ _ (hr 0)]
      · rw [hv11, hemb_R i hv]
    · have hw : (eW i).IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
      have hv00 : ∀ y' : InfiniteAdeleRing F, ((bW y' i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 0 0
          = (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm (-(gwC i hw).det / ((radW y' i : ℝ) : ℂ)) := fun y' => by
        rw [hbW]
        have h := (WeylUnipotentDecay.placeValues_complex (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (gwW i) (kRI y' i) (y' (eW i))
          (gwC i hw) (hgwC i hw) (hkC y' i hw)).1
        rw [← hradC y' i hw] at h
        exact h
      have hv11 : ((bW y i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 1 1 = (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm ((radW y i : ℝ) : ℂ) := by
        rw [hbW]
        have h := (WeylUnipotentDecay.placeValues_complex (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (gwW i) (kRI y i) (y (eW i))
          (gwC i hw) (hgwC i hw) (hkC y i hw)).2
        rw [← hradC y i hw] at h
        exact h
      have hrC : ∀ y' : InfiniteAdeleRing F, ((radW y' i : ℝ) : ℂ) ≠ 0 := fun y' =>
        Complex.ofReal_ne_zero.mpr (hr y')
      refine ⟨?_, ?_⟩
      · rw [hv00 y, hv00 0, hemb_C i hw, hemb_C i hw, ← map_mul, ← map_mul, div_mul_cancel₀ _ (hrC y),
          div_mul_cancel₀ _ (hrC 0)]
      · rw [hv11, hemb_C i hw]

  obtain ⟨μ', hμ'⟩ : ∃ μ' : (AdeleRing (𝓞 F) F)ˣ →* ℂ, ∀ x, μ' x = ((μc x : ℂˣ) : ℂ) :=
    ⟨(Units.coeHom ℂ).comp μc, fun _ => rfl⟩
  obtain ⟨ν', hν'⟩ : ∃ ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂ, ∀ x, ν' x = ((νc x : ℂˣ) : ℂ) :=
    ⟨(Units.coeHom ℂ).comp νc, fun _ => rfl⟩
  have hemb0 : ∀ i (r : ℝ), r ≠ 0 → emb i r ≠ 0 := fun i r hr0 => (map_ne_zero (emb i)).mpr hr0
  obtain ⟨rU, hrU_def⟩ : ∃ rU : ℝ → ∀ i, ((eW i).Completion)ˣ, ∀ r i, rU r i =
      if hr0 : r = 0 then 1 else Units.mk0 (emb i r) (hemb0 i r hr0) := ⟨_, fun _ _ => rfl⟩
  have hrU : ∀ (r : ℝ) i, r ≠ 0 → ((rU r i : ((eW i).Completion)ˣ) : (eW i).Completion) = emb i r :=
    fun r i hr0 => by rw [hrU_def, dif_neg hr0, Units.val_mk0]
  have hrU_mul : ∀ (a b : ℝ) i, a ≠ 0 → b ≠ 0 → rU (a * b) i = rU a i * rU b i := fun a b i ha hb =>
    Units.ext (by rw [Units.val_mul, hrU _ _ (mul_ne_zero ha hb), hrU _ _ ha, hrU _ _ hb, map_mul])

  obtain ⟨χpl, hχpl⟩ : ∃ χpl : ∀ i, ℝ → ℂ, ∀ i r,
      χpl i r = ν' (WeylUnipotentDecay.ideleAt F (eW i) (rU r i)) * (μ' (WeylUnipotentDecay.ideleAt F (eW i) (rU r i)))⁻¹ := ⟨_, fun _ _ => rfl⟩
  have hχpl_mul : ∀ i (a b : ℝ), 0 < a → 0 < b → χpl i (a * b) = χpl i a * χpl i b := by
    intro i a b ha hb
    rw [hχpl, hχpl, hχpl, hrU_mul a b i ha.ne' hb.ne', WeylUnipotentDecay.ideleAt_mul]
    simp only [map_mul, mul_inv]
    ring
  have hχpl_norm : ∀ i (r : ℝ), 0 < r → ‖χpl i r‖ = 1 := by
    intro i r _
    rw [hχpl, norm_mul, norm_inv, hν', hμ', hνc, hμc, inv_one, mul_one]
  have hχpl_cont : ∀ i, ContinuousOn (χpl i) (Set.Ioi 0) := by
    intro i
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, φ g₀ ≠ 0 := not_forall.mp hφ0
    have hexp0 : ∀ u : ℝ, Real.exp u ≠ 0 := fun u => (Real.exp_pos u).ne'

    have hemb_norm : ∀ r : ℝ, ‖emb i r‖ = ‖r‖ := by
      intro r
      by_cases hv : (eW i).IsReal
      · rw [hemb_R i hv]
        have h := WeylUnipotentDecay.norm_ringEquivRealOfIsReal hv ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r)
        rw [RingEquiv.apply_symm_apply] at h
        exact h.symm
      · have hw : (eW i).IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
        rw [hemb_C i hw]
        have h := WeylUnipotentDecay.norm_ringEquivComplexOfIsComplex hw ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm (r : ℂ))
        rw [RingEquiv.apply_symm_apply, Complex.norm_real] at h
        exact h.symm
    have hemb_cont : Continuous (emb i) :=
      AddMonoidHomClass.continuous_of_bound (emb i) 1 fun r => by rw [hemb_norm, one_mul]

    have hval : ∀ u : ℝ, ((WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i)) : AdeleRing (𝓞 F) F)
        = ((Pi.mulSingle (eW i) (emb i (Real.exp u)) : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) :=
      fun u => by rw [WeylUnipotentDecay.val_ideleAt, hrU _ _ (hexp0 u)]
    have hinv : ∀ u : ℝ, (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i))⁻¹ = WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp (-u)) i) := fun u => by
      rw [← WeylUnipotentDecay.ideleAt_inv]
      congr 1
      ext
      rw [Units.val_inv_eq_inv_val, hrU _ _ (hexp0 u), hrU _ _ (hexp0 (-u)), Real.exp_neg, map_inv₀]
    have hcval : Continuous fun u : ℝ => ((WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i)) : AdeleRing (𝓞 F) F) := by
      rw [show (fun u : ℝ => ((WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i)) : AdeleRing (𝓞 F) F)) = fun u =>
          ((Pi.mulSingle (eW i) (emb i (Real.exp u)) : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
        from funext hval]
      exact ((continuous_mulSingle (eW i)).comp (hemb_cont.comp Real.continuous_exp)).prodMk continuous_const
    have hcinv : Continuous fun u : ℝ => (((WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
      rw [show (fun u : ℝ => (((WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) = fun u =>
          ((Pi.mulSingle (eW i) (emb i (Real.exp (-u))) : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
        from funext fun u => by rw [hinv u, hval (-u)]]
      exact ((continuous_mulSingle (eW i)).comp
        (hemb_cont.comp (Real.continuous_exp.comp continuous_neg))).prodMk continuous_const

    have hBcont : Continuous fun u : ℝ => φ (WeylUnipotentDecay.diagGL2 F (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i))⁻¹ (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i)) * g₀) :=
      hφc.comp ((WeylUnipotentDecay.continuous_diagGL2 F hcinv (by simpa only [inv_inv] using hcval) hcval
        hcinv).mul continuous_const)

    have hlaw : ∀ u : ℝ, φ (WeylUnipotentDecay.diagGL2 F (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i))⁻¹ (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i)) * g₀)
        = ((etaFst μc α hα s (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i))⁻¹ : ℂˣ) : ℂ) * ((etaSnd νc α hα s (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i)) : ℂˣ) : ℂ) * φ g₀ := fun u => by
      rw [hφ _ (WeylUnipotentDecay.diagGL2_mem F _ _) g₀, WeylUnipotentDecay.borelDiagFst_diagGL2,
        WeylUnipotentDecay.borelDiagSnd_diagGL2]
    have hpos : ∀ u : ℝ, 0 < Real.exp u ^ (eW i).mult := fun u => pow_pos (Real.exp_pos u) _
    have hmodA : ∀ u : ℝ, ((α (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i)) : ℝˣ) : ℝ) = Real.exp u ^ (eW i).mult := fun u => by
      rw [hαL]
      show ((distribHaarChar (AdeleRing (𝓞 F) F) (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i)) : ℝ≥0) : ℝ) = _
      rw [WeylUnipotentDecay.distribHaarChar_ideleAt, hrU _ _ (hexp0 u), hemb_norm, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos u)]
    have hmodA' : ∀ u : ℝ, ((α (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i))⁻¹ : ℝˣ) : ℝ) = (Real.exp u ^ (eW i).mult)⁻¹ := fun u => by
      rw [map_inv, Units.val_inv_eq_inv_val, hmodA]
    have heta : ∀ u : ℝ, ((etaFst μc α hα s (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i))⁻¹ : ℂˣ) : ℂ) * ((etaSnd νc α hα s (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i)) : ℂˣ) : ℂ)
        = χpl i (Real.exp u) * ((((Real.exp u ^ (eW i).mult)⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2) * (((Real.exp u ^ (eW i).mult : ℝ)) : ℂ) ^ (-(s + 1 / 2))) := fun u => by
      rw [etaFst_apply, etaSnd_apply, Units.val_mul, Units.val_mul, cpowChar_apply_val, cpowChar_apply_val,
        hmodA, hmodA', hχpl, map_inv, Units.val_inv_eq_inv_val, ← hμ', ← hν']
      ring
    have hfac_cont : Continuous fun u : ℝ => ((((Real.exp u ^ (eW i).mult)⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2) * (((Real.exp u ^ (eW i).mult : ℝ)) : ℂ) ^ (-(s + 1 / 2))) := by
      refine Continuous.mul ?_ ?_
      · exact Continuous.cpow (Complex.continuous_ofReal.comp
            ((Real.continuous_exp.pow _).inv₀ fun u => (hpos u).ne')) continuous_const
          fun u => Or.inl (by rw [Complex.ofReal_re]; exact inv_pos.2 (hpos u))
      · exact Continuous.cpow (Complex.continuous_ofReal.comp (Real.continuous_exp.pow _)) continuous_const
          fun u => Or.inl (by rw [Complex.ofReal_re]; exact hpos u)
    have hfac_ne : ∀ u : ℝ, ((((Real.exp u ^ (eW i).mult)⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2) * (((Real.exp u ^ (eW i).mult : ℝ)) : ℂ) ^ (-(s + 1 / 2))) ≠ 0 := fun u =>
      mul_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (inv_ne_zero (hpos u).ne'))))
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (hpos u).ne')))

    have hχexp : Continuous fun u : ℝ => χpl i (Real.exp u) := by
      rw [show (fun u : ℝ => χpl i (Real.exp u)) = fun u =>
          φ (WeylUnipotentDecay.diagGL2 F (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i))⁻¹ (WeylUnipotentDecay.ideleAt F (eW i) (rU (Real.exp u) i)) * g₀) / (φ g₀ * ((((Real.exp u ^ (eW i).mult)⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2) * (((Real.exp u ^ (eW i).mult : ℝ)) : ℂ) ^ (-(s + 1 / 2))))
        from funext fun u => by
          rw [hlaw, heta, eq_div_iff (mul_ne_zero hg₀ (hfac_ne u))]
          ring]
      exact hBcont.div (continuous_const.mul hfac_cont) fun u => mul_ne_zero hg₀ (hfac_ne u)
    exact (hχexp.comp_continuousOn (Real.continuousOn_log.mono fun r hr => hr.ne')).congr
      fun r hr => show χpl i r = χpl i (Real.exp (Real.log r)) by rw [Real.exp_log hr]
  choose tW htW using fun i =>
    WeylUnipotentDecay.exists_forall_eq_cpow_of_continuousOn_of_norm_eq_one (hχpl_cont i) (hχpl_mul i) (hχpl_norm i)

  have haSnd : ∀ y, (((borelDiagFst (⟨_, hmem y⟩ : ↥(adelicBorel (𝓞 F) F))) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := fun y =>
    WeylUnipotentDecay.borelDiagFst_prod_val_snd F eW (bW y) (hmem y)
  have hdSnd : ∀ y, (((borelDiagSnd (⟨_, hmem y⟩ : ↥(adelicBorel (𝓞 F) F))) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := fun y =>
    WeylUnipotentDecay.borelDiagSnd_prod_val_snd F eW (bW y) (hmem y)
  have haU : ∀ y i, ((WeylUnipotentDecay.archUnits F (borelDiagFst (⟨_, hmem y⟩ : ↥(adelicBorel (𝓞 F) F))) (eW i) : ((eW i).Completion)ˣ) : (eW i).Completion)
      = ((bW y i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 0 0 := fun y i =>
    WeylUnipotentDecay.borelDiagFst_prod_val_fst_apply F eW (bW y) (hmem y) i
  have hdU : ∀ y i, ((WeylUnipotentDecay.archUnits F (borelDiagSnd (⟨_, hmem y⟩ : ↥(adelicBorel (𝓞 F) F))) (eW i) : ((eW i).Completion)ˣ) : (eW i).Completion)
      = ((bW y i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 1 1 := fun y i =>
    WeylUnipotentDecay.borelDiagSnd_prod_val_fst_apply F eW (bW y) (hmem y) i
  have hrW : ∀ (y : InfiniteAdeleRing F) i, radW y i ≠ 0 := fun y i => (hrad y i).ne'

  have hcU : ∀ y i, WeylUnipotentDecay.archUnits F (borelDiagFst (⟨_, hmem y⟩ : ↥(adelicBorel (𝓞 F) F))) (eW i) = (WeylUnipotentDecay.archUnits F (borelDiagFst (⟨_, hmem 0⟩ : ↥(adelicBorel (𝓞 F) F))) (eW i) * rU (radW 0 i) i) * (rU (radW y i) i)⁻¹ := by
    intro y i
    rw [eq_mul_inv_iff_mul_eq]
    ext : 1
    rw [Units.val_mul, Units.val_mul, haU, haU, hrU _ _ (hrW y i), hrU _ _ (hrW 0 i)]
    exact (hbW_val y i).1
  have hdU' : ∀ y i, WeylUnipotentDecay.archUnits F (borelDiagSnd (⟨_, hmem y⟩ : ↥(adelicBorel (𝓞 F) F))) (eW i) = rU (radW y i) i := by
    intro y i
    ext : 1
    rw [hdU, hrU _ _ (hrW y i)]
    exact (hbW_val y i).2
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℂ, K₀ = ∏ i, μ' (WeylUnipotentDecay.ideleAt F (eW i) (WeylUnipotentDecay.archUnits F (borelDiagFst (⟨_, hmem 0⟩ : ↥(adelicBorel (𝓞 F) F))) (eW i) * rU (radW 0 i) i)) := ⟨_, rfl⟩
  have hE : ∀ y,
      ((μc (borelDiagFst (⟨_, hmem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * ((νc (borelDiagSnd (⟨_, hmem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
      = K₀ * ∏ i, ((radW y i : ℝ) : ℂ) ^ ((tW i : ℂ) * Complex.I) := by
    intro y
    rw [← hμ', ← hν', WeylUnipotentDecay.map_eq_prod_ideleAt F μ' _ (haSnd y),
      WeylUnipotentDecay.map_eq_prod_ideleAt F ν' _ (hdSnd y),
      ← Equiv.prod_comp eW (fun v => μ' (WeylUnipotentDecay.ideleAt F v (WeylUnipotentDecay.archUnits F _ v))),
      ← Equiv.prod_comp eW (fun v => ν' (WeylUnipotentDecay.ideleAt F v (WeylUnipotentDecay.archUnits F _ v))),
      hK₀, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hcU y i, hdU' y i, ← htW i (radW y i) (hrad y i), hχpl, WeylUnipotentDecay.ideleAt_mul,
      WeylUnipotentDecay.ideleAt_inv]
    simp only [map_mul, map_inv]
    ring
  exact ⟨tW, K₀, hE⟩

end ArchChar
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

end WeylUnipotentDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.WeylUnipotentDecay P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.InfiniteAdeleHaar"

set_option maxHeartbeats 8000000 in
open scoped Classical in

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F) (N : ℕ),
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : F,
      ‖∫ y, φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y)) ∂(adelicAddHaar (𝓞 F) F)‖ ≤
        C * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ)) := by
  intro α hα μc νc hμc hνc ψ hψ s hs φ hφ hφK hφc g N
  by_cases hφ0 : ∀ x, φ x = 0
  · refine ⟨1, one_pos, fun ξ => ?_⟩
    simp only [hφ0, zero_mul, MeasureTheory.integral_zero, norm_zero]
    positivity
  letI := adeleBorel (𝓞 F) F
  haveI := borelSpace_adeleBorel (𝓞 F) F
  have hint : ∀ g' : AdelicGL2 (𝓞 F) F,
      Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g')) (adelicAddHaar (𝓞 F) F) :=
    fun g' => WeylUnipotentIntegrable.integrable_weyl_unipotent_mul F hα μc νc hμc hνc s hs φ hφ hφc g'
  obtain ⟨a, ha, hψarch⟩ :=
    NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  letI : ∀ w : InfinitePlace F, MeasurableSpace (w.Completion) := fun w => borel _
  haveI : ∀ w : InfinitePlace F, BorelSpace (w.Completion) := fun w => ⟨rfl⟩
  letI : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  haveI : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))
  haveI : SecondCountableTopology (InfiniteAdeleRing F) :=
    inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have hmeq : adeleBorel (𝓞 F) F
      = (Prod.instMeasurableSpace :
          MeasurableSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) := by
    have h := (Prod.borelSpace (α := InfiniteAdeleRing F)
        (β := FiniteAdeleRing (𝓞 F) F)).measurable_eq
    exact h.symm
  let ρ : @Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) Prod.instMeasurableSpace :=
    hmeq ▸ adelicAddHaar (𝓞 F) F
  have hsplit : ∀ (μ : Measure (InfiniteAdeleRing F)) [μ.IsAddHaarMeasure],
      ∃ (σ : Measure (FiniteAdeleRing (𝓞 F) F)), SigmaFinite σ ∧ ρ = μ.prod σ := by
    intro μ _
    exact WeylUnipotentDecay.adelicAddHaar_eq_prod F μ hmeq
  let nW := Fintype.card (InfinitePlace F)
  let eW : Fin nW ≃ InfinitePlace F := (Fintype.equivFin (InfinitePlace F)).symm
  let KW : Fin nW → Subgroup (AdelicGL2 (𝓞 F) F) := fun i => archRowIsometrySubgroup F (eW i)
  have hcommW : ∀ i j, i ≠ j → ∀ x ∈ KW i, ∀ y ∈ KW j, Commute x y := by
    intro i j hij x hx y hy
    exact WeylUnipotentDecay.commute_archRowIsometrySubgroup_of_ne F
      (fun h => hij (eW.injective h)) hx hy
  have hfW : ∀ i, ∃ t : Finset (AdelicGL2 (𝓞 F) F → ℂ), ∀ k ∈ KW i,
      (fun x => φ (x * k)) ∈ Submodule.span ℂ (t : Set (AdelicGL2 (𝓞 F) F → ℂ)) :=
    fun i => hφK (eW i)
  obtain ⟨M, aT, bT, haT_span, haT_fin, hbT_span, hT_eq⟩ :=
    AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite KW hcommW φ hfW
  have hs_uC : ∀ τ : ℝ, (2 : ℝ) < (4 * s + 2 - (τ : ℂ) * Complex.I).re := by
    intro τ
    have h4 : (4 * s + 2 - (τ : ℂ) * Complex.I).re = 4 * s.re + 2 := by
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re]; simp
    rw [h4]; linarith
  have hs_uR : ∀ τ : ℝ, (1 : ℝ) < (2 * s + 1 - (τ : ℂ) * Complex.I).re := by
    intro τ
    have h2 : (2 * s + 1 - (τ : ℂ) * Complex.I).re = 2 * s.re + 1 := by
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re]; simp
    rw [h2]; linarith
  have hLC : ∃ (LC : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (cC : ℝ), 0 < cC ∧
      ∀ ξ : ℂ, ∃ v' : ℂ, ‖v'‖ ≤ 1 ∧ cC * ‖ξ‖ ≤ ‖LC v' ξ‖ := by
    refine ⟨Complex.reCLM.smulRight (Complex.reCLM : ℂ →L[ℝ] ℝ)
        + Complex.imCLM.smulRight (Complex.imCLM : ℂ →L[ℝ] ℝ), 1, one_pos, fun ξ => ?_⟩
    rcases eq_or_ne ξ 0 with rfl | hξ
    · exact ⟨0, by simp, by simp⟩
    · refine ⟨ξ / ‖ξ‖, ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, norm_norm]
        exact (div_self (norm_ne_zero_iff.mpr hξ)).le
      · have hξn : (‖ξ‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hξ
        have heval : (Complex.reCLM.smulRight (Complex.reCLM : ℂ →L[ℝ] ℝ)
              + Complex.imCLM.smulRight (Complex.imCLM : ℂ →L[ℝ] ℝ)) (ξ / ‖ξ‖) ξ
            = ξ.re * ξ.re / ‖ξ‖ + ξ.im * ξ.im / ‖ξ‖ := by
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
            ContinuousLinearMap.smul_apply, Complex.reCLM_apply, Complex.imCLM_apply,
            smul_eq_mul, Complex.div_re, Complex.div_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.normSq_ofReal]
          field_simp
          ring
        rw [one_mul, heval, Real.norm_eq_abs, ← add_div, ← Complex.normSq_apply,
          Complex.normSq_eq_norm_sq, sq, abs_div,
          abs_of_nonneg (mul_self_nonneg _), abs_of_nonneg (norm_nonneg _),
          mul_div_assoc, div_self hξn, mul_one]
  have hLR : ∃ (LR : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) (cR : ℝ), 0 < cR ∧
      ∀ ξ : ℝ, ∃ v' : ℝ, ‖v'‖ ≤ 1 ∧ cR * ‖ξ‖ ≤ ‖LR v' ξ‖ := by
    refine ⟨ContinuousLinearMap.mul ℝ ℝ, 1, one_pos, fun ξ => ⟨1, by simp, ?_⟩⟩
    simp [ContinuousLinearMap.mul_apply']
  let μ : Measure (InfiniteAdeleRing F) := InfiniteAdeleHaar.archMeasure F
  haveI : μ.IsAddHaarMeasure := InfiniteAdeleHaar.isAddHaarMeasure_archMeasure
  obtain ⟨σ, hσ, hρ⟩ := hsplit μ
  haveI := hσ
  haveI : σ.IsAddHaarMeasure := WeylUnipotentDecay.sigma_isAddHaarMeasure F μ σ hmeq hρ
  have hρint : ∀ f : AdeleRing (𝓞 F) F → ℂ,
      ∫ y, f y ∂(adelicAddHaar (𝓞 F) F) = ∫ p, f p ∂(μ.prod σ) := fun f => by
    rw [← hρ]
    exact (WeylUnipotentDecay.integral_cast_measurableSpace hmeq (adelicAddHaar (𝓞 F) F) f).symm
  have hfinint : ∀ g' : AdelicGL2 (𝓞 F) F, Integrable (fun t : FiniteAdeleRing (𝓞 F) F =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g')) σ :=
    fun g' => AutomorphicForm.weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
      F σ hα μc νc hμc hνc
      s hs φ hφ hφc g'
  have hψnorm : ∀ x : AdeleRing (𝓞 F) F, ‖ψ x‖ = 1 :=
    fun x => NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ x
  have hintξ : ∀ ξ : F, Integrable
      (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) *
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y))) (adelicAddHaar (𝓞 F) F) := by
    intro ξ
    refine (hint g).mul_bdd (c := 1) ?_ ?_
    · exact (hψ.continuous.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => (hψnorm _).le
  have hintξ' : ∀ ξ : F, Integrable
      (fun y : AdeleRing (𝓞 F) F =>
        φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y)))
      (μ.prod σ) := by
    intro ξ
    rw [← hρ]
    exact (WeylUnipotentDecay.integrable_cast_measurableSpace_iff hmeq
      (adelicAddHaar (𝓞 F) F) _).mpr (hintξ ξ)
  have hJrw : ∀ ξ : F,
      ∫ y, φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y)) ∂(adelicAddHaar (𝓞 F) F)
        = ∫ p : AdeleRing (𝓞 F) F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 p * g) *
            ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * p)) ∂(μ.prod σ) := fun ξ => hρint _
  have hFub : ∀ ξ : F,
      (∫ p : AdeleRing (𝓞 F) F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 p * g) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * p)) ∂(μ.prod σ))
        = ∫ y : InfiniteAdeleRing F, ∫ t : FiniteAdeleRing (𝓞 F) F,
            φ (adelicWeyl (𝓞 F) F * unipotentGL2 (WeylUnipotentDecay.adeleOf F y t) * g) *
              ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * WeylUnipotentDecay.adeleOf F y t)) ∂σ ∂μ :=
    fun ξ => MeasureTheory.integral_prod
      (fun p : AdeleRing (𝓞 F) F => φ (adelicWeyl (𝓞 F) F * unipotentGL2 p * g) *
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * p))) (hintξ' ξ)
  have hψsplit : ∀ (ξ : F) (y : InfiniteAdeleRing F) (t : FiniteAdeleRing (𝓞 F) F),
      ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * WeylUnipotentDecay.adeleOf F y t))
        = ψ (WeylUnipotentDecay.adeleOf F (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).1 * y)) 0)
          * ψ (WeylUnipotentDecay.adeleOf F 0 (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t))) := by
    intro ξ y t
    rw [WeylUnipotentDecay.algebraMap_adeleRing_mul_split,
      show -WeylUnipotentDecay.adeleOf F ((algebraMap F (AdeleRing (𝓞 F) F) ξ).1 * y)
            ((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t)
          = WeylUnipotentDecay.adeleOf F (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).1 * y))
              (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t)) from rfl,
      WeylUnipotentDecay.adeleOf_eq_add, ψ.map_add_eq_mul]
  have hbT_ind : ∀ m, IsInducedSection (𝓞 F) F (etaFst μc α hα s) (etaSnd νc α hα s) (bT m) := by
    intro m
    have hsub : {ψ' : AdelicGL2 (𝓞 F) F → ℂ |
          ∃ h : AdelicGL2 (𝓞 F) F, h ∈ (⨆ j, KW j : Subgroup (AdelicGL2 (𝓞 F) F)) ∧
            ψ' = fun x => φ (x * h)}
        ⊆ (inducedSectionSubmodule (etaFst μc α hα s) (etaSnd νc α hα s) :
            Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) := by
      rintro _ ⟨h, _hh, rfl⟩
      exact hφ.rightTranslate h
    exact Submodule.span_le.mpr hsub (hbT_span m)
  have hspan_cont_b : ∀ f : AdelicGL2 (𝓞 F) F → ℂ,
      f ∈ Submodule.span ℂ {ψ' : AdelicGL2 (𝓞 F) F → ℂ |
        ∃ h : AdelicGL2 (𝓞 F) F, h ∈ (⨆ j, KW j : Subgroup (AdelicGL2 (𝓞 F) F)) ∧
          ψ' = fun x => φ (x * h)} → Continuous f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem ψ' h =>
        obtain ⟨h', _hh', rfl⟩ := h
        exact hφc.comp (continuous_mul_const h')
    | zero => exact continuous_const
    | add ψ' ψ'' _ _ hψ' hψ'' => exact hψ'.add hψ''
    | smul c ψ' _ hψ' => exact continuous_const.mul hψ'
  have hbT_cont : ∀ m, Continuous (bT m) := fun m => hspan_cont_b (bT m) (hbT_span m)
  have hspan_cont_a : ∀ f : AdelicGL2 (𝓞 F) F → ℂ,
      f ∈ Submodule.span ℂ {ψ' : AdelicGL2 (𝓞 F) F → ℂ |
        ∃ x h : AdelicGL2 (𝓞 F) F, h ∈ (⨆ j, KW j : Subgroup (AdelicGL2 (𝓞 F) F)) ∧
          ψ' = fun g => φ (x * g * h)} → Continuous f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem ψ' h =>
        obtain ⟨x', h', _hh', rfl⟩ := h
        exact hφc.comp (@WeylUnipotentDecay.continuous_const_mul_mul_const
          (AdelicGL2 (𝓞 F) F) _ _ _ x' h')
    | zero => exact continuous_const
    | add ψ' ψ'' _ _ hψ' hψ'' => exact hψ'.add hψ''
    | smul c ψ' _ hψ' => exact continuous_const.mul hψ'
  have haT_cont : ∀ m i, Continuous (aT m i) := fun m i => hspan_cont_a (aT m i) (haT_span m i)
  have hbT_int : ∀ m g', Integrable
      (fun y : AdeleRing (𝓞 F) F => bT m (adelicWeyl (𝓞 F) F * unipotentGL2 y * g'))
      (adelicAddHaar (𝓞 F) F) :=
    fun m g' => WeylUnipotentIntegrable.integrable_weyl_unipotent_mul F hα μc νc hμc hνc s hs (bT m) (hbT_ind m)
      (hbT_cont m) g'
  have hbTintξ : ∀ m (ξ : F) g', Integrable
      (fun y => bT m (adelicWeyl (𝓞 F) F * unipotentGL2 y * g') *
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y))) (adelicAddHaar (𝓞 F) F) := by
    intro m ξ g'
    refine (hbT_int m g').mul_bdd (c := 1) ?_ ?_
    · exact (hψ.continuous.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => (hψnorm _).le
  have hbTintξ' : ∀ m (ξ : F) g', Integrable
      (fun y : AdeleRing (𝓞 F) F =>
        bT m (adelicWeyl (𝓞 F) F * unipotentGL2 y * g') *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y)))
      (μ.prod σ) := by
    intro m ξ g'
    rw [← hρ]
    exact (WeylUnipotentDecay.integrable_cast_measurableSpace_iff hmeq
      (adelicAddHaar (𝓞 F) F) _).mpr (hbTintξ m ξ g')
  have hbTfinint : ∀ m g', Integrable (fun t : FiniteAdeleRing (𝓞 F) F =>
      bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g')) σ :=
    fun m g' => AutomorphicForm.weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
      F σ hα μc νc hμc hνc
      s hs (bT m) (hbT_ind m) (hbT_cont m) g'
  have hMnorm : ∀ m (ξ : F) g' (t : FiniteAdeleRing (𝓞 F) F),
      ‖bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g') *
        ψ (WeylUnipotentDecay.adeleOf F 0 (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t)))‖
      = ‖bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g')‖ := by
    intro m ξ g' t
    rw [norm_mul, hψnorm, mul_one]
  have hMajorant : ∀ m g' (ξ : F),
      ‖∫ t, bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g') *
          ψ (WeylUnipotentDecay.adeleOf F 0 (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t))) ∂σ‖
        ≤ ∫ t, ‖bT m (adelicWeyl (𝓞 F) F
              * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g')‖ ∂σ := by
    intro m g' ξ
    calc ‖∫ t, bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g') *
              ψ (WeylUnipotentDecay.adeleOf F 0
                (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t))) ∂σ‖
        ≤ ∫ t, ‖bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g') *
              ψ (WeylUnipotentDecay.adeleOf F 0
                (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t)))‖ ∂σ :=
          norm_integral_le_integral_norm _
      _ = ∫ t, ‖bT m (adelicWeyl (𝓞 F) F
              * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g')‖ ∂σ := by
          congr 1; ext t; exact hMnorm m ξ g' t
  have hFmwC : ∀ m i (hw : (eW i).IsComplex),
      let ιC : ↥(Matrix.unitaryGroup (Fin 2) ℂ) →* AdelicGL2 (𝓞 F) F :=
        (adelicArchGLInclAt F (eW i)).comp
          ((AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion).subtype.comp
            (WeylUnipotentDecay.rowIsometryEquivUnitary hw).symm.toMonoidHom)
      ∃ Fm ∈ Submodule.span ℂ {Fm : Matrix (Fin 2) (Fin 2) ℂ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ),
            Fm = fun M => (l.map (fun φ => φ M)).prod},
        ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ),
          aT m i (ιC k) = Fm (k : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro m i hw ιC
    have hΦc : Continuous (fun k => aT m i (ιC k)) :=
      (haT_cont m i).comp ((WeylUnipotentDecay.continuous_adelicArchGLInclAt F (eW i)).comp
        (continuous_subtype_val.comp (WeylUnipotentDecay.continuous_rowIsometryEquivUnitary_symm hw)))
    have hΦfin : ∃ s : Finset (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ),
        ∀ k, (fun x => aT m i (ιC (x * k))) ∈ Submodule.span ℂ (s : Set _) :=
      WeylUnipotentDecay.exists_finset_span_comp_monoidHom ιC (archRowIsometrySubgroup F (eW i))
        (fun k => Subgroup.mem_map_of_mem (adelicArchGLInclAt F (eW i))
          ((WeylUnipotentDecay.rowIsometryEquivUnitary hw).symm k).2)
        (aT m i) (haT_fin m i)
    exact Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite
      (fun k => aT m i (ιC k)) hΦc hΦfin
  have hFmwR : ∀ m i (hv : (eW i).IsReal),
      let ιR : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) →* AdelicGL2 (𝓞 F) F :=
        (adelicArchGLInclAt F (eW i)).comp
          ((AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion).subtype.comp
            (WeylUnipotentDecay.rowIsometryEquivOrthogonal hv).symm.toMonoidHom)
      ∃ Fm ∈ Submodule.span ℂ {Fm : Matrix (Fin 2) (Fin 2) ℝ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℂ),
            Fm = fun M => (l.map (fun φ => φ M)).prod},
        ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
          aT m i (ιR k) = Fm (k : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro m i hv ιR
    have hΦc : Continuous (fun k => aT m i (ιR k)) :=
      (haT_cont m i).comp ((WeylUnipotentDecay.continuous_adelicArchGLInclAt F (eW i)).comp
        (continuous_subtype_val.comp (WeylUnipotentDecay.continuous_rowIsometryEquivOrthogonal_symm hv)))
    have hΦfin : ∃ s : Finset (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ),
        ∀ k, (fun x => aT m i (ιR (x * k))) ∈ Submodule.span ℂ (s : Set _) :=
      WeylUnipotentDecay.exists_finset_span_comp_monoidHom ιR (archRowIsometrySubgroup F (eW i))
        (fun k => Subgroup.mem_map_of_mem (adelicArchGLInclAt F (eW i))
          ((WeylUnipotentDecay.rowIsometryEquivOrthogonal hv).symm k).2)
        (aT m i) (haT_fin m i)
    exact Matrix.OrthogonalGroup.exists_polynomial_eq_of_continuous_of_rightFinite
      (fun k => aT m i (ιR k)) hΦc hΦfin
  let LC : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := WeylUnipotentDecay.pairingC
  have hcC : (0 : ℝ) < 1 := one_pos
  have hLCξ : ∀ ξ : ℂ, ∃ v' : ℂ, ‖v'‖ ≤ 1 ∧ (1 : ℝ) * ‖ξ‖ ≤ ‖LC v' ξ‖ := fun ξ => by
    rcases eq_or_ne ξ 0 with rfl | hξ
    · exact ⟨0, by simp, by simp⟩
    · refine ⟨ξ / ‖ξ‖, ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, norm_norm]
        exact (div_self (norm_ne_zero_iff.mpr hξ)).le
      · have hξn : (‖ξ‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hξ
        have heval : LC (ξ / ‖ξ‖) ξ = ξ.re * ξ.re / ‖ξ‖ + ξ.im * ξ.im / ‖ξ‖ := by
          rw [show LC = WeylUnipotentDecay.pairingC from rfl, WeylUnipotentDecay.pairingC_apply]
          simp only [Complex.div_re, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.normSq_ofReal]
          field_simp; ring
        rw [one_mul, heval, Real.norm_eq_abs, ← add_div, ← Complex.normSq_apply,
          Complex.normSq_eq_norm_sq, sq, abs_div,
          abs_of_nonneg (mul_self_nonneg _), abs_of_nonneg (norm_nonneg _),
          mul_div_assoc, div_self hξn, mul_one]
  let LR : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := WeylUnipotentDecay.pairingR
  have hcR : (0 : ℝ) < 1 := one_pos
  have hLRξ : ∀ ξ : ℝ, ∃ v' : ℝ, ‖v'‖ ≤ 1 ∧ (1 : ℝ) * ‖ξ‖ ≤ ‖LR v' ξ‖ := fun ξ =>
    ⟨1, by simp, by simp [show LR = WeylUnipotentDecay.pairingR from rfl,
      WeylUnipotentDecay.pairingR_apply]⟩
  have hArchDecayC : ∀ m i (hw : (eW i).IsComplex) (τ : ℝ),
      let ιC : ↥(Matrix.unitaryGroup (Fin 2) ℂ) →* AdelicGL2 (𝓞 F) F :=
        (adelicArchGLInclAt F (eW i)).comp
          ((AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion).subtype.comp
            (WeylUnipotentDecay.rowIsometryEquivUnitary hw).symm.toMonoidHom)
      let gwC : Matrix (Fin 2) (Fin 2) ℂ :=
        ((WeylUnipotentDecay.glMapRingEquiv
          (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
          (NumberField.AdelicLevel.archComponent F (eW i)
            (NumberField.AdelicLevel.glArch (𝓞 F) F g))) : Matrix (Fin 2) (Fin 2) ℂ)
      ∃ (Fm : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (C : ℝ),
        (∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ),
          aT m i (ιC k) = Fm (k : Matrix (Fin 2) (Fin 2) ℂ)) ∧
        Continuous (fun z : ℂ => Fm (AutomorphicForm.ComplexIwasawa.kC gwC z)) ∧
        (∃ B : ℝ, ∀ z : ℂ, ‖Fm (AutomorphicForm.ComplexIwasawa.kC gwC z)‖ ≤ B) ∧
        0 < C ∧ ∀ ξ' : ℂ,
          ‖VectorFourier.fourierIntegral Real.fourierChar volume LC.toLinearMap₁₂
            (fun z => ((AutomorphicForm.ComplexIwasawa.radC gwC z : ℂ) ^ (-(4 * s + 2 - (τ : ℂ) * Complex.I)))
              * Fm (AutomorphicForm.ComplexIwasawa.kC gwC z)) ξ'‖
            ≤ C * (1 + ‖ξ'‖) ^ (-(N : ℝ)) := by
    intro m i hw τ ιC gwC
    have hgwC : gwC.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero _
    obtain ⟨Fm, hFm_span, hΦ_eq⟩ := hFmwC m i hw
    obtain ⟨hPC, hPB⟩ := WeylUnipotentDecay.contDiff_and_bound_comp_of_mem_span_listProd
      (AutomorphicForm.ComplexIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kC_apply hgwC).1
      (AutomorphicForm.ComplexIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kC_apply hgwC).2
      hFm_span
    obtain ⟨C, hC, hbound⟩ :=
      AutomorphicForm.ComplexIwasawa.norm_fourierIntegral_cpow_radC_mul_le_polyDecay
        hgwC (hs_uC τ) hPC hPB LC hcC hLCξ N
    obtain ⟨B₀, -, hB₀⟩ := hPB 0
    exact ⟨Fm, C, hΦ_eq, hPC.continuous,
      ⟨B₀, fun z => by simpa only [norm_iteratedFDeriv_zero] using hB₀ z⟩, hC, hbound⟩
  have hArchDecayR : ∀ m i (hv : (eW i).IsReal) (τ : ℝ),
      let ιR : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) →* AdelicGL2 (𝓞 F) F :=
        (adelicArchGLInclAt F (eW i)).comp
          ((AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion).subtype.comp
            (WeylUnipotentDecay.rowIsometryEquivOrthogonal hv).symm.toMonoidHom)
      let gwR : Matrix (Fin 2) (Fin 2) ℝ :=
        ((WeylUnipotentDecay.glMapRingEquiv
          (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)
          (NumberField.AdelicLevel.archComponent F (eW i)
            (NumberField.AdelicLevel.glArch (𝓞 F) F g))) : Matrix (Fin 2) (Fin 2) ℝ)
      ∃ (Fm : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (C : ℝ),
        (∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
          aT m i (ιR k) = Fm (k : Matrix (Fin 2) (Fin 2) ℝ)) ∧
        Continuous (fun x : ℝ => Fm (WeylUnipotentDecay.realIwasawaK gwR x)) ∧
        (∃ B : ℝ, ∀ x : ℝ, ‖Fm (WeylUnipotentDecay.realIwasawaK gwR x)‖ ≤ B) ∧
        0 < C ∧ ∀ ξ' : ℝ,
          ‖VectorFourier.fourierIntegral Real.fourierChar volume LR.toLinearMap₁₂
            (fun x => ((Real.sqrt ((gwR 0 0 + x * gwR 1 0) ^ 2
                  + (gwR 0 1 + x * gwR 1 1) ^ 2) : ℂ) ^ (-(2 * s + 1 - (τ : ℂ) * Complex.I)))
              * Fm (WeylUnipotentDecay.realIwasawaK gwR x)) ξ'‖
            ≤ C * (1 + ‖ξ'‖) ^ (-(N : ℝ)) := by
    intro m i hv τ ιR gwR
    have hgwR : gwR.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero _
    obtain ⟨Fm, hFm_span, hΦ_eq⟩ := hFmwR m i hv
    obtain ⟨hPC, hPB⟩ := WeylUnipotentDecay.contDiff_and_bound_comp_of_mem_span_listProd
      (k := WeylUnipotentDecay.realIwasawaK gwR)
      (AutomorphicForm.RealIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kR_apply hgwR).1
      (AutomorphicForm.RealIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kR_apply hgwR).2
      hFm_span
    obtain ⟨C, hC, hbound⟩ :=
      AutomorphicForm.RealIwasawa.norm_fourierIntegral_cpow_rad_mul_le_polyDecay
        hgwR (hs_uR τ) hPC hPB LR hcR hLRξ N
    obtain ⟨B₀, -, hB₀⟩ := hPB 0
    exact ⟨Fm, C, hΦ_eq, hPC.continuous,
      ⟨B₀, fun z => by simpa only [norm_iteratedFDeriv_zero] using hB₀ z⟩, hC, hbound⟩
  let gwW : ∀ i, GL (Fin 2) (eW i).Completion := fun i =>
    NumberField.AdelicLevel.archComponent F (eW i) (NumberField.AdelicLevel.glArch (𝓞 F) F g)
  let kRI : InfiniteAdeleRing F → ∀ i,
      ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion) := fun y i =>
    if hv : (eW i).IsReal then
      (WeylUnipotentDecay.rowIsometryEquivOrthogonal hv).symm
        ⟨WeylUnipotentDecay.realIwasawaK
            ((WeylUnipotentDecay.glMapRingEquiv
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) (gwW i) :
                GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
            ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) (y (eW i))),
          WeylUnipotentDecay.realIwasawaK_mem_orthogonalGroup
            (Matrix.GeneralLinearGroup.det_ne_zero _) _⟩
    else
      have hw : (eW i).IsComplex :=
        NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
      (WeylUnipotentDecay.rowIsometryEquivUnitary hw).symm
        ⟨AutomorphicForm.ComplexIwasawa.kC
            ((WeylUnipotentDecay.glMapRingEquiv
              (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (gwW i) :
                GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
            ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (y (eW i))),
          Matrix.specialUnitaryGroup_le_unitaryGroup
            (AutomorphicForm.ComplexIwasawa.kC_mem_specialUnitaryGroup
              (Matrix.GeneralLinearGroup.det_ne_zero _) _)⟩
  let kA : InfiniteAdeleRing F → Fin nW → AdelicGL2 (𝓞 F) F := fun y i =>
    adelicArchGLInclAt F (eW i) (kRI y i)
  have hkA : ∀ y i, kA y i ∈ KW i := fun y i =>
    Subgroup.mem_map_of_mem (adelicArchGLInclAt F (eW i)) (kRI y i).2
  let xBF : InfiniteAdeleRing F → FiniteAdeleRing (𝓞 F) F → AdelicGL2 (𝓞 F) F := fun y t =>
    adelicWeyl (𝓞 F) F * unipotentGL2 (WeylUnipotentDecay.adeleOf F y t) * g
      * (List.ofFn (kA y)).prod⁻¹
  have hφeq : ∀ (y : InfiniteAdeleRing F) (t : FiniteAdeleRing (𝓞 F) F),
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (WeylUnipotentDecay.adeleOf F y t) * g)
        = ∑ m, (∏ i, aT m i (kA y i)) * bT m (xBF y t) := fun y t => by
    have heq : adelicWeyl (𝓞 F) F * unipotentGL2 (WeylUnipotentDecay.adeleOf F y t) * g
        = xBF y t * (List.ofFn (kA y)).prod :=
      (inv_mul_cancel_right _ _).symm
    exact heq ▸ hT_eq (xBF y t) (kA y) (hkA y)
  have hkprod_fin : ∀ y, NumberField.AdelicLevel.glFin (𝓞 F) F (List.ofFn (kA y)).prod = 1 :=
    fun y => WeylUnipotentDecay.glFin_prod_adelicArchGLInclAt F (fun j => eW j)
      (fun j => ((kRI y j : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup
        (eW j).Completion)) : GL (Fin 2) (eW j).Completion))
  have hxBF_fin : ∀ y t, NumberField.AdelicLevel.glFin (𝓞 F) F (xBF y t)
      = NumberField.AdelicLevel.glFin (𝓞 F) F (adelicWeyl (𝓞 F) F)
        * unipotentGL2 (R := FiniteAdeleRing (𝓞 F) F) t
        * NumberField.AdelicLevel.glFin (𝓞 F) F g := fun y t => by
    simp only [xBF, map_mul, map_inv, hkprod_fin y, inv_one, mul_one,
      WeylUnipotentDecay.glFin_unipotentGL2]
    rfl
  have hkprod_arch : ∀ y i,
      NumberField.AdelicLevel.archComponent F (eW i)
          (NumberField.AdelicLevel.glArch (𝓞 F) F (List.ofFn (kA y)).prod)
        = ((kRI y i : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup
              (eW i).Completion)) : GL (Fin 2) (eW i).Completion) := fun y i =>
    WeylUnipotentDecay.archComponent_glArch_prod_adelicArchGLInclAt F (fun j => eW j) eW.injective
      (fun j => ((kRI y j : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup
        (eW j).Completion)) : GL (Fin 2) (eW j).Completion)) i
  have hxBF_arch : ∀ y t i,
      NumberField.AdelicLevel.archComponent F (eW i)
          (NumberField.AdelicLevel.glArch (𝓞 F) F (xBF y t))
        = gl2Weyl * unipotentGL2 (y (eW i)) * gwW i
          * ((kRI y i : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup
              (eW i).Completion)) : GL (Fin 2) (eW i).Completion)⁻¹ := fun y t i => by
    simp only [xBF, map_mul, map_inv, hkprod_arch y i,
      WeylUnipotentDecay.archComponent_glArch_adelicWeyl,
      WeylUnipotentDecay.archComponent_glArch_unipotentGL2]
    rfl
  let bArch : InfiniteAdeleRing F → ∀ i, GL (Fin 2) (eW i).Completion := fun y i =>
    gl2Weyl * unipotentGL2 (y (eW i)) * gwW i
      * ((kRI y i : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup
          (eW i).Completion)) : GL (Fin 2) (eW i).Completion)⁻¹
  have hxBF_bArch : ∀ y t i,
      NumberField.AdelicLevel.archComponent F (eW i)
        (NumberField.AdelicLevel.glArch (𝓞 F) F (xBF y t)) = bArch y i := hxBF_arch
  let gwR : ∀ i, (eW i).IsReal → Matrix (Fin 2) (Fin 2) ℝ := fun i hv =>
    ((WeylUnipotentDecay.glMapRingEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) (gwW i) : GL (Fin 2) ℝ)
        : Matrix (Fin 2) (Fin 2) ℝ)
  let gwC : ∀ i, (eW i).IsComplex → Matrix (Fin 2) (Fin 2) ℂ := fun i hw =>
    ((WeylUnipotentDecay.glMapRingEquiv
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (gwW i) : GL (Fin 2) ℂ)
        : Matrix (Fin 2) (Fin 2) ℂ)
  obtain ⟨radW, hradW⟩ : ∃ radW : InfiniteAdeleRing F → Fin nW → ℝ, ∀ y i, radW y i =
      if hv : (eW i).IsReal then
        Real.sqrt ((gwR i hv 0 0
              + NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv (y (eW i)) * gwR i hv 1 0) ^ 2
            + (gwR i hv 0 1
              + NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv (y (eW i)) * gwR i hv 1 1) ^ 2)
      else
        AutomorphicForm.ComplexIwasawa.radC
          (gwC i (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv))
          (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv) (y (eW i))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨NW, hNW⟩ : ∃ NW : Fin nW → ℝ, ∀ i, NW i =
      if hv : (eW i).IsReal then |(gwR i hv).det|
      else ‖(gwC i (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv)).det‖ :=
    ⟨_, fun _ => rfl⟩
  have hradR : ∀ y i (hv : (eW i).IsReal), radW y i =
      Real.sqrt ((gwR i hv 0 0
            + NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv (y (eW i)) * gwR i hv 1 0) ^ 2
          + (gwR i hv 0 1
            + NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv (y (eW i)) * gwR i hv 1 1) ^ 2) :=
    fun y i hv => by rw [hradW, dif_pos hv]
  have hradC : ∀ y i (hw : (eW i).IsComplex), radW y i =
      AutomorphicForm.ComplexIwasawa.radC (gwC i hw)
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw (y (eW i))) :=
    fun y i hw => by
      rw [hradW, dif_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw)]
  have hNW_R : ∀ i (hv : (eW i).IsReal), NW i = |(gwR i hv).det| := fun i hv => by
    rw [hNW, dif_pos hv]
  have hNW_C : ∀ i (hw : (eW i).IsComplex), NW i = ‖(gwC i hw).det‖ := fun i hw => by
    rw [hNW, dif_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw)]
  have hbArch_ent : ∀ y i, 0 < radW y i ∧ 0 < NW i
      ∧ ((bArch y i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 1 0 = 0
      ∧ ‖((bArch y i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 0 0‖
          = NW i / radW y i
      ∧ ‖((bArch y i : GL (Fin 2) (eW i).Completion) : Matrix (Fin 2) (Fin 2) (eW i).Completion) 1 1‖
          = radW y i := fun y i => by
    by_cases hv : (eW i).IsReal
    · rw [hradR y i hv, hNW_R i hv]
      let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
      have hkR : ((WeylUnipotentDecay.glMapRingEquiv e
            ((kRI y i : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion))
              : GL (Fin 2) (eW i).Completion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          = WeylUnipotentDecay.realIwasawaK (gwR i hv) (e (y (eW i))) :=
        Matrix.ext fun a b => by
          simp only [kRI, dif_pos hv, WeylUnipotentDecay.glMapRingEquiv_coe_apply,
            WeylUnipotentDecay.coe_rowIsometryEquivOrthogonal_symm]
          exact e.apply_symm_apply _
      exact WeylUnipotentDecay.placeEntries_real e (WeylUnipotentDecay.norm_ringEquivRealOfIsReal hv) (gwW i)
        ((kRI y i : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion))
          : GL (Fin 2) (eW i).Completion) (y (eW i)) (gwR i hv) rfl hkR
    · have hw : (eW i).IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
      rw [hradC y i hw, hNW_C i hw]
      let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      have hkC : ((WeylUnipotentDecay.glMapRingEquiv e
            ((kRI y i : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion))
              : GL (Fin 2) (eW i).Completion) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
          = AutomorphicForm.ComplexIwasawa.kC (gwC i hw) (e (y (eW i))) :=
        Matrix.ext fun a b => by
          simp only [kRI, dif_neg hv, WeylUnipotentDecay.glMapRingEquiv_coe_apply,
            WeylUnipotentDecay.coe_rowIsometryEquivUnitary_symm]
          exact e.apply_symm_apply _
      exact WeylUnipotentDecay.placeEntries_complex e (WeylUnipotentDecay.norm_ringEquivComplexOfIsComplex hw)
        (gwW i)
        ((kRI y i : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion))
          : GL (Fin 2) (eW i).Completion) (y (eW i)) (gwC i hw) rfl hkC
  let bAInf : InfiniteAdeleRing F → AdelicGL2 (𝓞 F) F := fun y =>
    (List.ofFn fun i => adelicArchGLInclAt F (eW i) (bArch y i)).prod
  have hbAInf_mem : ∀ y, bAInf y ∈ adelicBorel (𝓞 F) F := fun y =>
    WeylUnipotentDecay.prod_adelicArchGLInclAt_mem_adelicBorel F eW (bArch y) fun i => (hbArch_ent y i).2.2.1
  have hbAInf_arch : ∀ y i,
      NumberField.AdelicLevel.archComponent F (eW i)
        (NumberField.AdelicLevel.glArch (𝓞 F) F (bAInf y)) = bArch y i := fun y i =>
    WeylUnipotentDecay.archComponent_glArch_prod_adelicArchGLInclAt F (fun j => eW j) eW.injective
      (bArch y) i
  have hbAInf_fin : ∀ y, NumberField.AdelicLevel.glFin (𝓞 F) F (bAInf y) = 1 := fun y =>
    WeylUnipotentDecay.glFin_prod_adelicArchGLInclAt F (fun j => eW j) (bArch y)
  obtain ⟨xFin, hxFin0⟩ : ∃ xf : FiniteAdeleRing (𝓞 F) F → AdelicGL2 (𝓞 F) F,
      ∀ t, (bAInf 0)⁻¹ * xBF 0 t = xf t :=
    ⟨fun t => (bAInf 0)⁻¹ * xBF 0 t, fun _ => rfl⟩
  have hxFin : ∀ y t, (bAInf y)⁻¹ * xBF y t = xFin t := fun y t => by
    rw [← hxFin0 t]
    refine WeylUnipotentDecay.adelicGL2_ext F (fun w => ?_) ?_
    · obtain ⟨i, rfl⟩ := eW.surjective w
      simp only [map_mul (NumberField.AdelicLevel.glArch (𝓞 F) F),
        map_inv (NumberField.AdelicLevel.glArch (𝓞 F) F),
        map_mul (NumberField.AdelicLevel.archComponent F (eW i)),
        map_inv (NumberField.AdelicLevel.archComponent F (eW i)),
        hbAInf_arch, hxBF_bArch, inv_mul_cancel]
    · simp only [map_mul (NumberField.AdelicLevel.glFin (𝓞 F) F),
        map_inv (NumberField.AdelicLevel.glFin (𝓞 F) F), hbAInf_fin, inv_one, one_mul, hxBF_fin]
  have hbT_split : ∀ y t m, bT m (xBF y t)
      = ((etaFst μc α hα s (borelDiagFst (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F)))
            : ℂˣ) : ℂ)
        * ((etaSnd νc α hα s (borelDiagSnd (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F)))
            : ℂˣ) : ℂ)
        * bT m (xFin t) := fun y t m =>
    WeylUnipotentDecay.apply_eq_mul_apply_of_inv_mul_eq (f := bT m)
      (hbT_ind m (bAInf y) (hbAInf_mem y)) (hxFin y t)
  have hαa : ∀ y, ((α (borelDiagFst (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ)
      = ∏ i, (NW i / radW y i) ^ (eW i).mult := fun y =>
    WeylUnipotentDecay.val_modulus_borelDiagFst_prod F eW (bArch y) (hbAInf_mem y) _
      fun i => (hbArch_ent y i).2.2.2.1
  have hαd : ∀ y, ((α (borelDiagSnd (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ)
      = ∏ i, radW y i ^ (eW i).mult := fun y =>
    WeylUnipotentDecay.val_modulus_borelDiagSnd_prod F eW (bArch y) (hbAInf_mem y) _
      fun i => (hbArch_ent y i).2.2.2.2

  have hkR : ∀ (y : InfiniteAdeleRing F) i (hv : (eW i).IsReal), ((WeylUnipotentDecay.glMapRingEquiv (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)
        ((kRI y i : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion)) : GL (Fin 2) (eW i).Completion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = WeylUnipotentDecay.realIwasawaK (gwR i hv) ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) (y (eW i))) := fun y i hv =>
    Matrix.ext fun a b => by
      simp only [kRI, dif_pos hv, WeylUnipotentDecay.glMapRingEquiv_coe_apply,
        WeylUnipotentDecay.coe_rowIsometryEquivOrthogonal_symm]
      exact (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).apply_symm_apply _
  have hkC : ∀ (y : InfiniteAdeleRing F) i (hw : (eW i).IsComplex), ((WeylUnipotentDecay.glMapRingEquiv (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
        ((kRI y i : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion)) : GL (Fin 2) (eW i).Completion) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = AutomorphicForm.ComplexIwasawa.kC (gwC i hw) ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) (y (eW i))) := fun y i hw =>
    Matrix.ext fun a b => by
      simp only [kRI, dif_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw),
        WeylUnipotentDecay.glMapRingEquiv_coe_apply, WeylUnipotentDecay.coe_rowIsometryEquivUnitary_symm]
      exact (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).apply_symm_apply _
  obtain ⟨tW, K₀, hE₀⟩ := WeylUnipotentDecay.archChar_factorization F α rfl hα μc νc hμc hνc s φ hφ hφc hφ0 eW gwW
    gwR (fun _ _ => rfl) gwC (fun _ _ => rfl)
    (fun y i => ((kRI y i : ↥(AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion)) : GL (Fin 2) (eW i).Completion))
    hkR hkC radW hradR hradC (fun y i => (hbArch_ent y i).1) bArch (fun _ _ => rfl) hbAInf_mem
  have hE : ∀ y,
      ((μc (borelDiagFst (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((νc (borelDiagSnd (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
      = K₀ * ∏ i, ((radW y i : ℝ) : ℂ) ^ ((tW i : ℂ) * Complex.I) := hE₀
  clear hE₀
  have hη : ∀ y,
      ((etaFst μc α hα s (borelDiagFst (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((etaSnd νc α hα s (borelDiagSnd (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
      = K₀ * ((∏ i, ((NW i : ℝ) : ℂ) ^ (((eW i).mult : ℂ) * (s + 1 / 2)))
        * ∏ i, ((radW y i : ℝ) : ℂ) ^ (-(((eW i).mult : ℂ) * (2 * s + 1)) + (tW i : ℂ) * Complex.I)) := by
    intro y
    have h1 := WeylUnipotentDecay.etaFst_one_mul_etaSnd_one_eq_prod α hα s _ _ (fun i => (eW i).mult) NW (radW y)
      (fun i => (hbArch_ent 0 i).2.1) (fun i => (hbArch_ent y i).1) (hαa y) (hαd y)
    have hsplit : ∀ i, ((radW y i : ℝ) : ℂ) ^ (-(((eW i).mult : ℂ) * (2 * s + 1)) + (tW i : ℂ) * Complex.I)
        = ((radW y i : ℝ) : ℂ) ^ (-(((eW i).mult : ℂ) * (2 * s + 1)))
          * ((radW y i : ℝ) : ℂ) ^ ((tW i : ℂ) * Complex.I) := fun i =>
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hbArch_ent y i).1.ne')
    have hfac :
        ((etaFst μc α hα s (borelDiagFst (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
          * ((etaSnd νc α hα s (borelDiagSnd (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        = (((μc (borelDiagFst (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((νc (borelDiagSnd (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ))
          * (((etaFst 1 α hα s (borelDiagFst (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((etaSnd 1 α hα s (borelDiagSnd (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)) := by
      rw [etaFst_apply, etaSnd_apply, etaFst_apply, etaSnd_apply, MonoidHom.one_apply, MonoidHom.one_apply,
        one_mul, one_mul]
      push_cast
      ring
    rw [hfac, h1, hE y]
    simp_rw [hsplit]
    rw [Finset.prod_mul_distrib]
    ring
  have hkA_R : ∀ y i (hv : (eW i).IsReal), kA y i
      = ((adelicArchGLInclAt F (eW i)).comp
          ((AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion).subtype.comp
            (WeylUnipotentDecay.rowIsometryEquivOrthogonal hv).symm.toMonoidHom))
        ⟨WeylUnipotentDecay.realIwasawaK (gwR i hv)
            (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv (y (eW i))),
          WeylUnipotentDecay.realIwasawaK_mem_orthogonalGroup (Matrix.GeneralLinearGroup.det_ne_zero _) _⟩ :=
    fun y i hv => by
      simp only [kA, kRI, dif_pos hv]
      rfl
  have hkA_C : ∀ y i (hw : (eW i).IsComplex), kA y i
      = ((adelicArchGLInclAt F (eW i)).comp
          ((AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion).subtype.comp
            (WeylUnipotentDecay.rowIsometryEquivUnitary hw).symm.toMonoidHom))
        ⟨AutomorphicForm.ComplexIwasawa.kC (gwC i hw)
            (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw (y (eW i))),
          Matrix.specialUnitaryGroup_le_unitaryGroup
            (AutomorphicForm.ComplexIwasawa.kC_mem_specialUnitaryGroup
              (Matrix.GeneralLinearGroup.det_ne_zero _) _)⟩ :=
    fun y i hw => by
      simp only [kA, kRI, dif_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw)]
      rfl
  have hxFin_eq : ∀ t, xFin t = (bAInf 0)⁻¹
      * (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g
          * (List.ofFn (kA 0)).prod⁻¹) := fun t => (hxFin0 t).symm
  clear_value bAInf bArch xBF kA kRI
  have hinv_mem : (bAInf 0)⁻¹ ∈ adelicBorel (𝓞 F) F := inv_mem (hbAInf_mem 0)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℂ, ∀ m (x : AdelicGL2 (𝓞 F) F), bT m ((bAInf 0)⁻¹ * x) = c₀ * bT m x :=
    ⟨_, fun m x => hbT_ind m (bAInf 0)⁻¹ hinv_mem x⟩
  obtain ⟨g', hg'⟩ : ∃ g' : AdelicGL2 (𝓞 F) F, g * (List.ofFn (kA 0)).prod⁻¹ = g' := ⟨_, rfl⟩
  have hbT_xFin : ∀ m t, bT m (xFin t)
      = c₀ * bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g') :=
    fun m t => by
      rw [hxFin_eq t, ← hg']
      exact WeylUnipotentDecay.apply_mul_word_eq (f := bT m) (hc₀ m) _ _ _ _
  obtain ⟨ηv, hηv⟩ : ∃ ηv : InfiniteAdeleRing F → ℂ, ∀ y, ηv y
      = ((etaFst μc α hα s (borelDiagFst (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((etaSnd νc α hα s (borelDiagSnd (⟨bAInf y, hbAInf_mem y⟩ : ↥(adelicBorel (𝓞 F) F)))
            : ℂˣ) : ℂ) :=
    ⟨_, fun _ => rfl⟩
  have hbT_split' : ∀ y t m, bT m (xBF y t) = ηv y * bT m (xFin t) := fun y t m => by
    rw [hηv]; exact hbT_split y t m
  have hηv_eq : ∀ y, ηv y
      = K₀ * ((∏ i, ((NW i : ℝ) : ℂ) ^ (((eW i).mult : ℂ) * (s + 1 / 2)))
        * ∏ i, ((radW y i : ℝ) : ℂ) ^ (-(((eW i).mult : ℂ) * (2 * s + 1)) + (tW i : ℂ) * Complex.I)) := fun y => by
    rw [hηv]; exact hη y
  obtain ⟨PsiArch, hPsiArch⟩ : ∃ PsiArch : F → InfiniteAdeleRing F → ℂ, ∀ ξ y, PsiArch ξ y
      = ψ (WeylUnipotentDecay.adeleOf F (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).1 * y)) 0) :=
    ⟨_, fun _ _ => rfl⟩
  have hψf_cont : ∀ ξ : F, Continuous (fun t : FiniteAdeleRing (𝓞 F) F =>
      ψ (WeylUnipotentDecay.adeleOf F 0 (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t)))) := fun ξ =>
    hψ.continuous.comp (continuous_const.prodMk (continuous_const.mul continuous_id).neg)
  have hbTψint : ∀ m (ξ : F), Integrable (fun t : FiniteAdeleRing (𝓞 F) F =>
      bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g')
        * ψ (WeylUnipotentDecay.adeleOf F 0 (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t)))) σ :=
    fun m ξ => (hbTfinint m g').mul_bdd (c := 1) (hψf_cont ξ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => (hψnorm _).le)
  obtain ⟨Bf, hBf⟩ : ∃ Bf : Fin M → F → ℂ, ∀ m ξ, Bf m ξ
      = ∫ t, bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g')
          * ψ (WeylUnipotentDecay.adeleOf F 0 (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t))) ∂σ :=
    ⟨_, fun _ _ => rfl⟩
  have hBf_le : ∀ m (ξ : F), ‖Bf m ξ‖
      ≤ ∫ t, ‖bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g')‖ ∂σ :=
    fun m ξ => by rw [hBf]; exact hMajorant m g' ξ
  have hpt : ∀ (ξ : F) (y : InfiniteAdeleRing F) (t : FiniteAdeleRing (𝓞 F) F),
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (WeylUnipotentDecay.adeleOf F y t) * g)
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * WeylUnipotentDecay.adeleOf F y t))
        = ∑ m, ((∏ i, aT m i (kA y i)) * ηv y * c₀ * PsiArch ξ y)
            * (bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g')
                * ψ (WeylUnipotentDecay.adeleOf F 0 (-((algebraMap F (AdeleRing (𝓞 F) F) ξ).2 * t)))) := by
    intro ξ y t
    rw [hφeq y t, hψsplit ξ y t, ← hPsiArch ξ y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hbT_split' y t m, hbT_xFin m t]
    ring
  have hinner : ∀ (ξ : F) (y : InfiniteAdeleRing F),
      (∫ t, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (WeylUnipotentDecay.adeleOf F y t) * g)
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * WeylUnipotentDecay.adeleOf F y t)) ∂σ)
        = ∑ m, ((∏ i, aT m i (kA y i)) * ηv y * c₀ * PsiArch ξ y) * Bf m ξ := by
    intro ξ y
    simp_rw [hpt ξ y]
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl fun m _ => by rw [MeasureTheory.integral_const_mul, hBf]
    · exact fun m _ => (hbTψint m ξ).const_mul _
  have hADC : ∀ m i (hw : (eW i).IsComplex),
      ∃ (Fm : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (C : ℝ),
        (∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ),
          aT m i (((adelicArchGLInclAt F (eW i)).comp
            ((AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion).subtype.comp
              (WeylUnipotentDecay.rowIsometryEquivUnitary hw).symm.toMonoidHom)) k)
            = Fm (k : Matrix (Fin 2) (Fin 2) ℂ)) ∧
        Continuous (fun z : ℂ => Fm (AutomorphicForm.ComplexIwasawa.kC (gwC i hw) z)) ∧
        (∃ B : ℝ, ∀ z : ℂ, ‖Fm (AutomorphicForm.ComplexIwasawa.kC (gwC i hw) z)‖ ≤ B) ∧
        0 < C ∧ ∀ ξ' : ℂ,
          ‖VectorFourier.fourierIntegral Real.fourierChar volume
              WeylUnipotentDecay.pairingC.toLinearMap₁₂
            (fun z => ((AutomorphicForm.ComplexIwasawa.radC (gwC i hw) z : ℂ) ^ (-(4 * s + 2 - (tW i : ℂ) * Complex.I)))
              * Fm (AutomorphicForm.ComplexIwasawa.kC (gwC i hw) z)) ξ'‖
            ≤ C * (1 + ‖ξ'‖) ^ (-(N : ℝ)) :=
    fun m i hw => hArchDecayC m i hw (tW i)
  have hADR : ∀ m i (hv : (eW i).IsReal),
      ∃ (Fm : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (C : ℝ),
        (∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
          aT m i (((adelicArchGLInclAt F (eW i)).comp
            ((AutomorphicForm.WindowedSiegel.rowIsometrySubgroup (eW i).Completion).subtype.comp
              (WeylUnipotentDecay.rowIsometryEquivOrthogonal hv).symm.toMonoidHom)) k)
            = Fm (k : Matrix (Fin 2) (Fin 2) ℝ)) ∧
        Continuous (fun x : ℝ => Fm (WeylUnipotentDecay.realIwasawaK (gwR i hv) x)) ∧
        (∃ B : ℝ, ∀ x : ℝ, ‖Fm (WeylUnipotentDecay.realIwasawaK (gwR i hv) x)‖ ≤ B) ∧
        0 < C ∧ ∀ ξ' : ℝ,
          ‖VectorFourier.fourierIntegral Real.fourierChar volume
              WeylUnipotentDecay.pairingR.toLinearMap₁₂
            (fun x => ((Real.sqrt ((gwR i hv 0 0 + x * gwR i hv 1 0) ^ 2
                  + (gwR i hv 0 1 + x * gwR i hv 1 1) ^ 2) : ℂ) ^ (-(2 * s + 1 - (tW i : ℂ) * Complex.I)))
              * Fm (WeylUnipotentDecay.realIwasawaK (gwR i hv) x)) ξ'‖
            ≤ C * (1 + ‖ξ'‖) ^ (-(N : ℝ)) :=
    fun m i hv => hArchDecayR m i hv (tW i)
  choose FmC CC hFmC using hADC
  choose FmR CR hFmR using hADR
  obtain ⟨Gpl, hGpl_def⟩ : ∃ Gpl : Fin M → ∀ i, (eW i).Completion → ℂ, ∀ m i z, Gpl m i z =
      if hv : (eW i).IsReal then
        ((Real.sqrt ((gwR i hv 0 0
              + NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv z * gwR i hv 1 0) ^ 2
            + (gwR i hv 0 1
              + NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv z * gwR i hv 1 1) ^ 2)
            : ℂ) ^ (-(2 * s + 1 - (tW i : ℂ) * Complex.I)))
          * FmR m i hv (WeylUnipotentDecay.realIwasawaK (gwR i hv)
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv z))
      else
        ((AutomorphicForm.ComplexIwasawa.radC
              (gwC i (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv))
              (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
                (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv) z) : ℂ) ^ (-(4 * s + 2 - (tW i : ℂ) * Complex.I)))
          * FmC m i (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv)
              (AutomorphicForm.ComplexIwasawa.kC
                (gwC i (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv))
                (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
                  (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv) z)) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hGpl : ∀ m i (y : InfiniteAdeleRing F),
      aT m i (kA y i) * ((radW y i : ℝ) : ℂ) ^ (-(((eW i).mult : ℂ) * (2 * s + 1)) + (tW i : ℂ) * Complex.I)
        = Gpl m i (y (eW i)) := by
    intro m i y
    by_cases hv : (eW i).IsReal
    · have hm : (eW i).mult = 1 := NumberField.InfinitePlace.mult_isReal ⟨_, hv⟩
      have he : -(((1 : ℕ) : ℂ) * (2 * s + 1)) + (tW i : ℂ) * Complex.I
          = -(2 * s + 1 - (tW i : ℂ) * Complex.I) := by push_cast; ring
      rw [hGpl_def, dif_pos hv, hkA_R y i hv, (hFmR m i hv).1, hradR y i hv, hm, he]
      exact mul_comm _ _
    · have hw : (eW i).IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
      have hm : (eW i).mult = 2 := NumberField.InfinitePlace.mult_isComplex ⟨_, hw⟩
      have he : -(((2 : ℕ) : ℂ) * (2 * s + 1)) + (tW i : ℂ) * Complex.I
          = -(4 * s + 2 - (tW i : ℂ) * Complex.I) := by push_cast; ring
      rw [hGpl_def, dif_neg hv, hkA_C y i hw, (hFmC m i hw).1, hradC y i hw, hm, he]
      exact mul_comm _ _
  obtain ⟨Cη, hCη⟩ : ∃ Cη : ℂ, Cη = K₀ * ∏ i, ((NW i : ℝ) : ℂ) ^ (((eW i).mult : ℂ) * (s + 1 / 2)) :=
    ⟨_, rfl⟩
  have hcoef : ∀ (ξ : F) m (y : InfiniteAdeleRing F),
      (∏ i, aT m i (kA y i)) * ηv y * c₀ * PsiArch ξ y
        = c₀ * Cη * PsiArch ξ y * ∏ i, Gpl m i (y (eW i)) := by
    intro ξ m y
    simp_rw [← hGpl m _ y]
    rw [hηv_eq y, hCη, Finset.prod_mul_distrib]
    ring
  have hPsiArch_prod : ∀ (ξ : F) (y : InfiniteAdeleRing F),
      PsiArch ξ y = ∏ i, WeylUnipotentDecay.phaseAt F (eW i)
        (algebraMap F (eW i).Completion (-(ξ / a)) * y (eW i)) := fun ξ y => by
    rw [hPsiArch]; exact WeylUnipotentDecay.addChar_arch_eq_prod_phaseAt F ψ ha hψarch eW ξ y
  obtain ⟨Φ, hΦ_def⟩ : ∃ Φ : F → Fin M → ∀ i, (eW i).Completion → ℂ, ∀ ξ m i z,
      Φ ξ m i z = WeylUnipotentDecay.phaseAt F (eW i) (algebraMap F (eW i).Completion (-(ξ / a)) * z) * Gpl m i z :=
    ⟨_, fun _ _ _ _ => rfl⟩
  have hcoef' : ∀ (ξ : F) m (y : InfiniteAdeleRing F),
      (∏ i, aT m i (kA y i)) * ηv y * c₀ * PsiArch ξ y = c₀ * Cη * ∏ i, Φ ξ m i (y (eW i)) := by
    intro ξ m y
    rw [hcoef ξ m y, hPsiArch_prod ξ y]
    simp_rw [hΦ_def]
    rw [Finset.prod_mul_distrib]
    ring
  have hdetR : ∀ i (hv : (eW i).IsReal), (gwR i hv).det ≠ 0 := fun i hv =>
    abs_pos.mp (by rw [← hNW_R i hv]; exact (hbArch_ent 0 i).2.1)
  have hdetC : ∀ i (hw : (eW i).IsComplex), (gwC i hw).det ≠ 0 := fun i hw =>
    norm_pos_iff.mp (by rw [← hNW_C i hw]; exact (hbArch_ent 0 i).2.1)
  have hΦint : ∀ (ξ : F) m i, Integrable (fun z => Φ ξ m i z) (InfiniteAdeleHaar.placeMeasure F (eW i)) := by
    intro ξ m i
    by_cases hv : (eW i).IsReal
    · simp_rw [hΦ_def, hGpl_def, dif_pos hv]
      exact WeylUnipotentDecay.integrable_phaseAt_mul_of_isReal F hv _
        (WeylUnipotentDecay.integrable_cpow_neg_sqrt_mul (hdetR i hv) (hs_uR (tW i)) _ (hFmR m i hv).2.1
          (hFmR m i hv).2.2.1)
    · have hw : (eW i).IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
      simp_rw [hΦ_def, hGpl_def, dif_neg hv]
      exact WeylUnipotentDecay.integrable_phaseAt_mul_of_isComplex F hw _
        (WeylUnipotentDecay.integrable_cpow_neg_radC_mul (hdetC i hw) (hs_uC (tW i)) _ (hFmC m i hw).2.1
          (hFmC m i hw).2.2.1)
  have hκpos : ∀ w : NumberField.InfinitePlace F, 0 < WeylUnipotentDecay.freqScale F a w :=
    fun w => WeylUnipotentDecay.freqScale_pos F ha w
  obtain ⟨dec, hdec⟩ : ∃ dec : F → Fin nW → ℝ, ∀ ξ i,
      dec ξ i = (1 + WeylUnipotentDecay.freqScale F a (eW i) * (eW i) ξ) ^ (-(N : ℝ)) :=
    ⟨_, fun _ _ => rfl⟩
  have hdec_nonneg : ∀ (ξ : F) i, 0 ≤ dec ξ i := fun ξ i => by
    rw [hdec]
    exact Real.rpow_nonneg (add_nonneg zero_le_one
      (mul_nonneg (hκpos _).le (NonnegHomClass.apply_nonneg (eW i) ξ))) _
  obtain ⟨IΦ, hIΦ⟩ : ∃ IΦ : F → Fin M → Fin nW → ℂ, ∀ ξ m i,
      IΦ ξ m i = ∫ z, Φ ξ m i z ∂(InfiniteAdeleHaar.placeMeasure F (eW i)) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨Cpl, hCpl_def⟩ : ∃ Cpl : Fin M → Fin nW → ℝ, ∀ m i, Cpl m i =
      if hv : (eW i).IsReal then CR m i hv
      else CC m i (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv) :=
    ⟨_, fun _ _ => rfl⟩
  have hCpl_pos : ∀ m i, 0 < Cpl m i := by
    intro m i
    rw [hCpl_def]
    by_cases hv : (eW i).IsReal
    · rw [dif_pos hv]; exact (hFmR m i hv).2.2.2.1
    · rw [dif_neg hv]; exact (hFmC m i _).2.2.2.1
  have hΦ_le : ∀ (ξ : F) m i, ‖IΦ ξ m i‖ ≤ Cpl m i * dec ξ i := by
    intro ξ m i
    rw [hIΦ, hCpl_def, hdec]
    by_cases hv : (eW i).IsReal
    · rw [dif_pos hv]
      have hb := (hFmR m i hv).2.2.2.2
        (-(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv (algebraMap F (eW i).Completion (-(ξ / a)))))
      rw [← WeylUnipotentDecay.integral_phaseAt_mul_eq_fourierIntegral_of_isReal F hv,
        WeylUnipotentDecay.norm_freq_of_isReal F hv a ξ] at hb
      simp_rw [hΦ_def, hGpl_def, dif_pos hv]
      exact hb
    · rw [dif_neg hv]
      have hw : (eW i).IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
      have hb := (hFmC m i hw).2.2.2.2 ((-2 : ℝ) •
        (starRingEnd ℂ) (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
          (algebraMap F (eW i).Completion (-(ξ / a)))))
      rw [← WeylUnipotentDecay.integral_phaseAt_mul_eq_fourierIntegral_of_isComplex F hw,
        WeylUnipotentDecay.norm_freq_of_isComplex F hw a ξ] at hb
      simp_rw [hΦ_def, hGpl_def, dif_neg hv]
      exact hb
  have hprodint : ∀ (ξ : F) m,
      Integrable (fun y : InfiniteAdeleRing F => ∏ i, Φ ξ m i (y (eW i))) μ := fun ξ m =>
    WeylUnipotentDecay.integrable_fintype_prod_comp_equiv eW (fun w => InfiniteAdeleHaar.placeMeasure F w) (hΦint ξ m)
  have hJ : ∀ ξ : F,
      ∫ y, φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y)) ∂(adelicAddHaar (𝓞 F) F)
        = ∑ m, (c₀ * Cη * ∏ i, IΦ ξ m i) * Bf m ξ := by
    intro ξ
    rw [hJrw ξ, hFub ξ]
    simp_rw [hinner ξ, hcoef' ξ]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [MeasureTheory.integral_mul_const]
      congr 1
      simp_rw [hIΦ]
      exact WeylUnipotentDecay.integral_const_mul_fintype_prod_comp_equiv eW
        (fun w => InfiniteAdeleHaar.placeMeasure F w) (c₀ * Cη) (Φ ξ m)
    · exact fun m _ => ((hprodint ξ m).const_mul _).mul_const _
  obtain ⟨Mf, hMf⟩ : ∃ Mf : Fin M → ℝ, ∀ m, Mf m
      = ∫ t, ‖bT m (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g')‖ ∂σ :=
    ⟨_, fun _ => rfl⟩
  have hBf_le' : ∀ m (ξ : F), ‖Bf m ξ‖ ≤ Mf m := fun m ξ => by rw [hMf]; exact hBf_le m ξ
  have hMf_nonneg : ∀ m, 0 ≤ Mf m := fun m => (norm_nonneg _).trans (hBf_le' m 0)
  obtain ⟨D, hD_def⟩ : ∃ D : ℝ,
      D = ∏ w : NumberField.InfinitePlace F, max 1 (WeylUnipotentDecay.freqScale F a w ^ (-(N : ℝ))) := ⟨_, rfl⟩
  have hD_nonneg : 0 ≤ D := by
    rw [hD_def]; exact Finset.prod_nonneg fun w _ => zero_le_one.trans (le_max_left _ _)
  have hdecay : ∀ ξ : F,
      (∏ i, dec ξ i) ≤ D * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ)) := fun ξ => by
    simp_rw [hdec]
    rw [hD_def, eW.prod_comp (fun w => (1 + WeylUnipotentDecay.freqScale F a w * w ξ) ^ (-(N : ℝ)))]
    exact WeylUnipotentDecay.prod_rpow_negNat_mul_apply_le F ξ N _ hκpos
  obtain ⟨Km, hKm⟩ : ∃ Km : Fin M → ℝ, ∀ m, Km m = ‖c₀ * Cη‖ * (∏ i, Cpl m i) * Mf m :=
    ⟨_, fun _ => rfl⟩
  have hKm_nonneg : ∀ m, 0 ≤ Km m := fun m => by
    rw [hKm]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => (hCpl_pos m i).le))
      (hMf_nonneg m)
  have hterm : ∀ (ξ : F) m,
      ‖(c₀ * Cη * ∏ i, IΦ ξ m i) * Bf m ξ‖ ≤ Km m * ∏ i, dec ξ i := by
    intro ξ m
    rw [hKm, norm_mul, norm_mul, norm_prod]
    calc ‖c₀ * Cη‖ * (∏ i, ‖IΦ ξ m i‖) * ‖Bf m ξ‖
        ≤ ‖c₀ * Cη‖ * (∏ i, Cpl m i * dec ξ i) * Mf m :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left
              (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hΦ_le ξ m i))
              (norm_nonneg _))
            (hBf_le' m ξ) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _)
              (Finset.prod_nonneg fun i _ => mul_nonneg (hCpl_pos m i).le (hdec_nonneg ξ i)))
      _ = ‖c₀ * Cη‖ * (∏ i, Cpl m i) * Mf m * ∏ i, dec ξ i := by
          rw [Finset.prod_mul_distrib]; ring
  refine ⟨(∑ m, Km m) * D + 1,
    add_pos_of_nonneg_of_pos (mul_nonneg (Finset.sum_nonneg fun m _ => hKm_nonneg m) hD_nonneg) one_pos,
    fun ξ => ?_⟩
  rw [hJ ξ]
  calc ‖∑ m, (c₀ * Cη * ∏ i, IΦ ξ m i) * Bf m ξ‖
      ≤ ∑ m, ‖(c₀ * Cη * ∏ i, IΦ ξ m i) * Bf m ξ‖ := norm_sum_le _ _
    _ ≤ ∑ m, Km m * ∏ i, dec ξ i := Finset.sum_le_sum fun m _ => hterm ξ m
    _ = (∑ m, Km m) * ∏ i, dec ξ i := by rw [Finset.sum_mul]
    _ ≤ (∑ m, Km m) * (D * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left (hdecay ξ) (Finset.sum_nonneg fun m _ => hKm_nonneg m)
    _ ≤ ((∑ m, Km m) * D + 1) * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ)) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
          (Real.rpow_nonneg (by positivity) _)

end S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary
end P2MW
export P2MW.S_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary (solution)
