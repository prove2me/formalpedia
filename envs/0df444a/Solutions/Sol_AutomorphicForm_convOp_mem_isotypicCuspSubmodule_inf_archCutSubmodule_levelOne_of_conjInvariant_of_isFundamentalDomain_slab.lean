-- Prove2me | solution 1 for AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_levelOne_of_conjInvariant_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/75d1af5b-08b7-52cc-98d9-f03eaabf3526

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Tactic.Group
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_levelOne_of_conjInvariant_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace R4BlockConjL1

variable {L : Type} [Field L] [NumberField L]

theorem isHaar : (adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

attribute [local instance] isHaar

scoped instance isMulRightInvariant : (adelicGLHaar (Fin 2) (𝓞 L) L).IsMulRightInvariant :=
  NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar L

variable (L)

def wf : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) := !![0, 1; 1, 0]

theorem weyl_mul_weyl : weyl (𝓞 L) L * weyl (𝓞 L) L = 1 := Units.ext (weyl (𝓞 L) L).val_inv

theorem weyl_inv : (weyl (𝓞 L) L)⁻¹ = weyl (𝓞 L) L := inv_eq_of_mul_eq_one_right (weyl_mul_weyl L)

theorem coe_glFin_weyl :
    ((glFin (𝓞 L) L (weyl (𝓞 L) L) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) = wf L := by
  ext i j
  rw [glFin_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem wf_apply : wf L 0 0 = 0 ∧ wf L 0 1 = 1 ∧ wf L 1 0 = 1 ∧ wf L 1 1 = 0 := ⟨rfl, rfl, rfl, rfl⟩

theorem wf_conj_apply (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    (wf L * m * wf L) 0 0 = m 1 1 ∧ (wf L * m * wf L) 0 1 = m 1 0 ∧
      (wf L * m * wf L) 1 0 = m 0 1 ∧ (wf L * m * wf L) 1 1 = m 0 0 := by
  obtain ⟨h00, h01, h10, h11⟩ := wf_apply L
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11, zero_mul, one_mul, mul_zero, mul_one,
      zero_add, add_zero]

structure IsPrin (M : Ideal (𝓞 L)) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Prop where
  integral : ∀ i j, m i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L
  ball : ∀ i j, (m - 1) i j ∈ idealBall (𝓞 L) L M

variable {L}

theorem integral_mul {x y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hx : ∀ i j, x i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) (hy : ∀ i j, y i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) :
    ∀ i j, (x * y) i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hx i 0) (hy 0 j))
    (mul_mem_integralFiniteAdeles (hx i 1) (hy 1 j))

theorem ball_mul_left {M : Ideal (𝓞 L)} {x y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hx : ∀ i j, x i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) (hy : ∀ i j, y i j ∈ idealBall (𝓞 L) L M) :
    ∀ i j, (x * y) i j ∈ idealBall (𝓞 L) L M := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem_idealBall (mul_mem_idealBall_left (hx i 0) (hy 0 j)) (mul_mem_idealBall_left (hx i 1) (hy 1 j))

theorem ball_mul_right {M : Ideal (𝓞 L)} {x y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hx : ∀ i j, x i j ∈ idealBall (𝓞 L) L M) (hy : ∀ i j, y i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) :
    ∀ i j, (x * y) i j ∈ idealBall (𝓞 L) L M := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem_idealBall (mul_mem_idealBall_right (hx i 0) (hy 0 j)) (mul_mem_idealBall_right (hx i 1) (hy 1 j))

variable (L)

theorem isPrin_iff (M : Ideal (𝓞 L)) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    IsPrin L M m ↔ IsLevelOneMatrix (𝓞 L) L M m ∧ IsLevelOneMatrix (𝓞 L) L M (wf L * m * wf L) := by
  obtain ⟨h00, h01, h10, h11⟩ := wf_conj_apply L m
  have e10 : (m - 1) 1 0 = m 1 0 := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero]
  have e01 : (m - 1) 0 1 = m 0 1 := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero]
  have e11 : (m - 1) 1 1 = m 1 1 - 1 := by rw [Matrix.sub_apply, Matrix.one_apply_eq]
  have e00 : (m - 1) 0 0 = m 0 0 - 1 := by rw [Matrix.sub_apply, Matrix.one_apply_eq]
  constructor
  · intro hp
    refine ⟨⟨⟨hp.integral, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · rw [← e10]; exact hp.ball 1 0
    · rw [← e11]; exact hp.ball 1 1
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · rw [h00]; exact hp.integral 1 1
      · rw [h01]; exact hp.integral 1 0
      · rw [h10]; exact hp.integral 0 1
      · rw [h11]; exact hp.integral 0 0
    · rw [h10, ← e01]; exact hp.ball 0 1
    · rw [h11, ← e00]; exact hp.ball 0 0
  · rintro ⟨h1, h2⟩
    refine ⟨h1.integral, ?_⟩
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · rw [e00, ← h11]; exact h2.lowerRight
    · rw [e01, ← h10]; exact h2.lowerLeft
    · rw [e10]; exact h1.lowerLeft
    · rw [e11]; exact h1.lowerRight

variable {L}

theorem IsPrin.conj {M : Ideal (𝓞 L)} {m a b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hm : IsPrin L M m) (ha : ∀ i j, a i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L)
    (hb : ∀ i j, b i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) (hab : a * b = 1) : IsPrin L M (a * m * b) := by
  refine ⟨integral_mul (integral_mul ha hm.integral) hb, ?_⟩
  have h : a * m * b - 1 = a * (m - 1) * b := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hab]
  rw [h]
  exact ball_mul_right (ball_mul_left ha hm.ball) hb

variable (L)

def finPrincipalLevel (M : Ideal (𝓞 L)) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :=
  finiteLevelOne (𝓞 L) L M ⊓
    (finiteLevelOne (𝓞 L) L M).map (MulAut.conj (glFin (𝓞 L) L (weyl (𝓞 L) L))).toMonoidHom

theorem mem_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (w x : G) :
    x ∈ H.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * x * w ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem mem_principalLevel_inf_iff (M : Ideal (𝓞 L)) (u : AdelicGL2 (𝓞 L) L) :
    u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L ↔
      glArch (𝓞 L) L u = 1 ∧ glFin (𝓞 L) L u ∈ finPrincipalLevel L M := by
  rw [Subgroup.mem_inf, mem_finiteAdelicGL2Subgroup_iff, mem_principalLevel_iff, finPrincipalLevel,
    Subgroup.mem_inf, mem_map_conj_iff, mem_map_conj_iff, mem_levelOne_iff, mem_levelOne_iff, map_mul, map_mul,
    map_inv]
  tauto

theorem mem_finPrincipalLevel_iff (M : Ideal (𝓞 L)) (η : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    η ∈ finPrincipalLevel L M ↔
      IsPrin L M (η : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) ∧
        IsPrin L M ((η⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) := by
  set W : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) := glFin (𝓞 L) L (weyl (𝓞 L) L) with hWdef
  have hW : W⁻¹ = W := by rw [hWdef, ← map_inv, weyl_inv]
  have hcW : (W : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) = wf L := coe_glFin_weyl L
  have h1 : ((W * η * W : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) =
      wf L * (η : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) * wf L := by
    rw [Units.val_mul, Units.val_mul, hcW]
  have h2 : (((W * η * W)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) =
      wf L * ((η⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) * wf L := by
    rw [mul_inv_rev, mul_inv_rev, hW, ← mul_assoc, Units.val_mul, Units.val_mul, hcW]
  rw [finPrincipalLevel, Subgroup.mem_inf, mem_map_conj_iff, ← hWdef, mem_finiteLevelOne_iff, mem_finiteLevelOne_iff, hW,
    h1, h2, isPrin_iff, isPrin_iff]
  tauto

variable {L}

theorem conj_mem_finPrincipalLevel {M : Ideal (𝓞 L)} {η k : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hη : η ∈ finPrincipalLevel L M) (hk : k ∈ finiteIntegralGL2 (𝓞 L) L) : k⁻¹ * η * k ∈ finPrincipalLevel L M := by
  rw [mem_finiteIntegralGL2_iff] at hk
  rw [mem_finPrincipalLevel_iff] at hη ⊢
  have hkk : ((k⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) *
      (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact hη.1.conj hk.2 hk.1 hkk
  · rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul]
    exact hη.2.conj hk.2 hk.1 hkk

theorem glFin_mem_finiteIntegralGL2_of_mem_levelOne {N : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L N) : glFin (𝓞 L) L k ∈ finiteIntegralGL2 (𝓞 L) L := by
  have h := finiteLevelOne_le_finiteLevelZero (𝓞 L) L N (mem_levelOne_iff.mp hk)
  exact mem_finiteIntegralGL2_iff.mpr ⟨h.1.integral, h.2.integral⟩

variable (L)

private theorem _root_.R4BlockConjL1.exists_notMem_finset (T : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ v : HeightOneSpectrum (𝓞 L), v ∉ T := by
  have hinj : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 L), v.asIdeal.under ℤ = Ideal.span {(p.1 : ℤ)} := by
    intro p
    haveI hpr : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hp0 : Ideal.span {(p.1 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 L)))
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hp0 hQ⟩, hQ.2.over.symm⟩
  choose g hg using hinj
  have hginj : Function.Injective g := by
    intro p q hpq
    have h := hg p
    rw [hpq, hg q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    simp only [Int.natAbs_natCast] at h'
    exact Subtype.ext h'.symm
  haveI : Infinite (HeightOneSpectrum (𝓞 L)) := Infinite.of_injective g hginj
  exact Infinite.exists_notMem_finset T

p2m_export "R4BlockConjL1" "exists_notMem_finset"

theorem ne_bot_of_forall_dvd_mem (S : Finset (HeightOneSpectrum (𝓞 L)))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ S) : N ≠ ⊥ := by
  rintro rfl
  obtain ⟨w, hw⟩ := exists_notMem_finset L S
  exact hw (hN w ⟨⊥, by rw [Ideal.mul_bot]⟩)

theorem isOpen_principalLevel {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) :
    IsOpen (principalLevel (𝓞 L) L N : Set (AdelicGL2 (𝓞 L) L)) := by
  have h1 : IsOpen (levelOne (𝓞 L) L N : Set (AdelicGL2 (𝓞 L) L)) := isOpen_levelOne (𝓞 L) L hN
  have hom : IsOpenMap (fun x : AdelicGL2 (𝓞 L) L => weyl (𝓞 L) L * x * (weyl (𝓞 L) L)⁻¹) :=
    (isOpenMap_mul_right (weyl (𝓞 L) L)⁻¹).comp (isOpenMap_mul_left (weyl (𝓞 L) L))
  have h2 : IsOpen (((levelOne (𝓞 L) L N).map (MulAut.conj (weyl (𝓞 L) L)).toMonoidHom :
      Subgroup (AdelicGL2 (𝓞 L) L)) : Set (AdelicGL2 (𝓞 L) L)) := by
    rw [Subgroup.coe_map]
    have heq : ((MulAut.conj (weyl (𝓞 L) L)).toMonoidHom : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) ''
        (levelOne (𝓞 L) L N : Set (AdelicGL2 (𝓞 L) L)) =
        (fun x : AdelicGL2 (𝓞 L) L => weyl (𝓞 L) L * x * (weyl (𝓞 L) L)⁻¹) '' (levelOne (𝓞 L) L N : Set _) := by
      refine Set.image_congr fun x _ => ?_
      rfl
    rw [heq]
    exact hom _ h1
  exact h1.inter h2

theorem eq_of_glArch_eq_of_glFin_eq {g g' : AdelicGL2 (𝓞 L) L} (h1 : glArch (𝓞 L) L g = glArch (𝓞 L) L g')
    (h2 : glFin (𝓞 L) L g = glFin (𝓞 L) L g') : g = g' := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have h : (glArch (𝓞 L) L g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) =
        (glArch (𝓞 L) L g' : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) := Units.ext_iff.mp h1
    have hij := congrArg (fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L) => m i j) h
    simp only [glArch_apply] at hij
    exact hij
  · have h : (glFin (𝓞 L) L g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) =
        (glFin (𝓞 L) L g' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) := Units.ext_iff.mp h2
    have hij := congrArg (fun m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) => m i j) h
    simp only [glFin_apply] at hij
    exact hij

theorem mul_comm_of_glFin_eq_one_of_glArch_eq_one {a r : AdelicGL2 (𝓞 L) L} (ha : glFin (𝓞 L) L a = 1)
    (hr : glArch (𝓞 L) L r = 1) : a * r = r * a := by
  refine eq_of_glArch_eq_of_glFin_eq L ?_ ?_
  · rw [map_mul, map_mul, hr, mul_one, one_mul]
  · rw [map_mul, map_mul, ha, mul_one, one_mul]

theorem apply_conj_eq_of_ne_zero (M : Ideal (𝓞 L)) (g : AdelicGL2 (𝓞 L) L → ℂ)
    (hgU : IsBiInvariantUnder L (principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) g)
    (hgsupp : ∀ x : AdelicGL2 (𝓞 L) L, g x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L, glFin (𝓞 L) L u = glFin (𝓞 L) L x)
    {k : AdelicGL2 (𝓞 L) L} (hka : glArch (𝓞 L) L k = 1) (hkf : glFin (𝓞 L) L k ∈ finiteIntegralGL2 (𝓞 L) L)
    (z : AdelicGL2 (𝓞 L) L) (hz : g z ≠ 0) : g (k⁻¹ * z * k) = g z := by
  obtain ⟨u₀, hu₀, hu₀z⟩ := hgsupp z hz
  obtain ⟨hu₀a, hu₀f⟩ := (mem_principalLevel_inf_iff L M u₀).mp hu₀
  set a : AdelicGL2 (𝓞 L) L := z * u₀⁻¹ with ha
  have haf : glFin (𝓞 L) L a = 1 := by rw [ha, map_mul, map_inv, hu₀z, mul_inv_cancel]
  have hza : z = a * u₀ := by rw [ha, inv_mul_cancel_right]
  have hconj : k⁻¹ * u₀ * k ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L := by
    refine (mem_principalLevel_inf_iff L M _).mpr ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, hka, hu₀a, inv_one, one_mul, one_mul]
    · rw [map_mul, map_mul, map_inv]
      exact conj_mem_finPrincipalLevel hu₀f hkf
  have hcomm : a * k⁻¹ = k⁻¹ * a :=
    mul_comm_of_glFin_eq_one_of_glArch_eq_one L haf (by rw [map_inv, hka, inv_one])
  have hkz : k⁻¹ * z * k = a * (k⁻¹ * u₀ * k) := by
    rw [hza, ← mul_assoc k⁻¹ a u₀, ← hcomm]
    simp only [mul_assoc]
  rw [hkz, (hgU _ hconj a).2, hza, (hgU _ hu₀ a).2]

theorem apply_conj_eq (M : Ideal (𝓞 L)) (g : AdelicGL2 (𝓞 L) L → ℂ)
    (hgU : IsBiInvariantUnder L (principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) g)
    (hgsupp : ∀ x : AdelicGL2 (𝓞 L) L, g x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L, glFin (𝓞 L) L u = glFin (𝓞 L) L x)
    {k : AdelicGL2 (𝓞 L) L} (hka : glArch (𝓞 L) L k = 1) (hkf : glFin (𝓞 L) L k ∈ finiteIntegralGL2 (𝓞 L) L)
    (z : AdelicGL2 (𝓞 L) L) : g (k⁻¹ * z * k) = g z := by
  by_cases hz : g z = 0
  · rw [hz]
    by_contra h
    have h' := apply_conj_eq_of_ne_zero L M g hgU hgsupp (k := k⁻¹) (by rw [map_inv, hka, inv_one])
      (by rw [map_inv]; exact inv_mem hkf) (k⁻¹ * z * k) h
    have hs : k⁻¹⁻¹ * (k⁻¹ * z * k) * k⁻¹ = z := by group
    rw [hs, hz] at h'
    exact h h'.symm
  · exact apply_conj_eq_of_ne_zero L M g hgU hgsupp hka hkf z hz

abbrev levelOneFin (N : Ideal (𝓞 L)) : Subgroup (AdelicGL2 (𝓞 L) L) :=
  levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L

abbrev prinIn (N M : Ideal (𝓞 L)) : Subgroup ↥(levelOneFin L N) :=
  (principalLevel (𝓞 L) L M).subgroupOf (levelOneFin L N)

variable {L}

theorem glArch_coe_levelOneFin {N : Ideal (𝓞 L)} (h : ↥(levelOneFin L N)) :
    glArch (𝓞 L) L (h : AdelicGL2 (𝓞 L) L) = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff L _).mp (Subgroup.mem_inf.mp h.2).2

theorem glFin_coe_levelOneFin {N : Ideal (𝓞 L)} (h : ↥(levelOneFin L N)) :
    glFin (𝓞 L) L (h : AdelicGL2 (𝓞 L) L) ∈ finiteIntegralGL2 (𝓞 L) L :=
  glFin_mem_finiteIntegralGL2_of_mem_levelOne (Subgroup.mem_inf.mp h.2).1

variable (L)

scoped instance prinIn_normal (N M : Ideal (𝓞 L)) : (prinIn L N M).Normal := by
  refine ⟨fun n hn h => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : ((n : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L) ∈
      principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L :=
    Subgroup.mem_inf.mpr ⟨hn, (Subgroup.mem_inf.mp n.2).2⟩
  obtain ⟨hna, hnf⟩ := (mem_principalLevel_inf_iff L M _).mp hn'
  have hha := glArch_coe_levelOneFin h
  have key := conj_mem_finPrincipalLevel hnf (inv_mem (glFin_coe_levelOneFin h))
  rw [inv_inv] at key
  have hmem : ((h * n * h⁻¹ : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L) ∈
      principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    refine (mem_principalLevel_inf_iff L M _).mpr ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, hha, hna, inv_one, mul_one, mul_one]
    · rw [map_mul, map_mul, map_inv]
      exact key
  exact (Subgroup.mem_inf.mp hmem).1

scoped instance compactSpace_levelOneFin (N : Ideal (𝓞 L)) : CompactSpace ↥(levelOneFin L N) :=
  isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup L N)

theorem isOpen_prinIn (N : Ideal (𝓞 L)) {M : Ideal (𝓞 L)} (hM : M ≠ ⊥) :
    IsOpen ((prinIn L N M : Subgroup ↥(levelOneFin L N)) : Set ↥(levelOneFin L N)) := by
  rw [Subgroup.coe_subgroupOf]
  exact (isOpen_principalLevel L hM).preimage continuous_subtype_val

theorem finite_quotient (N : Ideal (𝓞 L)) {M : Ideal (𝓞 L)} (hM : M ≠ ⊥) :
    Finite (↥(levelOneFin L N) ⧸ prinIn L N M) :=
  Subgroup.quotient_finite_of_isOpen _ (isOpen_prinIn L N hM)

def ravg (N M : Ideal (𝓞 L)) [Fintype (↥(levelOneFin L N) ⧸ prinIn L N M)] (g : AdelicGL2 (𝓞 L) L → ℂ) :
    AdelicGL2 (𝓞 L) L → ℂ :=
  fun y => ∑ q : ↥(levelOneFin L N) ⧸ prinIn L N M,
    g (y * ((q.out : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L))

theorem ravg_apply (N M : Ideal (𝓞 L)) [Fintype (↥(levelOneFin L N) ⧸ prinIn L N M)] (g : AdelicGL2 (𝓞 L) L → ℂ)
    (y : AdelicGL2 (𝓞 L) L) :
    ravg L N M g y = ∑ q : ↥(levelOneFin L N) ⧸ prinIn L N M,
      g (y * ((q.out : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L)) := rfl

section Avg

variable (N M : Ideal (𝓞 L)) [Fintype (↥(levelOneFin L N) ⧸ prinIn L N M)]
  (g : AdelicGL2 (𝓞 L) L → ℂ)
  (hgU : IsBiInvariantUnder L (principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) g)

omit [Fintype (↥(levelOneFin L N) ⧸ prinIn L N M)] in
include hgU in

theorem apply_mul_out (y : AdelicGL2 (𝓞 L) L) (c : ↥(levelOneFin L N)) :
    g (y * (((QuotientGroup.mk c : ↥(levelOneFin L N) ⧸ prinIn L N M).out : ↥(levelOneFin L N)) :
      AdelicGL2 (𝓞 L) L)) = g (y * (c : AdelicGL2 (𝓞 L) L)) := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul (prinIn L N M) c
  rw [hn, Subgroup.coe_mul, ← mul_assoc]
  have hnU : (((n : ↥(prinIn L N M)) : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L) ∈
      principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp n.2,
      (Subgroup.mem_inf.mp ((n : ↥(prinIn L N M)) : ↥(levelOneFin L N)).2).2⟩
  exact (hgU _ hnU _).2

include hgU in

theorem ravg_apply_mul (h : ↥(levelOneFin L N)) (y : AdelicGL2 (𝓞 L) L) :
    ravg L N M g (y * (h : AdelicGL2 (𝓞 L) L)) = ravg L N M g y := by
  rw [ravg_apply, ravg_apply]
  have hterm : ∀ q : ↥(levelOneFin L N) ⧸ prinIn L N M,
      g (y * (h : AdelicGL2 (𝓞 L) L) * ((q.out : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L)) =
        g (y * ((((QuotientGroup.mk h : ↥(levelOneFin L N) ⧸ prinIn L N M) * q).out : ↥(levelOneFin L N)) :
          AdelicGL2 (𝓞 L) L)) := by
    intro q
    have hq : (QuotientGroup.mk h : ↥(levelOneFin L N) ⧸ prinIn L N M) * q = QuotientGroup.mk (h * q.out) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq, apply_mul_out L N M g hgU, Subgroup.coe_mul, mul_assoc]
  simp_rw [hterm]
  exact Equiv.sum_comp (Equiv.mulLeft (QuotientGroup.mk h : ↥(levelOneFin L N) ⧸ prinIn L N M))
    (fun q => g (y * ((q.out : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L)))

include hgU in

theorem ravg_mul_apply
    (hgsupp : ∀ x : AdelicGL2 (𝓞 L) L, g x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L, glFin (𝓞 L) L u = glFin (𝓞 L) L x)
    (h : ↥(levelOneFin L N)) (y : AdelicGL2 (𝓞 L) L) :
    ravg L N M g ((h : AdelicGL2 (𝓞 L) L) * y) = ravg L N M g y := by
  rw [ravg_apply, ravg_apply]
  have hterm : ∀ q : ↥(levelOneFin L N) ⧸ prinIn L N M,
      g ((h : AdelicGL2 (𝓞 L) L) * y * ((q.out : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L)) =
        g (y * (((q * (QuotientGroup.mk h : ↥(levelOneFin L N) ⧸ prinIn L N M)).out : ↥(levelOneFin L N)) :
          AdelicGL2 (𝓞 L) L)) := by
    intro q
    have hq : q * (QuotientGroup.mk h : ↥(levelOneFin L N) ⧸ prinIn L N M) = QuotientGroup.mk (q.out * h) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq, apply_mul_out L N M g hgU, Subgroup.coe_mul,
      ← apply_conj_eq L M g hgU hgsupp (glArch_coe_levelOneFin h) (glFin_coe_levelOneFin h)
        ((h : AdelicGL2 (𝓞 L) L) * y * ((q.out : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L))]
    congr 1
    group
  simp_rw [hterm]
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk h : ↥(levelOneFin L N) ⧸ prinIn L N M))
    (fun q => g (y * ((q.out : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L)))

theorem continuous_ravg (hg : Continuous g) : Continuous (ravg L N M g) := by
  unfold ravg
  exact continuous_finsetSum _ fun q _ => hg.comp (continuous_id.mul continuous_const)

theorem hasCompactSupport_ravg (hgc : HasCompactSupport g) : HasCompactSupport (ravg L N M g) := by
  classical
  have key : ∀ s : Finset (↥(levelOneFin L N) ⧸ prinIn L N M),
      HasCompactSupport (fun y : AdelicGL2 (𝓞 L) L =>
        ∑ q ∈ s, g (y * ((q.out : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hgc.comp_homeomorph (Homeomorph.mulRight _)).add ih
  exact key Finset.univ

theorem rightConv_ravg (hg : Continuous g) (hgc : HasCompactSupport g)
    (u : AdelicGL2 (𝓞 L) L → ℂ) (huc : Continuous u)
    (huU : ∀ x : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOneFin L N, u (x * k) = u x) (x : AdelicGL2 (𝓞 L) L) :
    rightConv L u (ravg L N M g) x =
      (Fintype.card (↥(levelOneFin L N) ⧸ prinIn L N M) : ℂ) * rightConv L u g x := by
  set μ : Measure (AdelicGL2 (𝓞 L) L) := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set c : ↥(levelOneFin L N) ⧸ prinIn L N M → AdelicGL2 (𝓞 L) L :=
    fun q => ((q.out : ↥(levelOneFin L N)) : AdelicGL2 (𝓞 L) L) with hc
  have hcmem : ∀ q, c q ∈ levelOneFin L N := fun q => (q.out : ↥(levelOneFin L N)).2
  rw [rightConv_apply, rightConv_apply]
  have hint : ∀ q, Integrable (fun y => u (x * y) * g (y * c q)) μ := fun q =>
    ((huc.comp (continuous_const.mul continuous_id)).mul
      (hg.comp (continuous_id.mul continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hgc.comp_homeomorph (Homeomorph.mulRight (c q))))
  have hstep : ∀ q, ∫ y, u (x * y) * g (y * c q) ∂μ = ∫ y, u (x * y) * g y ∂μ := by
    intro q
    rw [← integral_mul_right_eq_self (μ := μ) (fun y => u (x * y) * g (y * c q)) (c q)⁻¹]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show u (x * (y * (c q)⁻¹)) * g (y * (c q)⁻¹ * c q) = u (x * y) * g y
    rw [inv_mul_cancel_right, ← mul_assoc, huU _ _ (inv_mem (hcmem q))]
  calc ∫ y, u (x * y) * ravg L N M g y ∂μ
      = ∫ y, ∑ q, u (x * y) * g (y * c q) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show u (x * y) * ravg L N M g y = ∑ q, u (x * y) * g (y * c q)
        rw [ravg_apply, Finset.mul_sum]
    _ = ∑ q, ∫ y, u (x * y) * g (y * c q) ∂μ := integral_finsetSum _ (fun q _ => hint q)
    _ = ∑ q : ↥(levelOneFin L N) ⧸ prinIn L N M, ∫ y, u (x * y) * g y ∂μ :=
        Finset.sum_congr rfl (fun q _ => hstep q)
    _ = (Fintype.card (↥(levelOneFin L N) ⧸ prinIn L N M) : ℂ) * ∫ y, u (x * y) * g y ∂μ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Avg

theorem rightConv_mem_archCutSubmodule_of_conjInvariant (tys : ArchTypeFamily L)
    (g : AdelicGL2 (𝓞 L) L → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgconj : ∀ (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      g (rowIsometryInclAt₀ L w κ * x * (rowIsometryInclAt₀ L w κ)⁻¹) = g x)
    (u : AdelicGL2 (𝓞 L) L → ℂ) (huc : Continuous u) (hut : u ∈ archCutSubmodule L tys) :
    rightConv L u g ∈ archCutSubmodule L tys := by
  classical
  set μ : Measure (AdelicGL2 (𝓞 L) L) := adelicGLHaar (Fin 2) (𝓞 L) L with hμ

  set Λ : (AdelicGL2 (𝓞 L) L → ℂ) → (AdelicGL2 (𝓞 L) L → ℂ) := fun h x => ∫ y, h (x * y) * g y ∂μ with hΛ
  have hΛu : rightConv L u g = Λ u := by
    funext x; simp only [hΛ, rightConv_apply, hμ]
  have hint : ∀ h : AdelicGL2 (𝓞 L) L → ℂ, Continuous h → ∀ x, Integrable (fun y => h (x * y) * g y) μ :=
    fun h hh x => ((hh.comp (continuous_const.mul continuous_id)).mul hg).integrable_of_hasCompactSupport hgc.mul_left
  have hΛadd : ∀ h₁ h₂ : AdelicGL2 (𝓞 L) L → ℂ, Continuous h₁ → Continuous h₂ → Λ (h₁ + h₂) = Λ h₁ + Λ h₂ := by
    intro h₁ h₂ c₁ c₂
    funext x
    simp only [hΛ, Pi.add_apply]
    rw [← integral_add (hint h₁ c₁ x) (hint h₂ c₂ x)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have hΛsmul : ∀ (c : ℂ) (h : AdelicGL2 (𝓞 L) L → ℂ), Λ (c • h) = c • Λ h := by
    intro c h
    funext x
    simp only [hΛ, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring

  rw [mem_archCutSubmodule_iff]
  intro w
  set ι : ↥(rowIsometrySubgroup₀ w.Completion) →* AdelicGL2 (𝓞 L) L := rowIsometryInclAt₀ L w with hιdef
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    have h1 := congrArg (fun x => archComponent L w (glArch (𝓞 L) L x)) h
    simpa only [hιdef, rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply,
      glArch_adelicArchGLIncl, archComponent_archGLIncl_self] using h1

  have hgι : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (y : AdelicGL2 (𝓞 L) L), g ((ι k)⁻¹ * y) = g (y * (ι k)⁻¹) := by
    intro k y
    have := hgconj w k ((ι k)⁻¹ * y)
    rw [← mul_assoc, hιdef, mul_inv_cancel, one_mul] at this
    rw [hιdef]
    exact this.symm

  have hΛeq : ∀ (h : AdelicGL2 (𝓞 L) L → ℂ) (k : ↥(rowIsometrySubgroup₀ w.Completion)) (x : AdelicGL2 (𝓞 L) L),
      Λ (fun y => h (y * ι k)) x = Λ h (x * ι k) := by
    intro h k x
    simp only [hΛ]
    have hR : ∫ y, h (x * ι k * y) * g y ∂μ = ∫ y, h (x * y) * g (y * (ι k)⁻¹) ∂μ := by
      rw [← integral_mul_left_eq_self (μ := μ) (fun y => h (x * ι k * y) * g y) (ι k)⁻¹]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      show h (x * ι k * ((ι k)⁻¹ * y)) * g ((ι k)⁻¹ * y) = h (x * y) * g (y * (ι k)⁻¹)
      rw [← mul_assoc, mul_assoc x, mul_inv_cancel, mul_one, hgι]
    have hL : ∫ y, h (x * y * ι k) * g y ∂μ = ∫ y, h (x * y) * g (y * (ι k)⁻¹) ∂μ := by
      rw [← integral_mul_right_eq_self (μ := μ) (fun y => h (x * y * ι k) * g y) (ι k)⁻¹]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      show h (x * (y * (ι k)⁻¹) * ι k) * g (y * (ι k)⁻¹) = h (x * y) * g (y * (ι k)⁻¹)
      rw [← mul_assoc, inv_mul_cancel_right]
    rw [hL, hR]
  have hcut := (mem_archCutSubmodule_iff L tys u).mp hut w
  have hcut' : u ∈ Submodule.span ℂ (⋃ i : Fin (tys.card w),
      {φ : AdelicGL2 (𝓞 L) L → ℂ | ∃ T : (Fin (tys.rep w i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ),
        IsRightEquivariant ι (tys.rep w i).ρ T ∧ φ ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hcut
  obtain ⟨n, c, gen, hsum⟩ := Submodule.mem_span_set'.mp hcut'
  have hgen : ∀ j : Fin n, ∃ (i : Fin (tys.card w))
      (T : (Fin (tys.rep w i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ)) (v : Fin (tys.rep w i).n → ℂ),
      IsRightEquivariant ι (tys.rep w i).ρ T ∧ T v = (gen j : AdelicGL2 (𝓞 L) L → ℂ) := by
    intro j
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (gen j).2
    obtain ⟨T, hT, v, hv⟩ := hi
    exact ⟨i, T, v, hT, hv⟩
  choose idx Tj vj hTj hTv using hgen

  let W : Type := (j : Fin n) → (Fin (tys.rep w (idx j)).n → ℂ)
  let ρW : Representation ℂ ↥(rowIsometrySubgroup₀ w.Completion) W :=
    { toFun := fun k => LinearMap.pi fun j => ((tys.rep w (idx j)).ρ k).comp (LinearMap.proj j)
      map_one' := by
        apply LinearMap.ext; intro a; funext j
        show (tys.rep w (idx j)).ρ 1 (a j) = a j
        rw [map_one]; rfl
      map_mul' := fun k k' => by
        apply LinearMap.ext; intro a; funext j
        show (tys.rep w (idx j)).ρ (k * k') (a j) = (tys.rep w (idx j)).ρ k ((tys.rep w (idx j)).ρ k' (a j))
        rw [map_mul]; rfl }
  have ρW_apply : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W) (j : Fin n),
      ρW k a j = (tys.rep w (idx j)).ρ k (a j) := fun _ _ _ => rfl
  let TW : W →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ) := ∑ j, (Tj j).comp (LinearMap.proj j)
  have TW_apply : ∀ a : W, TW a = ∑ j, Tj j (a j) := fun a => by
    simp only [TW, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rfl
  have hTW : IsRightEquivariant ι ρW TW := by
    intro k a x
    rw [TW_apply, TW_apply, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ρW_apply]
    exact hTj j k (a j) x

  let Rk : ↥(rowIsometrySubgroup₀ w.Completion) → (AdelicGL2 (𝓞 L) L → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ) :=
    fun k => LinearMap.funLeft ℂ ℂ fun y : AdelicGL2 (𝓞 L) L => y * ι k
  let V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) :=
    Submodule.span ℂ (Set.range fun k : ↥(rowIsometrySubgroup₀ w.Completion) => Rk k u)
  have hVc : ∀ h ∈ V, Continuous h := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨k, rfl⟩ := hh
      exact huc.comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add h₁ h₂ _ _ ih₁ ih₂ => exact ih₁.add ih₂
    | smul a h _ ih => exact ih.const_smul a
  have hVstab : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)), ∀ h ∈ V, Rk k h ∈ V := by
    intro k h hh
    have hle : V.map (Rk k) ≤ V := by
      refine (Submodule.map_span_le _ _ _).mpr ?_
      rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      funext y
      show u (y * ι (k * k')) = u (y * ι k * ι k')
      rw [map_mul, mul_assoc]
    exact hle ⟨h, hh, rfl⟩

  let A : Submodule ℂ W := V.comap TW
  have hTWρ : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W), TW (ρW k a) = Rk k (TW a) :=
    fun k a => funext fun x => hTW k a x
  have hA : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W), a ∈ A → ρW k a ∈ A := fun k a ha => by
    show TW (ρW k a) ∈ V
    rw [hTWρ]
    exact hVstab k _ ha
  let TA : ↥A →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ) :=
    { toFun := fun a => Λ (TW a)
      map_add' := fun a b => by
        rw [Submodule.coe_add, map_add]
        exact hΛadd _ _ (hVc _ a.2) (hVc _ b.2)
      map_smul' := fun a x => by
        rw [Submodule.coe_smul, map_smul, RingHom.id_apply]
        exact hΛsmul a _ }
  have hTA : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : ↥A) (x : AdelicGL2 (𝓞 L) L),
      TA ⟨ρW k a, hA k a a.2⟩ x = TA a (x * ι k) := by
    intro k a x
    show Λ (TW (ρW k a)) x = Λ (TW a) (x * ι k)
    rw [hTWρ]
    exact hΛeq (TW a) k x
  obtain ⟨Text, hText, hTextA⟩ :=
    AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective ι hι ρW A hA TA hTA

  let a₀ : W := fun j => c j • vj j
  have hTWa₀ : TW a₀ = u := by
    rw [TW_apply, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Tj j (c j • vj j) = c j • (gen j : AdelicGL2 (𝓞 L) L → ℂ)
    rw [map_smul, hTv]
  have ha₀ : a₀ ∈ A := by
    show TW a₀ ∈ V
    rw [hTWa₀]
    refine Submodule.subset_span ⟨1, ?_⟩
    funext y
    show u (y * ι 1) = u y
    rw [map_one, mul_one]
  have hgoal : rightConv L u g = Text a₀ := by
    rw [hΛu, ← hTWa₀]
    have h := congrArg (fun f : ↥A →ₗ[ℂ] (AdelicGL2 (𝓞 L) L → ℂ) => f ⟨a₀, ha₀⟩) hTextA
    exact h.symm
  rw [hgoal, show a₀ = ∑ j, Pi.single j (a₀ j) from (Finset.univ_sum_single a₀).symm, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hTj' : IsRightEquivariant ι (tys.rep w (idx j)).ρ
      (Text.comp (LinearMap.single ℂ (fun j => Fin (tys.rep w (idx j)).n → ℂ) j)) := by
    intro k u' x
    show Text (Pi.single j ((tys.rep w (idx j)).ρ k u')) x = Text (Pi.single j u') (x * ι k)
    rw [← hText k (Pi.single j u') x]
    have hsingle : ρW k (Pi.single j u') = Pi.single j ((tys.rep w (idx j)).ρ k u') := by
      funext j'
      rw [ρW_apply]
      by_cases hj : j' = j
      · subst hj; simp only [Pi.single_eq_same]
      · simp only [Pi.single_eq_of_ne hj, map_zero]
    rw [hsingle]
  exact Submodule.mem_iSup_of_mem (idx j) (mem_typeSubmodule_of_isRightEquivariant hTj' (a₀ j))

end R4BlockConjL1
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_levelOne_of_conjInvariant_of_isFundamentalDomain_slab.R4BlockConjL1"

end
p2m_reactivate "P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_levelOne_of_conjInvariant_of_isFundamentalDomain_slab.R4BlockConjL1"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ S)
    (M : Ideal (𝓞 L)) (hM : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ M → w ∈ S)
    (tys : ArchTypeFamily L) (Ψ : HeckeEigensystem L ℂ)
    (g : AdelicGL2 (𝓞 L) L → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : IsBiInvariantUnder L (principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) g)
    (hgconj : ∀ (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      g (rowIsometryInclAt₀ L w κ * x * (rowIsometryInclAt₀ L w κ)⁻¹) = g x)
    (hgsupp : ∀ x : AdelicGL2 (𝓞 L) L, g x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L, glFin (𝓞 L) L u = glFin (𝓞 L) L x) :
    ∀ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N S Ψ ⊓ archCutSubmodule L tys,
      convOp L g u ∈ isotypicCuspSubmodule L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N S Ψ ⊓ archCutSubmodule L tys := by
  intro u hu
  obtain ⟨huV, hut⟩ := Submodule.mem_inf.mp hu
  rw [convOp_apply]
  by_cases h0 : u = 0
  · subst h0
    have hz : rightConv L (0 : AdelicGL2 (𝓞 L) L → ℂ) g = 0 := rightConv_zero_left L g
    rw [hz]
    exact Submodule.zero_mem _
  have hu' := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule L ΦL
    (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) ξL N S Ψ u huV h0
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  ·
    have hM0 : M ≠ ⊥ := R4BlockConjL1.ne_bot_of_forall_dvd_mem L S M hM
    haveI : Finite (↥(R4BlockConjL1.levelOneFin L N) ⧸ R4BlockConjL1.prinIn L N M) :=
      R4BlockConjL1.finite_quotient L N hM0
    letI : Fintype (↥(R4BlockConjL1.levelOneFin L N) ⧸ R4BlockConjL1.prinIn L N M) := Fintype.ofFinite _
    have huU : ∀ x : AdelicGL2 (𝓞 L) L, ∀ k ∈ R4BlockConjL1.levelOneFin L N, u (x * k) = u x :=
      hu'.level_invariant
    have hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
        (R4BlockConjL1.ravg L N M g) := by
      intro k hk y
      exact ⟨R4BlockConjL1.ravg_mul_apply L N M g hgU hgsupp ⟨k, hk⟩ y,
        R4BlockConjL1.ravg_apply_mul L N M g hgU ⟨k, hk⟩ y⟩
    have hconv :=
      AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_of_isFundamentalDomain_slab L α β ΦL
        hΦs hΦ ξL S N N hN hN Ψ (R4BlockConjL1.ravg L N M g) (R4BlockConjL1.continuous_ravg L N M g hg)
        (R4BlockConjL1.hasCompactSupport_ravg L N M g hgc) hbi u hu'
    have hcard : (Fintype.card (↥(R4BlockConjL1.levelOneFin L N) ⧸ R4BlockConjL1.prinIn L N M) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have heq : rightConv L u g =
        (Fintype.card (↥(R4BlockConjL1.levelOneFin L N) ⧸ R4BlockConjL1.prinIn L N M) : ℂ)⁻¹ •
          rightConv L u (R4BlockConjL1.ravg L N M g) := by
      funext x
      rw [Pi.smul_apply, smul_eq_mul, R4BlockConjL1.rightConv_ravg L N M g hg hgc u hu'.continuous huU x,
        ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    rw [heq]
    exact Submodule.smul_mem _ _ hconv.mem_isotypicCuspSubmodule
  · exact R4BlockConjL1.rightConv_mem_archCutSubmodule_of_conjInvariant L tys g hg hgc hgconj u hu'.continuous hut

end S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_levelOne_of_conjInvariant_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_levelOne_of_conjInvariant_of_isFundamentalDomain_slab (solution)
