-- Prove2me | solution 1 for AutomorphicForm.isRapidlyDecreasingOnSiegelSets_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9f7b3f29-88d2-5168-99b9-a41aea0e55e0

import Mathlib
import Theorems.Thm_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_rightConv_of_isCuspAutomorphicFnAt_of_norm_apply_eq_one_rat
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

noncomputable section

namespace KcTwistRapidTT2

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm IsDedekindDomain
open scoped ComplexConjugate

section Modulus

variable (K : Type) [Field K] [NumberField K]

def dm (g : AdelicGL2 (𝓞 K) K) : ℝ :=
  NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)

theorem dm_def (g : AdelicGL2 (𝓞 K) K) :
    dm K g = NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) := rfl

theorem dm_pos (g : AdelicGL2 (𝓞 K) K) : 0 < dm K g := NumberField.TateGlobal.ideleNorm_pos _

theorem dm_mul (g h : AdelicGL2 (𝓞 K) K) : dm K (g * h) = dm K g * dm K h := by
  rw [dm, map_mul, NumberField.TateGlobal.ideleNorm_mul]; rfl

theorem dm_one : dm K 1 = 1 := by
  have h := dm_mul K 1 1
  rw [mul_one] at h
  have hp := dm_pos K 1
  have : dm K 1 * (dm K 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hp.ne'
  · linarith

theorem dm_inv (g : AdelicGL2 (𝓞 K) K) : dm K g⁻¹ = (dm K g)⁻¹ := by
  have h := dm_mul K g g⁻¹
  rw [mul_inv_cancel, dm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem continuous_dm : Continuous (dm K) := NumberField.TateGlobal.continuous_ideleNorm_det K

theorem dm_eq_one_of_glArch_eq_one {X : AdelicGL2 (𝓞 K) K} (h1 : glArch (𝓞 K) K X = 1)
    (h2 : glFin (𝓞 K) K X ∈ finiteIntegralGL2 (𝓞 K) K) : dm K X = 1 := by
  rw [dm, NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K X h2]
  refine Finset.prod_eq_one fun w _ => ?_
  have : archDetNorm w X = 1 := by
    unfold archDetNorm
    rw [h1, map_one, Units.val_one, Matrix.det_one, norm_one]
  rw [this, one_pow]

def cw (w : ℝ) (g : AdelicGL2 (𝓞 K) K) : ℂ := (((dm K g) ^ (w / 2) : ℝ) : ℂ)

theorem cw_def (w : ℝ) (g : AdelicGL2 (𝓞 K) K) :
    cw K w g = (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ) :=
  rfl

theorem cw_mul (w : ℝ) (g h : AdelicGL2 (𝓞 K) K) : cw K w (g * h) = cw K w g * cw K w h := by
  rw [cw, dm_mul, Real.mul_rpow (dm_pos K g).le (dm_pos K h).le, Complex.ofReal_mul]; rfl

theorem cw_eq_one_of_dm {w : ℝ} {g : AdelicGL2 (𝓞 K) K} (h : dm K g = 1) : cw K w g = 1 := by
  rw [cw, h, Real.one_rpow, Complex.ofReal_one]

theorem cw_one (w : ℝ) : cw K w 1 = 1 := cw_eq_one_of_dm K (dm_one K)

theorem continuous_cw (w : ℝ) : Continuous (cw K w) :=
  Complex.continuous_ofReal.comp ((continuous_dm K).rpow_const fun g => Or.inl (dm_pos K g).ne')

theorem cw_ne_zero (w : ℝ) (g : AdelicGL2 (𝓞 K) K) : cw K w g ≠ 0 := by
  rw [cw, Complex.ofReal_ne_zero]
  exact (Real.rpow_pos_of_pos (dm_pos K g) _).ne'

end Modulus

section FinPart

variable (K : Type) [Field K] [NumberField K]

theorem cw_finEmbed_eq_one_of_mem (wt : ℝ) {k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hk : k ∈ finiteIntegralGL2 (𝓞 K) K) : cw K wt (AdelicDock.finEmbed (𝓞 K) K k) = 1 :=
  cw_eq_one_of_dm K (dm_eq_one_of_glArch_eq_one K (AdelicDock.glArch_finEmbed (𝓞 K) K k)
    (by rwa [AdelicDock.glFin_finEmbed]))

theorem isLocallyConstant_cw_finEmbed (wt : ℝ) :
    IsLocallyConstant (fun k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      cw K wt (AdelicDock.finEmbed (𝓞 K) K k)) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun k₀ => ?_
  refine ⟨{k | k₀⁻¹ * k ∈ finiteIntegralGL2 (𝓞 K) K}, ?_, ?_, ?_⟩
  · have hT : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
    exact (isOpen_finiteLevelZero (𝓞 K) K hT).preimage (continuous_const.mul continuous_id)
  · show k₀⁻¹ * k₀ ∈ finiteIntegralGL2 (𝓞 K) K
    rw [inv_mul_cancel]; exact Subgroup.one_mem _
  · intro k hk
    have hk' : k₀⁻¹ * k ∈ finiteIntegralGL2 (𝓞 K) K := hk
    have : k = k₀ * (k₀⁻¹ * k) := by rw [mul_inv_cancel_left]
    show cw K wt (AdelicDock.finEmbed (𝓞 K) K k) = cw K wt (AdelicDock.finEmbed (𝓞 K) K k₀)
    rw [this, map_mul, cw_mul, cw_finEmbed_eq_one_of_mem K wt hk', mul_one]

theorem isFinTestFactor_mul_cw (wt : ℝ) {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    (hff : IsFinTestFactor K ff) :
    IsFinTestFactor K (fun k => ff k * cw K wt (AdelicDock.finEmbed (𝓞 K) K k)) :=
  ⟨hff.1.mul (isLocallyConstant_cw_finEmbed K wt), hff.2.mul_right⟩

theorem cw_eq_cw_arch_mul_cw_fin (wt : ℝ) (g : AdelicGL2 (𝓞 K) K) :
    cw K wt g = cw K wt (adelicArchGLIncl K (glArch (𝓞 K) K g)) *
      cw K wt (AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K g)) := by
  set h : AdelicGL2 (𝓞 K) K :=
    adelicArchGLIncl K (glArch (𝓞 K) K g) * AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K g) with hh
  have hA : glArch (𝓞 K) K h = glArch (𝓞 K) K g := by
    rw [hh, map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
  have hF : glFin (𝓞 K) K h = glFin (𝓞 K) K g := by
    rw [hh, map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]
  have h1 : cw K wt (h⁻¹ * g) = 1 := by
    refine cw_eq_one_of_dm K (dm_eq_one_of_glArch_eq_one K ?_ ?_)
    · rw [map_mul, map_inv, hA, inv_mul_cancel]
    · rw [map_mul, map_inv, hF, inv_mul_cancel]; exact Subgroup.one_mem _
  calc cw K wt g = cw K wt (h * (h⁻¹ * g)) := by rw [mul_inv_cancel_left]
    _ = cw K wt h := by rw [cw_mul, h1, mul_one]
    _ = _ := by rw [hh, cw_mul]

end FinPart

section ArchPart

variable (K : Type) [Field K] [NumberField K]

open scoped Classical

local notation "GA" => GL (Fin 2) (InfiniteAdeleRing K)
local notation "MS" => (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)

def nA (y : GL (Fin 2) (InfiniteAdeleRing K)) : ℝ := dm K (adelicArchGLIncl K y)

theorem nA_pos (y : GA) : 0 < nA K y := dm_pos K _

theorem nA_eq_prod (y : GA) :
    nA K y = ∏ w : InfinitePlace K,
      ‖((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ w.mult := by
  have hint : glFin (𝓞 K) K (adelicArchGLIncl K y) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [glFin_adelicArchGLIncl]; exact Subgroup.one_mem _
  rw [nA, dm, NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K _ hint]
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold archDetNorm
  rw [glArch_adelicArchGLIncl]

def dR (i : {w : InfinitePlace K // w.IsReal}) (m : MS) : ℝ :=
  (m 0 0).1 i * (m 1 1).1 i - (m 0 1).1 i * (m 1 0).1 i

def dC (i : {w : InfinitePlace K // w.IsComplex}) (m : MS) : ℂ :=
  (m 0 0).2 i * (m 1 1).2 i - (m 0 1).2 i * (m 1 0).2 i

theorem contDiff_coordR (i : {w : InfinitePlace K // w.IsReal}) (a b : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun m : MS => (m a b).1 i) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : MS => m a b) := contDiff_apply_apply ℝ _ a b
  exact (contDiff_apply ℝ ℝ i).comp (contDiff_fst.comp h1)

theorem contDiff_coordC (i : {w : InfinitePlace K // w.IsComplex}) (a b : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun m : MS => (m a b).2 i) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : MS => m a b) := contDiff_apply_apply ℝ _ a b
  exact (contDiff_apply ℝ ℂ i).comp (contDiff_snd.comp h1)

theorem contDiff_dR (i : {w : InfinitePlace K // w.IsReal}) : ContDiff ℝ (⊤ : ℕ∞) (dR K i) :=
  ((contDiff_coordR K i 0 0).mul (contDiff_coordR K i 1 1)).sub
    ((contDiff_coordR K i 0 1).mul (contDiff_coordR K i 1 0))

theorem contDiff_dC (i : {w : InfinitePlace K // w.IsComplex}) : ContDiff ℝ (⊤ : ℕ∞) (dC K i) :=
  ((contDiff_coordC K i 0 0).mul (contDiff_coordC K i 1 1)).sub
    ((contDiff_coordC K i 0 1).mul (contDiff_coordC K i 1 0))

def sq (w : InfinitePlace K) (m : MS) : ℝ :=
  if hw : w.IsReal then (dR K ⟨w, hw⟩ m) ^ 2
  else ‖dC K ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ m‖ ^ 2

theorem contDiff_sq (w : InfinitePlace K) : ContDiff ℝ (⊤ : ℕ∞) (sq K w) := by
  by_cases hw : w.IsReal
  · have : sq K w = fun m => (dR K ⟨w, hw⟩ m) ^ 2 := funext fun m => dif_pos hw
    rw [this]
    exact (contDiff_dR K ⟨w, hw⟩).pow 2
  · have : sq K w = fun m => ‖dC K ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ m‖ ^ 2 :=
      funext fun m => dif_neg hw
    rw [this]
    exact (contDiff_norm_sq ℝ).comp (contDiff_dC K _)

omit [NumberField K] in
theorem det_archComponent (w : InfinitePlace K) (y : GA) :
    ((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det =
      (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 w *
          (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 w -
        (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 w *
          (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 w := by
  rw [Matrix.det_fin_two]
  rfl

omit [NumberField K] in
theorem sq_archEntries (w : InfinitePlace K) (y : GA) :
    sq K w (archEntries K y) =
      ‖((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2 := by
  by_cases hw : w.IsReal
  · rw [sq, dif_pos hw]
    have hd : dR K ⟨w, hw⟩ (archEntries K y) =
        NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
          ((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det := by
      rw [det_archComponent, map_sub, map_mul, map_mul]
      rfl
    rw [hd, ← sq_abs, ← Real.norm_eq_abs,
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _)]
  · rw [sq, dif_neg hw]
    have hd : dC K ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ (archEntries K y) =
        NumberField.InfinitePlace.Completion.extensionEmbedding w
          ((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det := by
      rw [det_archComponent, map_sub, map_mul, map_mul]
      rfl
    rw [hd, (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _)]

omit [NumberField K] in
theorem sq_archEntries_pos (w : InfinitePlace K) (y : GA) : 0 < sq K w (archEntries K y) := by
  rw [sq_archEntries]
  refine pow_pos (norm_pos_iff.mpr ?_) 2
  exact (Matrix.GeneralLinearGroup.det_ne_zero _)

def hS (wt : ℝ) (m : MS) : ℝ := ∏ w : InfinitePlace K, (sq K w m) ^ ((w.mult : ℝ) * wt / 4)

theorem contDiffAt_hS (wt : ℝ) {m : MS} (hm : ∀ w, sq K w m ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (hS K wt) m :=
  contDiffAt_prod fun w _ => ((contDiff_sq K w).contDiffAt).rpow_const_of_ne (hm w)

theorem hS_archEntries (wt : ℝ) (y : GA) : hS K wt (archEntries K y) = (nA K y) ^ (wt / 2) := by
  rw [nA_eq_prod, ← Real.finsetProd_rpow _ _ (fun w _ => pow_nonneg (norm_nonneg _) _)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [sq_archEntries]
  set a : ℝ := ‖((archComponent K w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖
  have ha : 0 ≤ a := norm_nonneg _
  rw [← Real.rpow_natCast a 2, ← Real.rpow_natCast a w.mult, ← Real.rpow_mul ha, ← Real.rpow_mul ha]
  congr 1
  push_cast
  ring

def U : Set MS := {m | ∀ w, sq K w m ≠ 0}

theorem isOpen_U : IsOpen (U K) := by
  have : U K = ⋂ w : InfinitePlace K, {m | sq K w m ≠ 0} := by
    ext m; simp [U]
  rw [this]
  exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (contDiff_sq K w).continuous continuous_const

omit [NumberField K] in
theorem archEntries_mem_U (y : GA) : archEntries K y ∈ U K := fun w => (sq_archEntries_pos K w y).ne'

omit [NumberField K] in
theorem continuous_archEntries : Continuous (archEntries K : GA → MS) :=
  continuous_pi fun i => continuous_pi fun j =>
    (AdelicBox.continuous_ringEquiv_mixedSpace (K := K)).comp (Units.continuous_val.matrix_elem i j)

theorem exists_bump {C : Set MS} (hC : IsCompact C) (hCU : C ⊆ U K) :
    ∃ b : MS → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ (∀ᶠ x in nhdsSet (U K)ᶜ, b x = 0) ∧ ∀ x ∈ C, b x = 1 := by
  have hd : Disjoint (U K)ᶜ C := by
    rw [Set.disjoint_left]
    intro x hx hxC
    exact hx (hCU hxC)
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (modelWithCornersSelf ℝ MS) (n := (⊤ : ℕ∞)) (isOpen_U K).isClosed_compl hC.isClosed hd
  refine ⟨f, ?_, hf0, fun x hx => hf1.self_of_nhdsSet x hx⟩
  exact contMDiff_iff_contDiff.mp f.contMDiff

theorem isArchTestFactor_mul_nA (wt : ℝ) {fa : GA → ℂ} (hfa : IsArchTestFactor K fa) :
    IsArchTestFactor K (fun y => fa y * (((nA K y) ^ (wt / 2) : ℝ) : ℂ)) := by
  obtain ⟨⟨Φ, hΦ, hrepr⟩, hsupp⟩ := hfa

  set C : Set MS := archEntries K '' tsupport fa with hC
  have hCc : IsCompact C := hsupp.image (continuous_archEntries K)
  have hCU : C ⊆ U K := by
    rintro _ ⟨y, -, rfl⟩
    exact archEntries_mem_U K y
  obtain ⟨b, hb, hb0, hb1⟩ := exists_bump K hCc hCU
  let ρ : MS → ℝ := fun m => b m * hS K wt m
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := by
    rw [contDiff_iff_contDiffAt]
    intro m
    by_cases hm : m ∈ U K
    · exact hb.contDiffAt.mul (contDiffAt_hS K wt hm)
    · have hev : ∀ᶠ x in nhds m, b x = 0 := hb0.filter_mono (nhds_le_nhdsSet hm)
      have hev' : ρ =ᶠ[nhds m] fun _ => 0 := hev.mono fun x hx => by
        show b x * hS K wt x = 0
        rw [hx, zero_mul]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev'
  refine ⟨⟨fun m => Φ m * ((ρ m : ℝ) : ℂ), hΦ.mul (Complex.ofRealCLM.contDiff.comp hρ), fun y => ?_⟩,
    hsupp.mul_right⟩
  by_cases hy : y ∈ tsupport fa
  · have h1 : b (archEntries K y) = 1 := hb1 _ ⟨y, hy, rfl⟩
    show fa y * (((nA K y) ^ (wt / 2) : ℝ) : ℂ) = Φ (archEntries K y) * ((ρ (archEntries K y) : ℝ) : ℂ)
    rw [← hrepr y]
    congr 2
    show nA K y ^ (wt / 2) = b (archEntries K y) * hS K wt (archEntries K y)
    rw [h1, one_mul, hS_archEntries]
  · have h0 : fa y = 0 := image_eq_zero_of_notMem_tsupport hy
    show fa y * (((nA K y) ^ (wt / 2) : ℝ) : ℂ) = Φ (archEntries K y) * ((ρ (archEntries K y) : ℝ) : ℂ)
    rw [← hrepr y, h0, zero_mul, zero_mul]

theorem cw_adelicArchGLIncl (wt : ℝ) (y : GA) :
    cw K wt (adelicArchGLIncl K y) = (((nA K y) ^ (wt / 2) : ℝ) : ℂ) := rfl

end ArchPart

section Assembly

variable (K : Type) [Field K] [NumberField K]

theorem isFactorizableTestFn_mul_cw (wt : ℝ) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : IsFactorizableTestFn K f) : IsFactorizableTestFn K (fun g => f g * cw K wt g) := by
  obtain ⟨fa, ff, hfa, hff, hrepr⟩ := hf
  refine ⟨fun y => fa y * (((nA K y) ^ (wt / 2) : ℝ) : ℂ),
    fun k => ff k * cw K wt (AdelicDock.finEmbed (𝓞 K) K k),
    isArchTestFactor_mul_nA K wt hfa, isFinTestFactor_mul_cw K wt hff, fun g => ?_⟩
  show f g * cw K wt g = _
  rw [hrepr g, cw_eq_cw_arch_mul_cw_fin K wt g, cw_adelicArchGLIncl]
  ring

end Assembly

section Conv

variable (K : Type) [Field K] [NumberField K]

open MeasureTheory NumberField.AdelicHaar NumberField.TateGlobal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

def nrm (e : ℝ) (g : AdelicGL2 (𝓞 K) K) : ℂ := (((ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ e : ℝ) : ℂ)

theorem nrm_def (e : ℝ) (g : AdelicGL2 (𝓞 K) K) :
    nrm K e g = (((ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ e : ℝ) : ℂ) := rfl

theorem nrm_pos' (g : AdelicGL2 (𝓞 K) K) : 0 < ideleNorm K (Matrix.GeneralLinearGroup.det g) := ideleNorm_pos _

theorem nrm_mul (e : ℝ) (g h : AdelicGL2 (𝓞 K) K) : nrm K e (g * h) = nrm K e g * nrm K e h := by
  rw [nrm, nrm, nrm, map_mul, ideleNorm_mul, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le,
    Complex.ofReal_mul]

theorem nrm_add (e e' : ℝ) (g : AdelicGL2 (𝓞 K) K) : nrm K e g * nrm K e' g = nrm K (e + e') g := by
  rw [nrm, nrm, nrm, ← Complex.ofReal_mul, ← Real.rpow_add (nrm_pos' K g)]

theorem nrm_zero (g : AdelicGL2 (𝓞 K) K) : nrm K 0 g = 1 := by
  rw [nrm, Real.rpow_zero, Complex.ofReal_one]

theorem nrm_eq_one_of {e : ℝ} {g : AdelicGL2 (𝓞 K) K} (h : ideleNorm K (Matrix.GeneralLinearGroup.det g) = 1) :
    nrm K e g = 1 := by
  rw [nrm, h, Real.one_rpow, Complex.ofReal_one]

theorem continuous_nrm (e : ℝ) : Continuous (nrm K e) :=
  Complex.continuous_ofReal.comp
    ((NumberField.TateGlobal.continuous_ideleNorm_det K).rpow_const fun g => Or.inl (nrm_pos' K g).ne')

theorem rightConv_twist (φ f : AdelicGL2 (𝓞 K) K → ℂ) (e e' : ℝ) (he : e + e' = 0) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K (fun x => φ x * nrm K e x) (fun x => f x * nrm K e' x) g = rightConv K φ f g * nrm K e g := by
  rw [rightConv_apply, rightConv_apply, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show φ (g * x) * nrm K e (g * x) * (f x * nrm K e' x) = φ (g * x) * f x * nrm K e g
  have h1 : nrm K e x * nrm K e' x = 1 := by rw [nrm_add, he, nrm_zero]
  calc φ (g * x) * nrm K e (g * x) * (f x * nrm K e' x)
      = φ (g * x) * f x * nrm K e g * (nrm K e x * nrm K e' x) := by rw [nrm_mul]; ring
    _ = φ (g * x) * f x * nrm K e g := by rw [h1, mul_one]

end Conv

section Cusp

variable (K : Type) [Field K] [NumberField K]

open MeasureTheory NumberField.AdelicHaar NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem det_unipotentGL2 (x : AdeleRing (𝓞 K) K) : Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 :=
  Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of])

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
  refine Units.ext ?_
  change Matrix.det (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K)) = (z : AdeleRing (𝓞 K) K) * z
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]

theorem nrm_centralScalar (e : ℝ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    nrm K e (centralScalar (𝓞 K) K z) = (((ideleNorm K z) ^ (2 * e) : ℝ) : ℂ) := by
  rw [nrm, det_centralScalar, ideleNorm_mul, Real.rpow_mul (ideleNorm_pos z).le, Real.rpow_two, pow_two]

def normRpowChar (r : ℝ) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ where
  toFun z := Units.mk0 ((((ideleNorm K z) ^ r : ℝ)) : ℂ)
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (ideleNorm_pos z) r).ne')
  map_one' := by
    refine Units.ext ?_
    simp [ideleNorm]
  map_mul' a b := by
    refine Units.ext ?_
    simp only [Units.val_mk0, Units.val_mul, ideleNorm_mul]
    rw [Real.mul_rpow (ideleNorm_pos a).le (ideleNorm_pos b).le, Complex.ofReal_mul]

theorem normRpowChar_apply (r : ℝ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((normRpowChar K r z : ℂˣ) : ℂ) = (((ideleNorm K z) ^ r : ℝ) : ℂ) := rfl

def shiftChar (Z : Subgroup (AdeleRing (𝓞 K) K)ˣ) (ξ : Z →* ℂˣ) (r : ℝ) : Z →* ℂˣ :=
  ξ * (normRpowChar K r).comp Z.subtype

theorem shiftChar_apply (Z : Subgroup (AdeleRing (𝓞 K) K)ˣ) (ξ : Z →* ℂˣ) (r : ℝ) (z : Z) :
    ((shiftChar K Z ξ r z : ℂˣ) : ℂ) = ((ξ z : ℂˣ) : ℂ) * ((((ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ)) ^ r : ℝ)) : ℂ) := by
  simp only [shiftChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, Units.val_mul,
    normRpowChar_apply]

theorem norm_shiftChar_top_eq_one (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ₀ r : ℝ) (h : σ₀ + r = 0)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = ideleNorm K x ^ σ₀)
    (z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) : ‖((shiftChar K ⊤ ξ r z : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ₀ := hσ₀ (z : (AdeleRing (𝓞 K) K)ˣ)
  rw [shiftChar_apply, norm_mul, h1, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (ideleNorm_pos _) _), ← Real.rpow_add (ideleNorm_pos _), h, Real.rpow_zero]

def slab (L U : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc L U}

theorem measurableSet_slab (L U : ℝ) : MeasurableSet (slab K L U) :=
  measurableSet_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det K).measurable

theorem memLp_two_mul_nrm {L U : ℝ} (hL : 0 < L) {t : Set (AdelicGL2 (𝓞 K) K)} (hts : t ⊆ slab K L U)
    (e : ℝ) {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : Continuous u)
    (h : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict t)) :
    MemLp (fun g => u g * nrm K e g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict t) := by
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  have hcont : Continuous fun g => u g * nrm K e g := hu.mul (continuous_nrm K e)
  set C : ℝ := max (L ^ (2 * e)) (U ^ (2 * e)) with hC
  have hbound : ∀ x ∈ slab K L U, (ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ (2 * e) ≤ C := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    by_cases hc : 0 ≤ 2 * e
    · exact (Real.rpow_le_rpow (nrm_pos' K x).le h2 hc).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hL h1 (le_of_lt (not_le.mp hc))).trans (le_max_left _ _)
  rw [← Measure.restrict_restrict_of_subset hts] at h ⊢
  have hsq : Integrable (fun x => ‖u x‖ ^ 2) ((μ.restrict (slab K L U)).restrict t) :=
    (memLp_two_iff_integrable_sq_norm h.1).1 h
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (hsq.const_mul C) ((hcont.norm.pow 2).aestronglyMeasurable) ?_
  have hae : ∀ᵐ x ∂((μ.restrict (slab K L U)).restrict t), x ∈ slab K L U :=
    ae_restrict_of_ae (ae_restrict_mem (measurableSet_slab K L U))
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_pow, abs_norm, norm_mul, mul_pow, nrm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (nrm_pos' K x) e)]
  have key : ((ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ e) ^ (2 : ℕ) =
      (ideleNorm K (Matrix.GeneralLinearGroup.det x)) ^ (2 * e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (nrm_pos' K x).le]
    congr 1
    push_cast
    ring
  rw [key, mul_comm]
  exact mul_le_mul_of_nonneg_right (hbound x hx) (pow_nonneg (norm_nonneg _) 2)

theorem ideleNorm_det_mem_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    {s : AdelicGL2 (𝓞 K) K} (hs : s ∈ centreCutSiegelSet K c u d₁ d₂) :
    d₁ ^ (∑ w : InfinitePlace K, w.mult) ≤ ideleNorm K (Matrix.GeneralLinearGroup.det s) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det s) ≤ d₂ ^ (∑ w : InfinitePlace K, w.mult) := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K s hs.1, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum]
  have hw := hs.2.2.2
  refine ⟨Finset.prod_le_prod (fun w _ => pow_nonneg hd₁.le _) fun w _ => ?_,
    Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w s).le _) fun w _ => ?_⟩
  · exact pow_le_pow_left₀ hd₁.le (hw w).1 _
  · exact pow_le_pow_left₀ (archDetNorm_pos w s).le (hw w).2 _

theorem exists_pinch_finset (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ T, m ≤ ideleNorm K (Matrix.GeneralLinearGroup.det x) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det x) ≤ m⁻¹ := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, le_rfl, fun x hx => (Finset.notMem_empty x hx).elim⟩
  | insert a T ha ih =>
    obtain ⟨m, hm0, hm1, hm⟩ := ih
    set N : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det a) with hN
    have hNpos : 0 < N := ideleNorm_pos _
    refine ⟨min m (min N N⁻¹), lt_min hm0 (lt_min hNpos (inv_pos.2 hNpos)), (min_le_left _ _).trans hm1, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · refine ⟨(min_le_right _ _).trans (min_le_left _ _), ?_⟩
      rw [← hN]
      have h1 : min m (min N N⁻¹) ≤ N⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
      have h2 : 0 < min m (min N N⁻¹) := lt_min hm0 (lt_min hNpos (inv_pos.2 hNpos))
      calc N = (N⁻¹)⁻¹ := (inv_inv N).symm
        _ ≤ (min m (min N N⁻¹))⁻¹ := inv_anti₀ h2 h1
    · obtain ⟨h1, h2⟩ := hm x hx
      refine ⟨(min_le_left _ _).trans h1, h2.trans ?_⟩
      exact inv_anti₀ (lt_min hm0 (lt_min hNpos (inv_pos.2 hNpos))) (min_le_left _ _)

theorem exists_window_subset_slab {c u d₁ d₂ : ℝ} (T : Finset (AdelicGL2 (𝓞 K) K)) (hd₁ : 0 < d₁) (hd : d₁ < d₂) :
    ∃ L U : ℝ, 0 < L ∧ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) ⊆ slab K L U := by
  obtain ⟨m, hm0, _, hm⟩ := exists_pinch_finset K T
  have hd₂ : 0 < d₂ := hd₁.trans hd
  refine ⟨d₁ ^ (∑ w : InfinitePlace K, w.mult) * m, d₂ ^ (∑ w : InfinitePlace K, w.mult) * m⁻¹,
    mul_pos (pow_pos hd₁ _) hm0, fun s hs => ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hs
  obtain ⟨x, hx, s₁, hs₁, rfl⟩ := hs
  obtain ⟨h1, h2⟩ := ideleNorm_det_mem_of_mem_centreCutSiegelSet K hd₁ hd hs₁
  obtain ⟨h3, h4⟩ := hm x hx
  show ideleNorm K (Matrix.GeneralLinearGroup.det (s₁ * x)) ∈ Set.Icc _ _
  rw [map_mul, ideleNorm_mul]
  exact ⟨mul_le_mul h1 h3 hm0.le (ideleNorm_pos _).le,
    mul_le_mul h2 h4 (ideleNorm_pos _).le (pow_nonneg hd₂.le _)⟩

theorem isCuspAutomorphicFnAt_mul_nrm (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)) (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (B : Set (AdeleRing (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (e : ℝ)
    (φ₁ : AdelicGL2 (𝓞 K) K → ℂ) (h3 : Continuous φ₁)
    (h4 : IsCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B) ξ φ₁) :
    IsCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B)
      (shiftChar K ⊤ ξ (2 * e)) (fun g => φ₁ g * nrm K e g) := by
  set D : Set (AdelicGL2 (𝓞 K) K) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂ with hD
  obtain ⟨hauto, hcusp⟩ := h4
  have h1 : LsXiMemberAt (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξ D φ₁ := hauto
  obtain ⟨hlsxi, hmem⟩ := (lsXiMemberAt_iff (𝓞 K) K _ ⊤ ξ D φ₁).1 h1

  have hlsxi' : IsLsXiFunction (𝓞 K) K ⊤ (shiftChar K ⊤ ξ (2 * e)) (fun g => φ₁ g * nrm K e g) := by
    refine ⟨fun γ x => ?_, fun z x => ?_⟩
    · show φ₁ (globalPoints (𝓞 K) K γ * x) * nrm K e (globalPoints (𝓞 K) K γ * x) = φ₁ x * nrm K e x
      rw [hlsxi.left_invariant, nrm_mul, nrm_eq_one_of K (AutomorphicForm.ideleNorm_det_globalPoints γ), one_mul]
    · show φ₁ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * x) *
          nrm K e (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * x) =
        ((shiftChar K ⊤ ξ (2 * e) z : ℂˣ) : ℂ) * (φ₁ x * nrm K e x)
      rw [hlsxi.central_transform z x, nrm_mul, nrm_centralScalar, shiftChar_apply]
      ring

  obtain ⟨L, U', hL, hDs⟩ := exists_window_subset_slab K (c := c) (u := u) T hd₁ hd
  have hmem' : MemLp (fun g => φ₁ g * nrm K e g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D) :=
    memLp_two_mul_nrm K hL hDs e h3 hmem

  have hcusp' : IsCuspidalFn (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) B) unipotentGL2
      (fun g => φ₁ g * nrm K e g) := by
    intro g
    have h0 : ∫ q, constantTermIntegrand unipotentGL2 φ₁ g q ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) B) = 0 :=
      hcusp g
    unfold constantTerm
    have hint : ∀ q, constantTermIntegrand unipotentGL2 (fun g => φ₁ g * nrm K e g) g q =
        constantTermIntegrand unipotentGL2 φ₁ g q * nrm K e g := by
      intro q
      show φ₁ (unipotentGL2 q * g) * nrm K e (unipotentGL2 q * g) = φ₁ (unipotentGL2 q * g) * nrm K e g
      rw [nrm_mul, nrm_eq_one_of K (by rw [det_unipotentGL2]; simp [ideleNorm]), one_mul]
    simp_rw [hint]
    rw [integral_mul_const, h0, zero_mul]
  exact ⟨(lsXiMemberAt_iff (𝓞 K) K _ ⊤ (shiftChar K ⊤ ξ (2 * e)) D _).2 ⟨hlsxi', hmem'⟩, hcusp'⟩

end Cusp

section Rat

open MeasureTheory NumberField.AdelicHaar NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LanglandsTunnell.RankinSelberg

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem main
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = ideleNorm ℚ x ^ σ₀)
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (h3 : Continuous φ₁) (h4 : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₁)
    (h4b : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁) :
    IsRapidlyDecreasingOnSiegelSets ℚ
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => φ₁ g * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-σ₀ / 2) : ℝ) : ℂ)) := by

  have hcov : CoversModCentre ℚ
      (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) :=
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
  obtain ⟨α, hα, hconv⟩ := h4b

  have hφ' : IsCuspAutomorphicFnAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1 / 2) 1 (1 / 2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      (shiftChar ℚ ⊤ ξ (2 * (-σ₀ / 2))) (fun g => φ₁ g * nrm ℚ (-σ₀ / 2) g) :=
    isCuspAutomorphicFnAt_mul_nrm ℚ (1 / 2) 1 (1 / 2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) _ _ _
      ξ (-σ₀ / 2) φ₁ h3 h4
  have hχu : ∀ z, ‖((shiftChar ℚ ⊤ ξ (2 * (-σ₀ / 2)) z : ℂˣ) : ℂ)‖ = 1 :=
    norm_shiftChar_top_eq_one ℚ ξ σ₀ (2 * (-σ₀ / 2)) (by ring) hσ₀

  have hf' : IsFactorizableTestFn ℚ (fun g => α g * cw ℚ σ₀ g) := isFactorizableTestFn_mul_cw ℚ σ₀ hα
  have hcont' : Continuous fun g => φ₁ g * nrm ℚ (-σ₀ / 2) g := h3.mul (continuous_nrm ℚ _)
  have key := AutomorphicForm.isRapidlyDecreasingOnSiegelSets_rightConv_of_isCuspAutomorphicFnAt_of_norm_apply_eq_one_rat
    (1 / 2) 1 (1 / 2) 2 (classRepTranslates ℚ) (by norm_num) hcov (shiftChar ℚ ⊤ ξ (2 * (-σ₀ / 2))) hχu
    (fun g => φ₁ g * nrm ℚ (-σ₀ / 2) g) hφ' hcont' (fun g => α g * cw ℚ σ₀ g) hf'
  have hconv' : rightConv ℚ (fun g => φ₁ g * nrm ℚ (-σ₀ / 2) g) (fun g => α g * cw ℚ σ₀ g) =
      fun g => φ₁ g * nrm ℚ (-σ₀ / 2) g := by
    funext g
    have hcw : (fun g => α g * cw ℚ σ₀ g) = fun g => α g * nrm ℚ (σ₀ / 2) g := rfl
    rw [hcw, rightConv_twist ℚ φ₁ α (-σ₀ / 2) (σ₀ / 2) (by ring) g, hconv]
  rw [hconv'] at key
  exact key

end Rat

end KcTwistRapidTT2

end

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀)
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (h3 : Continuous φ₁) (h4 : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₁)
    (h4b : (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁))
    (h6 : (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ₁ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ₁ g)) :
    IsRapidlyDecreasingOnSiegelSets ℚ
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => φ₁ g * ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-σ₀ / 2) : ℝ) : ℂ)) :=
  KcTwistRapidTT2.main ξ σ₀ hσ₀ φ₁ h3 h4 h4b

end S_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat
end P2MW
export P2MW.S_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_rat (solution)
