-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7f02bc21-dd96-55b6-a330-bd7d6ed02610

import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open NumberField.AdelicVolume

noncomputable section

namespace R4SiegelBound

theorem isCompact_units {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M] [T1Space M]
    {B B' : Set M} (hB : IsCompact B) (hB' : IsCompact B') :
    IsCompact {u : Mˣ | (u : M) ∈ B ∧ ((u⁻¹ : Mˣ) : M) ∈ B'} := by
  set S : Set Mˣ := {u : Mˣ | (u : M) ∈ B ∧ ((u⁻¹ : Mˣ) : M) ∈ B'} with hS
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have hset : Units.embedProduct M '' S =
      (B ×ˢ (MulOpposite.unop ⁻¹' B')) ∩ Set.range (Units.embedProduct M) := by
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨hu.1, hu.2⟩, u, rfl⟩
    · rintro ⟨hp, u, rfl⟩
      exact ⟨u, ⟨hp.1, hp.2⟩, rfl⟩
  rw [hset]
  refine IsCompact.inter_right (hB.prod ?_) Units.isClosedEmbedding_embedProduct.isClosed_range
  have : MulOpposite.unop ⁻¹' B' = MulOpposite.opHomeomorph '' B' := by
    ext p
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h; exact ⟨p.unop, h, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact hx
  rw [this]
  exact hB'.image MulOpposite.opHomeomorph.continuous

theorem isCompact_annulus {F : Type*} [NormedField F] [ProperSpace F] (a b : ℝ) :
    IsCompact {x : F | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
  have hsub : {x : F | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ⊆ Metric.closedBall 0 b := fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hx.2
  refine (isCompact_closedBall (0 : F) b).of_isClosed_subset ?_ hsub
  exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

variable {L : Type} [Field L] [NumberField L]

def Df (L : Type) [Field L] [NumberField L] : Set (FiniteAdeleRing (𝓞 L) L)ˣ :=
  {u | (u : FiniteAdeleRing (𝓞 L) L) ∈ integralFiniteAdeles (𝓞 L) L ∧
    ((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) ∈ integralFiniteAdeles (𝓞 L) L}

theorem isCompact_Df : IsCompact (Df L) :=
  isCompact_units (isCompact_integralFiniteAdeles (𝓞 L) L) (isCompact_integralFiniteAdeles (𝓞 L) L)

def Di (L : Type) [Field L] [NumberField L] (d₁ d₂ : ℝ) : Set (InfiniteAdeleRing L)ˣ :=
  {u | (u : InfiniteAdeleRing L) ∈ Set.univ.pi (fun w : InfinitePlace L => {x : w.Completion | d₁ ≤ ‖x‖ ∧ ‖x‖ ≤ d₂}) ∧
    ((u⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) ∈
      Set.univ.pi (fun w : InfinitePlace L => {x : w.Completion | d₂⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ d₁⁻¹})}

theorem isCompact_Di (d₁ d₂ : ℝ) : IsCompact (Di L d₁ d₂) := by
  refine isCompact_units (isCompact_univ_pi fun w => ?_) (isCompact_univ_pi fun w => ?_)
  · haveI := properSpace_completion (F := L) w
    exact isCompact_annulus d₁ d₂
  · haveI := properSpace_completion (F := L) w
    exact isCompact_annulus d₂⁻¹ d₁⁻¹

theorem det_fst_apply (g : AdelicGL2 (𝓞 L) L) (w : InfinitePlace L) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 w =
      ((archComponent L w (glArch (𝓞 L) L g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have h : (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).det).1 w =
      (((archEval L w).comp (adeleArch (𝓞 L) L)).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).det := by
    rw [← RingHom.map_det]; rfl
  rw [h]
  rfl

theorem det_snd (g : AdelicGL2 (𝓞 L) L) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 =
      ((glFin (𝓞 L) L g : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have h : (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).det).2 =
      ((adeleFin (𝓞 L) L).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).det := by
    rw [← RingHom.map_det]; rfl
  rw [h]
  rfl

theorem det_mem_integralFiniteAdeles {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (hm : ∀ i j, m i j ∈ integralFiniteAdeles (𝓞 L) L) : m.det ∈ integralFiniteAdeles (𝓞 L) L := by
  intro v
  rw [Matrix.det_fin_two, coe_sub_apply, coe_mul_apply, coe_mul_apply]
  exact sub_mem (mul_mem (hm 0 0 v) (hm 1 1 v)) (mul_mem (hm 0 1 v) (hm 1 0 v))

def P1 (L : Type) [Field L] [NumberField L] : (AdeleRing (𝓞 L) L)ˣ →* (InfiniteAdeleRing L)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def P2 (L : Type) [Field L] [NumberField L] : (AdeleRing (𝓞 L) L)ˣ →* (FiniteAdeleRing (𝓞 L) L)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def I1 (L : Type) [Field L] [NumberField L] : (InfiniteAdeleRing L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def I2 (L : Type) [Field L] [NumberField L] : (FiniteAdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem I1_mul_I2 (z : (AdeleRing (𝓞 L) L)ˣ) : I1 L (P1 L z) * I2 L (P2 L z) = z := by
  apply Units.ext
  show ((z : AdeleRing (𝓞 L) L).1, (1 : FiniteAdeleRing (𝓞 L) L)) * ((1 : InfiniteAdeleRing L), (z : AdeleRing (𝓞 L) L).2) = _
  rw [Prod.mk_mul_mk, mul_one, one_mul]
  rfl

theorem continuous_I1 : Continuous (I1 L) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

theorem continuous_I2 : Continuous (I2 L) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

theorem P2_det_mem_Df {c u d₁ d₂ : ℝ} {s : AdelicGL2 (𝓞 L) L} (hs : s ∈ centreCutSiegelSet L c u d₁ d₂) :
    P2 L (Matrix.GeneralLinearGroup.det s) ∈ Df L := by
  have hK := (mem_centreCutSiegelSet_iff.mp hs).1
  have hK' : glFin (𝓞 L) L s⁻¹ ∈ finiteIntegralGL2 (𝓞 L) L := by rw [map_inv]; exact inv_mem hK
  refine ⟨?_, ?_⟩
  · show ((Matrix.GeneralLinearGroup.det s : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 ∈ _
    rw [det_snd]
    exact det_mem_integralFiniteAdeles (mem_finiteIntegralGL2_iff.mp hK).1
  · show (((P2 L (Matrix.GeneralLinearGroup.det s))⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) ∈ _
    rw [← map_inv, ← map_inv]
    show ((Matrix.GeneralLinearGroup.det s⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 ∈ _
    rw [det_snd]
    exact det_mem_integralFiniteAdeles (mem_finiteIntegralGL2_iff.mp hK').1

theorem norm_P1_det_apply (s : AdelicGL2 (𝓞 L) L) (w : InfinitePlace L) :
    ‖((P1 L (Matrix.GeneralLinearGroup.det s) : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) w‖ = archDetNorm w s := by
  rw [show ((P1 L (Matrix.GeneralLinearGroup.det s) : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) w =
    ((Matrix.GeneralLinearGroup.det s : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 w from rfl, det_fst_apply]
  rfl

omit [NumberField L] in
theorem inv_P1_apply (a : (InfiniteAdeleRing L)ˣ) (w : InfinitePlace L) :
    ((a⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) w = (((a : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) w)⁻¹ := by
  have h1 : ((a⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) w * ((a : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) w = 1 :=
    congrArg (fun f : InfiniteAdeleRing L => f w) a.inv_mul
  exact eq_inv_of_mul_eq_one_left h1

theorem norm_apply_eq_one_of_mem_Df {b : (FiniteAdeleRing (𝓞 L) L)ˣ} (hb : b ∈ Df L) (v : HeightOneSpectrum (𝓞 L)) :
    ‖((b : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v‖ = 1 := by
  have h1 : Valued.v (((b : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hb.1 v)
  have h2 : Valued.v (((b⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hb.2 v)
  have hmul : ((b⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v *
      ((b : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v = 1 := by
    rw [← coe_mul_apply, Units.inv_mul, coe_one_apply]
  have hval : Valued.v (((b : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v) = 1 := by
    refine le_antisymm h1 ?_
    have h := congrArg Valued.v hmul
    rw [map_mul, map_one] at h

    have hle' : Valued.v (((b⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v) *
        Valued.v (((b : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v) ≤
        Valued.v (((b : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v) := by
      simpa only [one_mul] using
        mul_le_mul_left h2 (Valued.v (((b : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v))
    rwa [h] at hle'
  rw [NumberField.FinitePlace.norm_def, hval, map_one, NNReal.coe_one]

theorem ideleNorm_det_eq_prod {c u d₁ d₂ : ℝ} {s : AdelicGL2 (𝓞 L) L} (hs : s ∈ centreCutSiegelSet L c u d₁ d₂) :
    NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det s) = ∏ w : InfinitePlace L, archDetNorm w s ^ w.mult := by
  unfold NumberField.TateGlobal.ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm L]
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 L),
      ‖((Matrix.GeneralLinearGroup.det s : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => norm_apply_eq_one_of_mem_Df (P2_det_mem_Df hs) v
  rw [h2, mul_one]
  exact Finset.prod_congr rfl fun w _ => by rw [← norm_P1_det_apply]; rfl

theorem le_archDetNorm_of_le_ideleNorm {c u d₁ d₂ : ℝ} {s : AdelicGL2 (𝓞 L) L} (hs : s ∈ centreCutSiegelSet L c u d₁ d₂)
    {α₀ : ℝ} (hle : α₀ ≤ NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det s))
    (w₀ : InfinitePlace L) :
    min (α₀ / (max d₂ 1) ^ (∑ w : InfinitePlace L, w.mult)) 1 ≤ archDetNorm w₀ s := by
  classical
  set D : ℝ := max d₂ 1 with hD
  have hD1 : 1 ≤ D := le_max_right _ _
  have hD0 : 0 < D := lt_of_lt_of_le one_pos hD1
  have hdet := (mem_centreCutSiegelSet_iff.mp hs).2.2.2
  have hup : ∀ w : InfinitePlace L, archDetNorm w s ≤ D := fun w => (hdet w).2.trans (le_max_left _ _)
  have hpos : ∀ w : InfinitePlace L, 0 < archDetNorm w s := fun w => archDetNorm_pos w s

  set n : ℕ := ∑ w : InfinitePlace L, w.mult with hn
  have hrest : ∏ w ∈ Finset.univ.erase w₀, archDetNorm w s ^ w.mult ≤ D ^ n := by
    calc ∏ w ∈ Finset.univ.erase w₀, archDetNorm w s ^ w.mult
        ≤ ∏ w ∈ Finset.univ.erase w₀, D ^ w.mult :=
          Finset.prod_le_prod (fun w _ => pow_nonneg (hpos w).le _)
            (fun w _ => pow_le_pow_left₀ (hpos w).le (hup w) _)
      _ = D ^ (∑ w ∈ Finset.univ.erase w₀, w.mult) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ D ^ n := pow_le_pow_right₀ hD1 (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
  have hrest_pos : 0 < ∏ w ∈ Finset.univ.erase w₀, archDetNorm w s ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (hpos w) _
  have hprod : archDetNorm w₀ s ^ w₀.mult * ∏ w ∈ Finset.univ.erase w₀, archDetNorm w s ^ w.mult =
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det s) := by
    rw [ideleNorm_det_eq_prod hs]
    exact Finset.mul_prod_erase Finset.univ (fun w => archDetNorm w s ^ w.mult) (Finset.mem_univ w₀)

  have hpow : α₀ / D ^ n ≤ archDetNorm w₀ s ^ w₀.mult := by
    rw [div_le_iff₀ (pow_pos hD0 n)]
    calc α₀ ≤ NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det s) := hle
      _ = archDetNorm w₀ s ^ w₀.mult * ∏ w ∈ Finset.univ.erase w₀, archDetNorm w s ^ w.mult := hprod.symm
      _ ≤ archDetNorm w₀ s ^ w₀.mult * D ^ n :=
          mul_le_mul_of_nonneg_left hrest (pow_nonneg (hpos w₀).le _)

  by_cases hx1 : 1 ≤ archDetNorm w₀ s
  · exact (min_le_right _ _).trans hx1
  · push Not at hx1
    have hxle : archDetNorm w₀ s ^ w₀.mult ≤ archDetNorm w₀ s :=
      pow_le_of_le_one (hpos w₀).le hx1.le (by have := w₀.mult_pos; omega)
    exact (min_le_left _ _).trans (hpow.trans hxle)

theorem P1_det_mem_Di {c u d₁ d₂ : ℝ} {s : AdelicGL2 (𝓞 L) L} (hs : s ∈ centreCutSiegelSet L c u d₁ d₂)
    {α₀ : ℝ} (hα₀ : 0 < α₀) (hle : α₀ ≤ NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det s)) :
    P1 L (Matrix.GeneralLinearGroup.det s) ∈
      Di L (min (α₀ / (max d₂ 1) ^ (∑ w : InfinitePlace L, w.mult)) 1) (max d₂ 1) := by
  set ℓ : ℝ := min (α₀ / (max d₂ 1) ^ (∑ w : InfinitePlace L, w.mult)) 1 with hℓ
  have hdet := (mem_centreCutSiegelSet_iff.mp hs).2.2.2
  have hlow : ∀ w, ℓ ≤ archDetNorm w s := fun w => le_archDetNorm_of_le_ideleNorm hs hle w
  have hℓpos : 0 < ℓ := lt_min (div_pos hα₀ (pow_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _)) one_pos
  refine ⟨fun w _ => ?_, fun w _ => ?_⟩
  · rw [Set.mem_setOf_eq, norm_P1_det_apply]
    exact ⟨hlow w, (hdet w).2.trans (le_max_left _ _)⟩
  · rw [Set.mem_setOf_eq, inv_P1_apply, norm_inv, norm_P1_det_apply]
    have hpos : 0 < archDetNorm w s := archDetNorm_pos w s
    have hD : 0 < max d₂ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    exact ⟨(inv_le_inv₀ hD hpos).mpr ((hdet w).2.trans (le_max_left _ _)), (inv_le_inv₀ hpos hℓpos).mpr (hlow w)⟩

end R4SiegelBound

end

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel

open R4SiegelBound in
theorem solution
    (L : Type) [Field L] [NumberField L]
    (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hχ : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ))
    (α β : ℝ) (hα : 0 < α) (c u d₁ d₂ : ℝ)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) :
    ∃ M : ℝ, ∀ x ∈ {g : AdelicGL2 (𝓞 L) L |
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∩
          ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂,
      ‖chiDet (𝓞 L) L χ x‖ ≤ M := by

  obtain ⟨My', hMy'⟩ := hTc.exists_bound_of_continuousOn
    (NumberField.TateGlobal.continuous_ideleNorm_det L).continuousOn
  set My : ℝ := max My' 1 with hMy
  have hMypos : 0 < My := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMyle : ∀ y ∈ Tc, NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ≤ My := by
    intro y hy
    have h := hMy' y hy
    rw [Real.norm_eq_abs, abs_of_pos (NumberField.TateGlobal.ideleNorm_pos _)] at h
    exact h.trans (le_max_left _ _)
  set α₀ : ℝ := α / My with hα₀
  have hα₀pos : 0 < α₀ := div_pos hα hMypos

  set ℓ : ℝ := min (α₀ / (max d₂ 1) ^ (∑ w : InfinitePlace L, w.mult)) 1 with hℓ
  have hc1 : Continuous fun a : (InfiniteAdeleRing L)ˣ => ((χ (I1 L a) : ℂˣ) : ℂ) := hχ.comp continuous_I1
  have hc2 : Continuous fun b : (FiniteAdeleRing (𝓞 L) L)ˣ => ((χ (I2 L b) : ℂˣ) : ℂ) := hχ.comp continuous_I2
  have hc3 : Continuous (chiDet (𝓞 L) L χ) := hχ.comp Matrix.GeneralLinearGroup.continuous_det
  obtain ⟨A₁, hA₁⟩ := (isCompact_Di (L := L) ℓ (max d₂ 1)).exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨A₂, hA₂⟩ := (isCompact_Df (L := L)).exists_bound_of_continuousOn hc2.continuousOn
  obtain ⟨A₃, hA₃⟩ := hTc.exists_bound_of_continuousOn hc3.continuousOn
  refine ⟨max A₁ 0 * max A₂ 0 * max A₃ 0, fun x hx => ?_⟩
  obtain ⟨hxslab, hx⟩ := hx
  simp only [Set.mem_iUnion, Set.mem_image] at hx
  obtain ⟨y, hy, s, hs, rfl⟩ := hx

  have hle : α₀ ≤ NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det s) := by
    have h1 : α ≤ NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det s) *
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) := by
      have h := hxslab.1
      rwa [map_mul, NumberField.TateGlobal.ideleNorm_mul] at h
    rw [hα₀, div_le_iff₀ hMypos]
    exact h1.trans (mul_le_mul_of_nonneg_left (hMyle y hy) (NumberField.TateGlobal.ideleNorm_pos _).le)
  have hdet : chiDet (𝓞 L) L χ (s * y) =
      ((χ (I1 L (P1 L (Matrix.GeneralLinearGroup.det s))) : ℂˣ) : ℂ) *
        ((χ (I2 L (P2 L (Matrix.GeneralLinearGroup.det s))) : ℂˣ) : ℂ) * chiDet (𝓞 L) L χ y := by
    have e : Matrix.GeneralLinearGroup.det s =
        I1 L (P1 L (Matrix.GeneralLinearGroup.det s)) * I2 L (P2 L (Matrix.GeneralLinearGroup.det s)) :=
      (I1_mul_I2 _).symm
    show ((χ (Matrix.GeneralLinearGroup.det (s * y)) : ℂˣ) : ℂ) = _ * ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)
    rw [map_mul Matrix.GeneralLinearGroup.det, map_mul χ, Units.val_mul]
    conv_lhs => rw [e, map_mul χ, Units.val_mul]
  rw [hdet, norm_mul, norm_mul]
  have h1 := (hA₁ _ (P1_det_mem_Di hs hα₀pos hle)).trans (le_max_left A₁ 0)
  have h2 := (hA₂ _ (P2_det_mem_Df hs)).trans (le_max_left A₂ 0)
  have h3 := (hA₃ y hy).trans (le_max_left A₃ 0)
  exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)) h3 (norm_nonneg _)
    (mul_nonneg (le_max_right _ _) (le_max_right _ _))

end S_AutomorphicForm_exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet (solution)
