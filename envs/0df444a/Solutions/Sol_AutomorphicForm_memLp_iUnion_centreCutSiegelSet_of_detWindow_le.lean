-- Prove2me | solution 1 for AutomorphicForm.memLp_iUnion_centreCutSiegelSet_of_detWindow_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1efb9960-c484-5b10-9bdc-e605bb28a5aa

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le

set_option autoImplicit false

noncomputable section

namespace Ws23
namespace V2E

open MeasureTheory
open scoped ENNReal

section Generic

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

omit [MeasurableSpace G] [MeasurableMul G] in
theorem image_mul_left_eq_preimage (z : G) (A : Set G) :
    (fun x => z * x) '' A = (fun x => z⁻¹ * x) ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨z⁻¹ * x, hx, by simp⟩

theorem measurableSet_image_mul_left (z : G) {A : Set G} (hA : MeasurableSet A) :
    MeasurableSet ((fun x => z * x) '' A) := by
  rw [image_mul_left_eq_preimage]
  exact measurable_const_mul _ hA

theorem setLIntegral_image_mul_left (μ : Measure G) [μ.IsMulLeftInvariant]
    (f : G → ℝ≥0∞) (z : G) (r : ℝ≥0∞) (hr : r ≠ ∞) (hf : ∀ x, f (z * x) = r * f x)
    {A : Set G} (hA : MeasurableSet A) :
    ∫⁻ x in (fun x => z * x) '' A, f x ∂μ = r * ∫⁻ x in A, f x ∂μ := by
  have hmeas := measurableSet_image_mul_left z hA
  have hind : ∀ x, ((fun x => z * x) '' A).indicator f (z * x) = r * A.indicator f x := by
    intro x
    by_cases hx : x ∈ A
    · have hx' : z * x ∈ (fun x => z * x) '' A := ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, hf]
    · have hx' : z * x ∉ (fun x => z * x) '' A := by
        rintro ⟨y, hy, hyx⟩
        exact hx (mul_left_cancel hyx ▸ hy)
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
  rw [← lintegral_indicator hmeas, ← lintegral_indicator hA,
    ← lintegral_mul_left_eq_self (fun x => ((fun x => z * x) '' A).indicator f x) z]
  simp only [hind]
  rw [lintegral_const_mul' _ _ hr]

end Generic

section Tsum

theorem tsum_prod_pow_le {ι : Type*} [Fintype ι] (q : ι → ℝ≥0∞) :
    ∑' n : ι → ℕ, ∏ i, q i ^ n i ≤ ∏ i, ∑' k : ℕ, q i ^ k := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set N : ℕ := s.sup fun n => Finset.univ.sup n with hN
  have hs : s ⊆ Fintype.piFinset fun _ : ι => Finset.range (N + 1) := by
    intro n hn
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le ?_)
    calc n i ≤ Finset.univ.sup n := Finset.le_sup (f := n) (Finset.mem_univ i)
      _ ≤ N := Finset.le_sup (f := fun n => Finset.univ.sup n) hn
  calc ∑ n ∈ s, ∏ i, q i ^ n i ≤ ∑ n ∈ Fintype.piFinset fun _ : ι => Finset.range (N + 1), ∏ i, q i ^ n i :=
        Finset.sum_le_sum_of_subset hs
    _ = ∏ i, ∑ k ∈ Finset.range (N + 1), q i ^ k := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' k : ℕ, q i ^ k := Finset.prod_le_prod' fun i _ => ENNReal.sum_le_tsum _

theorem tsum_prod_pow_lt_top {ι : Type*} [Fintype ι] (q : ι → ℝ≥0∞) (hq : ∀ i, q i < 1) :
    ∑' n : ι → ℕ, ∏ i, q i ^ n i < ⊤ := by
  refine (tsum_prod_pow_le q).trans_lt ?_
  refine ENNReal.prod_lt_top fun i _ => ?_
  rw [ENNReal.tsum_geometric]
  exact ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 (hq i))

end Tsum

end Ws23.V2E

end

noncomputable section

namespace Ws23
namespace V2E

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.InfinitePlace
open scoped ENNReal

section Adelic

variable {F : Type} [Field F] [NumberField F]

def archUnitIdele : ((v : InfinitePlace F) → (v.Completion)ˣ) →* (AdeleRing (𝓞 F) F)ˣ where
  toFun b :=
    { val := ((fun v => (b v : v.Completion) : InfiniteAdeleRing F), 1)
      inv := ((fun v => ((b v)⁻¹ : (v.Completion)ˣ) : InfiniteAdeleRing F), 1)
      val_inv := by
        refine Prod.ext (funext fun v => ?_) (one_mul 1)
        show (b v : v.Completion) * ((b v)⁻¹ : (v.Completion)ˣ) = 1
        rw [Units.mul_inv]
      inv_val := by
        refine Prod.ext (funext fun v => ?_) (one_mul 1)
        show ((b v)⁻¹ : (v.Completion)ˣ) * (b v : v.Completion) = 1
        rw [Units.inv_mul] }
  map_one' := by
    apply Units.ext
    refine Prod.ext (funext fun v => ?_) rfl
    show ((1 : (v.Completion)ˣ) : v.Completion) = 1
    rw [Units.val_one]
  map_mul' b b' := by
    apply Units.ext
    refine Prod.ext (funext fun v => ?_) (one_mul 1).symm
    show ((b v * b' v : (v.Completion)ˣ) : v.Completion) = (b v : v.Completion) * (b' v : v.Completion)
    rw [Units.val_mul]

theorem archUnitIdele_fst (b : (v : InfinitePlace F) → (v.Completion)ˣ) (v : InfinitePlace F) :
    ((archUnitIdele b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v = (b v : v.Completion) := rfl

theorem archUnitIdele_snd (b : (v : InfinitePlace F) → (v.Completion)ˣ) :
    ((archUnitIdele b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl

open scoped Classical in
theorem archCentralUnit_eq_archUnitIdele (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    archCentralUnit F w a = archUnitIdele (Pi.mulSingle w a) := by
  apply Units.ext
  refine Prod.ext (funext fun v => ?_) rfl
  show Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion) v
    = ((Pi.mulSingle (M := fun v : InfinitePlace F => (v.Completion)ˣ) w a v : (v.Completion)ˣ) : v.Completion)
  by_cases hv : v = w
  · subst hv
    rw [Function.update_self, Pi.mulSingle_eq_same]
  · rw [Function.update_of_ne hv, Pi.mulSingle_eq_of_ne hv, Units.val_one]
    rfl

theorem archUnitIdele_pow_eq_prod (a : (v : InfinitePlace F) → (v.Completion)ˣ) (n : InfinitePlace F → ℕ) :
    archUnitIdele (fun v => a v ^ n v) = ∏ v, (archCentralUnit F v (a v)) ^ n v := by
  classical
  have : (fun v => a v ^ n v) = ∏ v, Pi.mulSingle v (a v ^ n v) := (Finset.univ_prod_mulSingle _).symm
  rw [this, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [archCentralUnit_eq_archUnitIdele, ← map_pow, Pi.mulSingle_pow]

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (h : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * h = h * centralScalar (𝓞 F) F z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 F) F) (fun _ => Commute.all _ _) _).eq

theorem archDetNorm_centralScalar_mul' (v : InfinitePlace F) (w : (AdeleRing (𝓞 F) F)ˣ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (centralScalar (𝓞 F) F w * g)
      = (‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖) * archDetNorm v g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  set s := archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F w))
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) v.Completion) i j
      = if i = j then (w : AdeleRing (𝓞 F) F).1 v else 0 := by
    intro i j
    simp only [s, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, if_pos rfl]
    · rw [centralScalar_apply_ne _ h, if_neg h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

theorem centralScalar_mul_mem_centreCutSiegelSet {c u d₁ d₂ e₁ e₂ : ℝ} {w : (AdeleRing (𝓞 F) F)ˣ}
    (hwf : (w : AdeleRing (𝓞 F) F).2 = 1) (hwa : ∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂)
    (hdet : ∀ v : InfinitePlace F,
      (‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖) * archDetNorm v g ∈ Set.Icc e₁ e₂) :
    centralScalar (𝓞 F) F w * g ∈ centreCutSiegelSet F c u e₁ e₂ := by
  obtain ⟨h1, h2, h3, -⟩ := hg
  set s := centralScalar (𝓞 F) F w with hs
  have h00 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = w := centralScalar_apply_eq w 0
  have h01 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0 := centralScalar_apply_ne w (by decide)
  have h10 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := centralScalar_apply_ne w (by decide)
  have h11 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = w := centralScalar_apply_eq w 1
  have hglFin : glFin (𝓞 F) F s = 1 := glFin_scalar_eq_one F hwf h00 h01 h10 h11
  have hcomp00 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 0 0 = (w : AdeleRing (𝓞 F) F).1 v := fun v => by
    rw [archComponent_apply, glArch_apply, h00]
  have hcomp01 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 0 1 = 0 := fun v => by
    rw [archComponent_apply, glArch_apply, h01]; rfl
  have hcomp10 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 1 0 = 0 := fun v => by
    rw [archComponent_apply, glArch_apply, h10]; rfl
  have hcomp11 : ∀ v : InfinitePlace F, ((archComponent F v (glArch (𝓞 F) F s) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) 1 1 = (w : AdeleRing (𝓞 F) F).1 v := fun v => by
    rw [archComponent_apply, glArch_apply, h11]
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [map_mul, hglFin, one_mul]
    exact h1
  · rw [map_mul, map_mul, localHeight_scalar_entries_mul (hwa v) (hcomp00 v) (hcomp01 v) (hcomp10 v) (hcomp11 v)]
    exact h2 v
  · rw [map_mul, map_mul, xWindowSq_scalar_entries_mul (hwa v) (hcomp00 v) (hcomp01 v) (hcomp10 v) (hcomp11 v)]
    exact h3 v
  · rw [hs, archDetNorm_centralScalar_mul']
    exact hdet v

theorem archDetNorm_mul (v : InfinitePlace F) (g x : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (g * x) = archDetNorm v g * archDetNorm v x := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

omit [NumberField F] in

theorem exists_norm_eq (v : InfinitePlace F) {r : ℝ} (hr : 0 ≤ r) : ∃ a : v.Completion, ‖a‖ = r := by
  rcases v.isReal_or_isComplex with hv | hv
  · obtain ⟨a, ha⟩ := Completion.surjective_extensionEmbeddingOfIsReal hv r
    refine ⟨a, ?_⟩
    rw [← (Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) a, ha,
      Real.norm_of_nonneg hr]
  · obtain ⟨a, ha⟩ := Completion.surjective_extensionEmbedding_of_isComplex hv (r : ℂ)
    refine ⟨a, ?_⟩
    rw [← (Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) a, ha,
      Complex.norm_real, Real.norm_of_nonneg hr]

theorem measurableSet_iUnion_centreCutSiegelSet (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) :
    letI := glBorel (Fin 2) (𝓞 F) F;
    MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
  letI := glBorel (Fin 2) (𝓞 F) F
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine MeasurableSet.biUnion T.countable_toSet fun x _ => ?_
  have himg : (· * x) '' centreCutSiegelSet F c u d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet F c u d₁ d₂ := by
    ext g; simp [Set.mem_preimage]
  rw [himg]
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).preimage (measurable_mul_const x⁻¹)

end Adelic

end Ws23.V2E

end

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel MeasureTheory

open NumberField.AdelicVolume
open scoped ENNReal

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ dp : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hdp : 0 < dp) (hdp₂ : dp < d₂) (hd₁ : d₁ ≤ dp)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφm : letI := glBorel (Fin 2) (𝓞 F) F; AEStronglyMeasurable φ (adelicGLHaar (Fin 2) (𝓞 F) F))
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hω : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g)
    (hcontr : d₁ ≤ 0 → ∀ (w : InfinitePlace F) (a : (w.Completion)ˣ), ‖(a : w.Completion)‖ < 1 →
      ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1)
    (hL2 : letI := glBorel (Fin 2) (𝓞 F) F;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂))) :
    letI := glBorel (Fin 2) (𝓞 F) F;
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  classical
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  haveI : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : MeasurableMul (AdelicGL2 (𝓞 F) F) :=
    ⟨fun g => (continuous_const_mul g).measurable, fun g => (continuous_mul_const g).measurable⟩
  set Dp : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂ with hDp
  set D : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ with hD
  have hDpm : MeasurableSet Dp := Ws23.V2E.measurableSet_iUnion_centreCutSiegelSet c u dp d₂ T
  set f : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => ‖φ g‖ₑ ^ 2 with hf
  have hfz : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      f (centralScalar (𝓞 F) F z * g) = ‖((ω z : ℂˣ) : ℂ)‖ₑ ^ 2 * f g := by
    intro z g
    simp only [hf, hω, enorm_mul, mul_pow]

  have hIp : ∫⁻ g in Dp, f g ∂μ < ⊤ := by
    have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞)) (f := φ)
      (μ := μ.restrict Dp) two_ne_zero ENNReal.ofNat_ne_top hL2.eLpNorm_lt_top
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at h2
    exact h2

  suffices hfin : ∫⁻ g in D, f g ∂μ < ⊤ by
    refine ⟨hφm.restrict, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

  set ρ : ℝ := dp / d₂ with hρ
  have hd₂ : 0 < d₂ := hdp.trans hdp₂
  have hρ0 : 0 < ρ := div_pos hdp hd₂
  have hρ1 : ρ < 1 := (div_lt_one hd₂).mpr hdp₂
  have hunit : ∀ v : InfinitePlace F, ∃ a : (v.Completion)ˣ, ‖(a : v.Completion)‖ = Real.sqrt ρ := by
    intro v
    obtain ⟨a, ha⟩ := Ws23.V2E.exists_norm_eq v (Real.sqrt_nonneg ρ)
    have ha0 : a ≠ 0 := by
      rw [← norm_pos_iff, ha]
      exact Real.sqrt_pos.mpr hρ0
    exact ⟨Units.mk0 a ha0, ha⟩
  choose a ha using hunit
  have ha2 : ∀ v, ‖(a v : v.Completion)‖ * ‖(a v : v.Completion)‖ = ρ := fun v => by
    rw [ha, Real.mul_self_sqrt hρ0.le]
  have ha1 : ∀ v, ‖(a v : v.Completion)‖ < 1 := fun v => by
    rw [ha, Real.sqrt_lt' one_pos, one_pow]
    exact hρ1

  set zι : (InfinitePlace F → ℕ) → (AdeleRing (𝓞 F) F)ˣ := fun n => Ws23.V2E.archUnitIdele fun v => a v ^ n v
    with hzι
  set B : (InfinitePlace F → ℕ) → Set (AdelicGL2 (𝓞 F) F) := fun n =>
    (fun g => centralScalar (𝓞 F) F (zι n) * g) '' Dp with hB
  have hBm : ∀ n, MeasurableSet (B n) := fun n => Ws23.V2E.measurableSet_image_mul_left _ hDpm
  have hBmass : ∀ n, ∫⁻ g in B n, f g ∂μ = ‖((ω (zι n) : ℂˣ) : ℂ)‖ₑ ^ 2 * ∫⁻ g in Dp, f g ∂μ := fun n =>
    Ws23.V2E.setLIntegral_image_mul_left μ f (centralScalar (𝓞 F) F (zι n)) _
      (ENNReal.pow_ne_top enorm_ne_top) (hfz (zι n)) hDpm

  set q : InfinitePlace F → ℝ≥0∞ := fun v => ‖((ω (AdelicVolume.archCentralUnit F v (a v)) : ℂˣ) : ℂ)‖ₑ ^ 2 with hq
  have hmult : ∀ n, ‖((ω (zι n) : ℂˣ) : ℂ)‖ₑ ^ 2 = ∏ v, q v ^ n v := by
    intro n
    have hnn : ‖((ω (zι n) : ℂˣ) : ℂ)‖₊ = ∏ v, ‖((ω (AdelicVolume.archCentralUnit F v (a v)) : ℂˣ) : ℂ)‖₊ ^ n v := by
      rw [hzι]
      show ‖((ω (Ws23.V2E.archUnitIdele fun v => a v ^ n v) : ℂˣ) : ℂ)‖₊ = _
      rw [Ws23.V2E.archUnitIdele_pow_eq_prod, map_prod, Units.coe_prod, nnnorm_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_pow, Units.val_pow_eq_pow_val, nnnorm_pow]
    simp only [hq, enorm_eq_nnnorm, hnn, ENNReal.coe_finsetProd, ENNReal.coe_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul, mul_comm, pow_mul]

  have hcover : ∀ g ∈ D, ∃ n : InfinitePlace F → ℕ, g ∈ B n ∧ ∀ v, d₁ ≤ ρ ^ n v * d₂ := by
    intro g hg
    obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_iUnion₂.mp hg
    have hsdet := fun v => (mem_centreCutSiegelSet_iff.mp hs).2.2.2 v

    have hex : ∀ v, ∃ k : ℕ, ρ ^ (k + 1) < archDetNorm v s / d₂ ∧ archDetNorm v s / d₂ ≤ ρ ^ k := fun v =>
      exists_nat_pow_near_of_lt_one (div_pos (archDetNorm_pos v s) hd₂)
        ((div_le_one hd₂).mpr (hsdet v).2) hρ0 hρ1
    choose n hn using hex
    refine ⟨n, ?_, fun v => ?_⟩
    ·
      have hzinv : (zι n)⁻¹ = Ws23.V2E.archUnitIdele (fun v => (a v ^ n v)⁻¹) := by
        rw [hzι, ← map_inv]
        rfl
      refine ⟨centralScalar (𝓞 F) F (zι n)⁻¹ * (s * x), ?_, ?_⟩
      · refine Set.mem_iUnion₂.mpr ⟨x, hx, centralScalar (𝓞 F) F (zι n)⁻¹ * s, ?_, mul_assoc _ _ _⟩
        rw [hzinv]
        refine Ws23.V2E.centralScalar_mul_mem_centreCutSiegelSet (Ws23.V2E.archUnitIdele_snd _)
          (fun v => ?_) hs (fun v => ?_)
        · rw [Ws23.V2E.archUnitIdele_fst]
          exact Units.ne_zero _
        · rw [Ws23.V2E.archUnitIdele_fst, Units.val_inv_eq_inv_val, norm_inv, Units.val_pow_eq_pow_val, norm_pow,
            ← mul_inv, ← pow_add, ← two_mul, pow_mul, sq, ha2]
          obtain ⟨h1, h2⟩ := hn v
          have hpos := archDetNorm_pos v s
          have hρn : 0 < ρ ^ n v := pow_pos hρ0 _
          constructor
          · rw [le_inv_mul_iff₀ hρn]
            have : ρ ^ (n v + 1) * d₂ < archDetNorm v s := (lt_div_iff₀ hd₂).mp h1
            calc ρ ^ n v * dp = ρ ^ (n v + 1) * d₂ := by rw [hρ, pow_succ]; field_simp
              _ ≤ archDetNorm v s := this.le
          · rw [inv_mul_le_iff₀ hρn]
            rwa [← div_le_iff₀ hd₂]
      · show centralScalar (𝓞 F) F (zι n) * (centralScalar (𝓞 F) F (zι n)⁻¹ * (s * x)) = s * x
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    ·
      obtain ⟨-, h2⟩ := hn v
      calc d₁ ≤ archDetNorm v s := (hsdet v).1
        _ ≤ ρ ^ n v * d₂ := by rwa [← div_le_iff₀ hd₂]

  set S : Set (InfinitePlace F → ℕ) := {n | ∀ v, d₁ ≤ ρ ^ n v * d₂} with hS
  have hDsub : D ⊆ ⋃ n ∈ S, B n := by
    intro g hg
    obtain ⟨n, hgn, hnS⟩ := hcover g hg
    exact Set.mem_iUnion₂.mpr ⟨n, hnS, hgn⟩

  set B' : (InfinitePlace F → ℕ) → Set (AdelicGL2 (𝓞 F) F) := fun n => if n ∈ S then B n else ∅ with hB'
  have hB'sub : (⋃ n ∈ S, B n) ⊆ ⋃ n, B' n := by
    intro g hg
    obtain ⟨n, hn, hgn⟩ := Set.mem_iUnion₂.mp hg
    exact Set.mem_iUnion.mpr ⟨n, by simp only [hB', if_pos hn]; exact hgn⟩
  have hle : ∫⁻ g in D, f g ∂μ ≤ ∑' n, ∫⁻ g in B' n, f g ∂μ :=
    (lintegral_mono_set (hDsub.trans hB'sub)).trans (lintegral_iUnion_le _ _)
  have hterm : ∀ n, ∫⁻ g in B' n, f g ∂μ = if n ∈ S then (∏ v, q v ^ n v) * ∫⁻ g in Dp, f g ∂μ else 0 := by
    intro n
    by_cases hn : n ∈ S
    · simp only [hB', if_pos hn, hBmass n, hmult n]
    · simp only [hB', if_neg hn, Measure.restrict_empty, lintegral_zero_measure]
  refine hle.trans_lt ?_
  simp_rw [hterm]
  by_cases hd : 0 < d₁
  ·
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ρ ^ N < d₁ / d₂ := exists_pow_lt_of_lt_one (div_pos hd hd₂) hρ1
    have hSfin : S ⊆ (Fintype.piFinset fun _ : InfinitePlace F => Finset.range N : Finset (InfinitePlace F → ℕ)) := by
      intro n hn
      refine Fintype.mem_piFinset.2 fun v => Finset.mem_range.2 ?_
      by_contra hge
      push Not at hge
      have h1 : ρ ^ n v ≤ ρ ^ N := pow_le_pow_of_le_one hρ0.le hρ1.le hge
      have h2 : d₁ ≤ ρ ^ n v * d₂ := hn v
      have : d₁ < d₁ := by
        calc d₁ ≤ ρ ^ n v * d₂ := h2
          _ ≤ ρ ^ N * d₂ := by gcongr
          _ < d₁ / d₂ * d₂ := by gcongr
          _ = d₁ := div_mul_cancel₀ d₁ hd₂.ne'
      exact lt_irrefl _ this
    rw [tsum_eq_sum (s := Fintype.piFinset fun _ : InfinitePlace F => Finset.range N) (fun n hn => by
      rw [if_neg (fun h => hn (hSfin h))])]
    refine ENNReal.sum_lt_top.mpr fun n _ => ?_
    split_ifs
    · exact ENNReal.mul_lt_top (ENNReal.prod_lt_top fun v _ => ENNReal.pow_lt_top (ENNReal.pow_lt_top enorm_lt_top)) hIp
    · exact ENNReal.zero_lt_top
  ·
    push Not at hd
    have hq1 : ∀ v, q v < 1 := by
      intro v
      have h := hcontr hd v (a v) (ha1 v)
      have h' : ‖((ω (AdelicVolume.archCentralUnit F v (a v)) : ℂˣ) : ℂ)‖ₑ < 1 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr h
      calc q v = ‖((ω (AdelicVolume.archCentralUnit F v (a v)) : ℂˣ) : ℂ)‖ₑ ^ 2 := rfl
        _ < 1 ^ 2 := by gcongr
        _ = 1 := one_pow 2
    calc ∑' n, (if n ∈ S then (∏ v, q v ^ n v) * ∫⁻ g in Dp, f g ∂μ else 0)
        ≤ ∑' n : InfinitePlace F → ℕ, (∏ v, q v ^ n v) * ∫⁻ g in Dp, f g ∂μ := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          split_ifs
          · exact le_rfl
          · exact zero_le
      _ = (∑' n : InfinitePlace F → ℕ, ∏ v, q v ^ n v) * ∫⁻ g in Dp, f g ∂μ := ENNReal.tsum_mul_right
      _ < ⊤ := ENNReal.mul_lt_top (Ws23.V2E.tsum_prod_pow_lt_top q hq1) hIp

end S_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le
end P2MW
export P2MW.S_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le (solution)
