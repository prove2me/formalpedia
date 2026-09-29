-- Prove2me | solution 1 for AutomorphicForm.eq_zero_of_isLsXiFunction_of_memLp_of_nonpos_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/318e20b7-8bb1-5251-8ee5-ab24d940f84b

import Mathlib
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eq_zero_of_isLsXiFunction_of_memLp_of_nonpos_of_coversModCentre

set_option autoImplicit false

p2m_open "NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicVolume MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_eq_zero_of_isLsXiFunction_of_memLp_of_nonpos_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"

open scoped Classical ENNReal NNReal MatrixGroups

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 globalPoints centralScalar IsLsXiFunction"
p2m_open "AutomorphicForm"

namespace NonposFloor

variable {F : Type} [Field F] [NumberField F]

local instance instMS : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
local instance instBS : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
local instance instHaar : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

abbrev μH (F : Type) [Field F] [NumberField F] : Measure (AdelicGL2 (𝓞 F) F) :=
  AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F

def sqm (φ : AdelicGL2 (𝓞 F) F → ℂ) (A : Set (AdelicGL2 (𝓞 F) F)) : ℝ≥0∞ :=
  ∫⁻ g in A, ((‖φ g‖₊ : ℝ≥0∞) ^ 2) ∂(μH F)

theorem measurable_sq_nnnorm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) :
    Measurable fun g => ((‖φ g‖₊ : ℝ≥0∞) ^ 2) :=
  (hφ.measurable.nnnorm.coe_nnreal_ennreal).pow_const 2

theorem sqm_mono (φ : AdelicGL2 (𝓞 F) F → ℂ) {A B : Set (AdelicGL2 (𝓞 F) F)} (h : A ⊆ B) : sqm φ A ≤ sqm φ B :=
  lintegral_mono_set h

theorem sqm_lt_top_of_memLp {φ : AdelicGL2 (𝓞 F) F → ℂ} {A : Set (AdelicGL2 (𝓞 F) F)}
    (h : MemLp φ 2 ((μH F).restrict A)) : sqm φ A < ⊤ := by
  have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by simp) h.2
  have hto : (2 : ℝ≥0∞).toReal = 2 := by simp
  unfold sqm
  convert h2 using 2 with g
  funext g
  rw [hto, ENNReal.rpow_two, enorm_eq_nnnorm]

def ent (v : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) (i j : Fin 2) : v.Completion :=
  ((archComponent F v (glArch (𝓞 F) F g) : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j

theorem continuous_ent (v : InfinitePlace F) (i j : Fin 2) : Continuous fun g : AdelicGL2 (𝓞 F) F => ent v g i j :=
  (Units.continuous_val.comp ((continuous_archComponent F v).comp (continuous_glArch (𝓞 F) F))).matrix_elem i j

theorem rowNormSq_eq (v : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    rowNormSq ((archComponent F v (glArch (𝓞 F) F g) : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion)
      = ‖ent v g 1 0‖ ^ 2 + ‖ent v g 1 1‖ ^ 2 := rfl

theorem topNormSq_eq (v : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    topNormSq ((archComponent F v (glArch (𝓞 F) F g) : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion)
      = ‖ent v g 0 0‖ ^ 2 + ‖ent v g 0 1‖ ^ 2 := rfl

def gam (n : ℤ) : SL(2, ℤ) := ⟨!![0, -1; 1, n], by simp [Matrix.det_fin_two_of]⟩
def unip (k : ℤ) : SL(2, ℤ) := ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem gam_mul_unip (n k : ℤ) : gam n * unip k = gam (k + n) := by
  apply Subtype.ext
  simp [gam, unip]

def gp (γ : SL(2, ℤ)) : AdelicGL2 (𝓞 F) F := globalPoints (𝓞 F) F (Matrix.SpecialLinearGroup.mapGL F γ)

theorem gp_mul (γ γ' : SL(2, ℤ)) : (gp (γ * γ') : AdelicGL2 (𝓞 F) F) = gp γ * gp γ' := by
  simp [gp, map_mul]

omit [NumberField F] in
theorem mapGL_entry (v : InfinitePlace F) (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL v.Completion γ : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) i j = (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : v.Completion) := by
  simp [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.map]

theorem ent_gp_mul (v : InfinitePlace F) (γ : SL(2, ℤ)) (g : AdelicGL2 (𝓞 F) F) (i j : Fin 2) :
    ent v (gp γ * g) i j = ∑ l, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i l : ℤ) : v.Completion) * ent v g l j := by
  unfold ent
  rw [map_mul, map_mul, gp, archComponent_glArch_globalPoints_mapGL, Units.val_mul, Matrix.mul_apply]
  simp only [mapGL_entry]

theorem ent_gam_top (v : InfinitePlace F) (n : ℤ) (g : AdelicGL2 (𝓞 F) F) (j : Fin 2) :
    ent v (gp (gam n) * g) 0 j = -ent v g 1 j := by
  rw [ent_gp_mul, Fin.sum_univ_two]
  simp [gam]

theorem ent_gam_bottom (v : InfinitePlace F) (n : ℤ) (g : AdelicGL2 (𝓞 F) F) (j : Fin 2) :
    ent v (gp (gam n) * g) 1 j = ent v g 0 j + (n : v.Completion) * ent v g 1 j := by
  rw [ent_gp_mul, Fin.sum_univ_two]
  simp [gam]

theorem ent_unip_top (v : InfinitePlace F) (k : ℤ) (g : AdelicGL2 (𝓞 F) F) (j : Fin 2) :
    ent v (gp (unip k) * g) 0 j = ent v g 0 j + (k : v.Completion) * ent v g 1 j := by
  rw [ent_gp_mul, Fin.sum_univ_two]
  simp [unip]

theorem ent_unip_bottom (v : InfinitePlace F) (k : ℤ) (g : AdelicGL2 (𝓞 F) F) (j : Fin 2) :
    ent v (gp (unip k) * g) 1 j = ent v g 1 j := by
  rw [ent_gp_mul, Fin.sum_univ_two]
  simp [unip]

omit [NumberField F] in
theorem norm_intCast_completion (v : InfinitePlace F) (n : ℤ) : ‖((n : v.Completion))‖ = |(n : ℝ)| := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
    map_intCast, Complex.norm_intCast]

theorem archDetNorm_mul (v : InfinitePlace F) (g h : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (g * h) = archDetNorm v g * archDetNorm v h := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

theorem archDetNorm_gp (v : InfinitePlace F) (γ : SL(2, ℤ)) : archDetNorm v (gp γ : AdelicGL2 (𝓞 F) F) = 1 := by
  unfold archDetNorm
  rw [gp, archComponent_glArch_globalPoints_mapGL]
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.2
  rw [Matrix.det_fin_two] at hdet
  have : ((Matrix.SpecialLinearGroup.mapGL v.Completion γ : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion).det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [mapGL_entry]
    have hc : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : v.Completion) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : v.Completion)
        - (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : v.Completion) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : v.Completion)
        = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
            - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : v.Completion) := by
      push_cast; ring
    rw [hc, hdet, Int.cast_one]
  rw [this, norm_one]

theorem archDetNorm_gp_mul (v : InfinitePlace F) (γ : SL(2, ℤ)) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (gp γ * g) = archDetNorm v g := by
  rw [archDetNorm_mul, archDetNorm_gp, one_mul]

theorem glFin_gp_mul_mem {γ : SL(2, ℤ)} {g : AdelicGL2 (𝓞 F) F} (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F) :
    glFin (𝓞 F) F (gp γ * g) ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [map_mul]
  exact Subgroup.mul_mem _ (glFin_globalPoints_mapGL_mem γ) hg

theorem archComponent_centralScalar_archCentralUnit (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) (i j : Fin 2) :
    ((archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F v₀ a))) :
        GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j
      = if i = j then ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v else 0 := by
  simp only [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h; rw [centralScalar_apply_eq, if_pos rfl]
  · rw [centralScalar_apply_ne _ h, if_neg h]; rfl

def centralEntry (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) : v.Completion :=
  ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v

theorem centralEntry_self (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) : centralEntry v₀ v₀ a = a :=
  archCentralUnit_fst_self v₀ a

theorem centralEntry_of_ne {v₀ v : InfinitePlace F} (a : (v₀.Completion)ˣ) (h : v ≠ v₀) : centralEntry v₀ v a = 1 :=
  archCentralUnit_fst_of_ne v₀ a h

theorem centralEntry_ne_zero (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) : centralEntry v₀ v a ≠ 0 :=
  archCentralUnit_fst_ne_zero v₀ a v

theorem localHeight_cS_mul (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)))
      = localHeight (archComponent F v (glArch (𝓞 F) F g)) := by
  rw [map_mul, map_mul]
  have h := archComponent_centralScalar_archCentralUnit v₀ v a
  exact localHeight_scalar_entries_mul (centralEntry_ne_zero v₀ v a)
    (by rw [h, if_pos rfl]; rfl) (by rw [h, if_neg (by decide)]) (by rw [h, if_neg (by decide)])
    (by rw [h, if_pos rfl]; rfl) _

theorem xWindowSq_cS_mul (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    xWindowSq (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)))
      = xWindowSq (archComponent F v (glArch (𝓞 F) F g)) := by
  rw [map_mul, map_mul]
  have h := archComponent_centralScalar_archCentralUnit v₀ v a
  exact xWindowSq_scalar_entries_mul (centralEntry_ne_zero v₀ v a)
    (by rw [h, if_pos rfl]; rfl) (by rw [h, if_neg (by decide)]) (by rw [h, if_neg (by decide)])
    (by rw [h, if_pos rfl]; rfl) _

theorem archDetNorm_cS_mul (v₀ v : InfinitePlace F) (a : (v₀.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)
      = ‖centralEntry v₀ v a‖ * ‖centralEntry v₀ v a‖ * archDetNorm v g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  have h := archComponent_centralScalar_archCentralUnit v₀ v a
  rw [Matrix.det_fin_two, h, h, h, h]
  simp [norm_mul, centralEntry]

theorem archDetNorm_cS_mul_self (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v₀ (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)
      = ‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖ * archDetNorm v₀ g := by
  rw [archDetNorm_cS_mul, centralEntry_self]

theorem archDetNorm_cS_mul_of_ne {v₀ v : InfinitePlace F} (h : v ≠ v₀) (a : (v₀.Completion)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g) = archDetNorm v g := by
  rw [archDetNorm_cS_mul, centralEntry_of_ne a h, norm_one, one_mul, one_mul]

omit [NumberField F] in
theorem norm_ratCast_completion (v : InfinitePlace F) (q : ℚ) : ‖((q : v.Completion))‖ = |(q : ℝ)| := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
    map_ratCast, Complex.norm_ratCast]

omit [NumberField F] in
theorem exists_unit_norm_mul_norm_eq (v : InfinitePlace F) {q : ℚ} (hq : 0 < q) :
    ∃ a : (v.Completion)ˣ, ‖(a : v.Completion)‖ * ‖(a : v.Completion)‖ = (q : ℝ) ^ 2 := by
  have hn : ‖((q : v.Completion))‖ = (q : ℝ) := by
    rw [norm_ratCast_completion, abs_of_pos (by exact_mod_cast hq)]
  have h0 : (q : v.Completion) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact (ne_of_gt (by exact_mod_cast hq : (0 : ℝ) < q)) hn.symm
  exact ⟨Units.mk0 _ h0, by rw [Units.val_mk0, hn, sq]⟩

theorem exists_rat_sq_mem_Icc {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ q : ℚ, 0 < q ∧ a ≤ (q : ℝ) ^ 2 ∧ (q : ℝ) ^ 2 ≤ b := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (Real.sqrt_lt_sqrt ha.le hab)
  have hqpos : (0 : ℝ) < q := (Real.sqrt_pos.mpr ha).trans hq1
  refine ⟨q, by exact_mod_cast hqpos, ?_, ?_⟩
  · calc a = Real.sqrt a ^ 2 := (Real.sq_sqrt ha.le).symm
      _ ≤ (q : ℝ) ^ 2 := by gcongr
  · calc (q : ℝ) ^ 2 ≤ Real.sqrt b ^ 2 := by gcongr
      _ = b := Real.sq_sqrt (ha.le.trans hab.le)

theorem exists_central_adjust (g : AdelicGL2 (𝓞 F) F) {e₁ e₂ : ℝ} (he₁ : 0 < e₁) (he : e₁ < e₂)
    (P : Finset (InfinitePlace F)) :
    ∃ z : (AdeleRing (𝓞 F) F)ˣ,
      glFin (𝓞 F) F (centralScalar (𝓞 F) F z) = 1 ∧
      (∀ v, localHeight (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F z * g)))
          = localHeight (archComponent F v (glArch (𝓞 F) F g))) ∧
      (∀ v, xWindowSq (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F z * g)))
          = xWindowSq (archComponent F v (glArch (𝓞 F) F g))) ∧
      (∀ v ∈ P, archDetNorm v (centralScalar (𝓞 F) F z * g) ∈ Set.Icc e₁ e₂) ∧
      (∀ v ∉ P, archDetNorm v (centralScalar (𝓞 F) F z * g) = archDetNorm v g) := by
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨1, by rw [map_one, map_one], fun v => by rw [map_one, one_mul],
      fun v => by rw [map_one, one_mul], fun v hv => (Finset.notMem_empty v hv).elim,
      fun v _ => by rw [map_one, one_mul]⟩
  | insert v₀ P hv₀ ih =>
    obtain ⟨z, hzfin, hzh, hzx, hzP, hznP⟩ := ih
    set g' := centralScalar (𝓞 F) F z * g with hg'
    have hr : 0 < archDetNorm v₀ g' := archDetNorm_pos v₀ g'
    obtain ⟨q, hq, hq1, hq2⟩ := exists_rat_sq_mem_Icc (div_pos he₁ hr) ((div_lt_div_iff_of_pos_right hr).mpr he)
    obtain ⟨a, ha⟩ := exists_unit_norm_mul_norm_eq v₀ hq
    have hcs : centralScalar (𝓞 F) F (archCentralUnit F v₀ a * z) * g
        = centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g' := by
      rw [map_mul, mul_assoc]
    refine ⟨archCentralUnit F v₀ a * z, ?_, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, map_mul, glFin_centralScalar_archCentralUnit, one_mul, hzfin]
    · intro v; rw [hcs, localHeight_cS_mul, hg', hzh]
    · intro v; rw [hcs, xWindowSq_cS_mul, hg', hzx]
    · intro v hv
      rw [hcs]
      rcases Finset.mem_insert.mp hv with rfl | hv
      · rw [archDetNorm_cS_mul_self, ha]
        exact ⟨(div_le_iff₀ hr).mp hq1, (le_div_iff₀ hr).mp hq2⟩
      · have hne : v ≠ v₀ := fun h => hv₀ (h ▸ hv)
        rw [archDetNorm_cS_mul_of_ne hne]
        exact hzP v hv
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [hcs, archDetNorm_cS_mul_of_ne hv.1]
      exact hznP v hv.2

omit [NumberField F] in

theorem norm_add_mul_ge (v : InfinitePlace F) (a c : v.Completion) (n : ℤ) :
    |(n : ℝ)| * ‖c‖ - ‖a‖ ≤ ‖a + (n : v.Completion) * c‖ := by
  have h1 : ‖(n : v.Completion) * c‖ ≤ ‖a + (n : v.Completion) * c‖ + ‖a‖ := by
    calc ‖(n : v.Completion) * c‖ = ‖(a + (n : v.Completion) * c) - a‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖a + (n : v.Completion) * c‖ + ‖a‖ := norm_sub_le _ _
  rw [norm_mul, norm_intCast_completion] at h1
  linarith

theorem image_mul_left_eq_preimage (y : AdelicGL2 (𝓞 F) F) (A : Set (AdelicGL2 (𝓞 F) F)) :
    (fun g => y * g) '' A = (fun g => y⁻¹ * g) ⁻¹' A := by
  ext g
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rwa [inv_mul_cancel_left]
  · intro h
    exact ⟨_, h, by rw [mul_inv_cancel_left]⟩

theorem measurableSet_image_mul_left (y : AdelicGL2 (𝓞 F) F) {A : Set (AdelicGL2 (𝓞 F) F)}
    (hA : MeasurableSet A) : MeasurableSet ((fun g => y * g) '' A) := by
  rw [image_mul_left_eq_preimage]
  exact measurable_const_mul _ hA

theorem sqm_image_gp {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ) (γ : SL(2, ℤ))
    {A : Set (AdelicGL2 (𝓞 F) F)} (hA : MeasurableSet A) :
    sqm φ ((fun g => (gp γ : AdelicGL2 (𝓞 F) F) * g) '' A) = sqm φ A := by
  unfold sqm
  rw [image_mul_left_eq_preimage]
  have hmp := measurePreserving_mul_left (μH F) ((gp γ : AdelicGL2 (𝓞 F) F)⁻¹)
  have hmeas : Measurable fun b => ((‖φ ((gp γ : AdelicGL2 (𝓞 F) F) * b)‖₊ : ℝ≥0∞) ^ 2) :=
    ((hcont.comp (continuous_const.mul continuous_id)).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have key := hmp.setLIntegral_comp_preimage hA hmeas
  simp only [mul_inv_cancel_left] at key
  rw [key]
  congr 1
  funext b
  rw [gp, hφ.left_invariant]

section Core

variable {c u d₁ d₂ : ℝ}

theorem core (hc : c ≤ 0) (hu : u ≠ 0)
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ)
    (x s : AdelicGL2 (𝓞 F) F) (hsfin : glFin (𝓞 F) F s ∈ finiteIntegralGL2 (𝓞 F) F)
    (hsdet : ∀ v, d₁ < archDetNorm v s ∧ archDetNorm v s < d₂) (hφs : φ (s * x) ≠ 0) :
    sqm φ ((· * x) '' centreCutSiegelSet F c u d₁ d₂) = ⊤ := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hu2 : 0 < u ^ 2 := by positivity

  have hbot : ∀ v, ∃ j : Fin 2, ent v s 1 j ≠ 0 := fun v => by
    rcases bottom_row_ne_zero (archComponent F v (glArch (𝓞 F) F s)) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  choose jv hjv using hbot
  set ρ : InfinitePlace F → ℝ := fun v => ‖ent v s 1 (jv v)‖ with hρdef
  have hρ : ∀ v, 0 < ρ v := fun v => norm_pos_iff.mpr (hjv v)
  set δ : InfinitePlace F → ℝ := fun v => ρ v / 4 with hδdef
  have hδ : ∀ v, 0 < δ v := fun v => by simp only [hδdef]; linarith [hρ v]

  set N : Set (AdelicGL2 (𝓞 F) F) := {b |
    glFin (𝓞 F) F (b * x⁻¹) ∈ finiteIntegralGL2 (𝓞 F) F ∧
    (∀ v, d₁ < archDetNorm v (b * x⁻¹) ∧ archDetNorm v (b * x⁻¹) < d₂) ∧
    (∀ v (i j : Fin 2), ‖ent v (b * x⁻¹) i j - ent v s i j‖ < δ v) ∧
    φ b ≠ 0} with hNdef
  have hcx : Continuous fun b : AdelicGL2 (𝓞 F) F => b * x⁻¹ := continuous_id.mul continuous_const
  have hNopen : IsOpen N := by
    simp only [hNdef, Set.setOf_and]
    refine IsOpen.inter ?_ (IsOpen.inter ?_ (IsOpen.inter ?_ ?_))
    · exact ((NumberField.AdelicLevel.isOpen_finiteLevelZero (𝓞 F) F (N := (⊤ : Ideal (𝓞 F))) (by simp)).preimage
        (continuous_glFin (𝓞 F) F)).preimage hcx
    · simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun v =>
        (isOpen_lt continuous_const ((continuous_archDetNorm v).comp hcx)).inter
          (isOpen_lt ((continuous_archDetNorm v).comp hcx) continuous_const)
    · simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun v => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        isOpen_lt (((continuous_ent v i j).comp hcx).sub continuous_const).norm continuous_const
    · exact isOpen_ne.preimage hcont
  have hsN : s * x ∈ N := by
    simp only [hNdef, Set.mem_setOf_eq, mul_inv_cancel_right, sub_self, norm_zero]
    exact ⟨hsfin, hsdet, fun v _ _ => hδ v, hφs⟩
  have hNmeas : MeasurableSet N := hNopen.measurableSet
  have hNpos : 0 < (μH F) N := hNopen.measure_pos _ ⟨_, hsN⟩

  have hm : sqm φ N ≠ 0 := by
    intro h0
    have hae := (lintegral_eq_zero_iff (measurable_sq_nnnorm hcont)).mp h0
    rw [Filter.EventuallyEq, ae_restrict_iff' hNmeas] at hae
    have : ∀ᵐ g ∂(μH F), g ∉ N := by
      filter_upwards [hae] with g hg hgN
      have h2 : ((‖φ g‖₊ : ℝ≥0∞) ^ 2) = 0 := hg hgN
      have : φ g = 0 := by simpa [pow_eq_zero_iff, ENNReal.coe_eq_zero, nnnorm_eq_zero] using h2
      exact hgN.2.2.2 this
    rw [← measure_eq_zero_iff_ae_notMem] at this
    exact hNpos.ne' this

  set A : InfinitePlace F → ℝ := fun v => ‖ent v s 0 (jv v)‖ + δ v with hAdef
  set R : InfinitePlace F → ℝ := fun v => (‖ent v s 1 0‖ + δ v) ^ 2 + (‖ent v s 1 1‖ + δ v) ^ 2 with hRdef
  set n₀v : InfinitePlace F → ℕ := fun v => ⌈(max (R v / u ^ 2) 1 + A v) / (ρ v - δ v)⌉₊ with hn₀vdef
  set n₀ : ℕ := Finset.univ.sup n₀v with hn₀def
  have hn₀v : ∀ v, n₀v v ≤ n₀ := fun v => Finset.le_sup (Finset.mem_univ v)

  have hclose : ∀ b ∈ N, ∀ v (i j : Fin 2), ‖ent v (b * x⁻¹) i j‖ ≤ ‖ent v s i j‖ + δ v := by
    intro b hb v i j
    have h := hb.2.2.1 v i j
    have := norm_le_norm_add_norm_sub' (ent v (b * x⁻¹) i j) (ent v s i j)
    have := norm_sub_rev (ent v (b * x⁻¹) i j) (ent v s i j)
    calc ‖ent v (b * x⁻¹) i j‖ ≤ ‖ent v s i j‖ + ‖ent v (b * x⁻¹) i j - ent v s i j‖ := norm_le_insert' _ _
      _ ≤ ‖ent v s i j‖ + δ v := by linarith
  have hfar : ∀ b ∈ N, ∀ v, ρ v - δ v ≤ ‖ent v (b * x⁻¹) 1 (jv v)‖ := by
    intro b hb v
    have h := hb.2.2.1 v 1 (jv v)
    have := norm_le_insert (ent v (b * x⁻¹) 1 (jv v)) (ent v s 1 (jv v))

    have h2 : ‖ent v s 1 (jv v)‖ ≤ ‖ent v (b * x⁻¹) 1 (jv v)‖ + ‖ent v (b * x⁻¹) 1 (jv v) - ent v s 1 (jv v)‖ := by
      rw [norm_sub_rev]; exact norm_le_insert' _ _
    simp only [hρdef]
    linarith

  have hwin : ∀ b ∈ N, ∀ n : ℕ, n₀ ≤ n → ∀ v,
      xWindowSq (archComponent F v (glArch (𝓞 F) F ((gp (gam n) : AdelicGL2 (𝓞 F) F) * (b * x⁻¹)))) ≤ u ^ 2 := by
    intro b hb n hn v
    set h := b * x⁻¹ with hh
    have hρδ : 0 < ρ v - δ v := by simp only [hδdef]; linarith [hρ v]

    set L : ℝ := (n : ℝ) * (ρ v - δ v) - A v with hL
    have hLge : max (R v / u ^ 2) 1 ≤ L := by
      have h1 : (max (R v / u ^ 2) 1 + A v) / (ρ v - δ v) ≤ n₀v v := Nat.le_ceil _
      have h2 : (n₀v v : ℝ) ≤ n := by exact_mod_cast (hn₀v v).trans hn
      have h3 := (div_le_iff₀ hρδ).mp (h1.trans h2)
      simp only [hL]; linarith
    have hL1 : 1 ≤ L := (le_max_right _ _).trans hLge
    have hL0 : 0 < L := one_pos.trans_le hL1

    have hrow : L ^ 2 ≤ rowNormSq ((archComponent F v (glArch (𝓞 F) F ((gp (gam n) : AdelicGL2 (𝓞 F) F) * h)) :
        GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) := by
      rw [rowNormSq_eq]
      have hj : L ≤ ‖ent v ((gp (gam n) : AdelicGL2 (𝓞 F) F) * h) 1 (jv v)‖ := by
        rw [ent_gam_bottom]
        have h1 := norm_add_mul_ge v (ent v h 0 (jv v)) (ent v h 1 (jv v)) n
        have h2 : |((n : ℤ) : ℝ)| = n := by simp
        rw [h2] at h1
        have h3 : (n : ℝ) * (ρ v - δ v) ≤ (n : ℝ) * ‖ent v h 1 (jv v)‖ :=
          mul_le_mul_of_nonneg_left (hfar b hb v) (Nat.cast_nonneg n)
        have h4 : ‖ent v h 0 (jv v)‖ ≤ A v := hclose b hb v 0 (jv v)
        simp only [hL]
        linarith
      have hsq : L ^ 2 ≤ ‖ent v ((gp (gam n) : AdelicGL2 (𝓞 F) F) * h) 1 (jv v)‖ ^ 2 :=
        pow_le_pow_left₀ hL0.le hj 2
      generalize hjdef : jv v = j at hsq
      fin_cases j
      · simp only [Fin.zero_eta] at hsq
        linarith [sq_nonneg ‖ent v ((gp (gam n) : AdelicGL2 (𝓞 F) F) * h) 1 1‖]
      · simp only [Fin.mk_one] at hsq
        linarith [sq_nonneg ‖ent v ((gp (gam n) : AdelicGL2 (𝓞 F) F) * h) 1 0‖]

    have htop : topNormSq ((archComponent F v (glArch (𝓞 F) F ((gp (gam n) : AdelicGL2 (𝓞 F) F) * h)) :
        GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) ≤ R v := by
      rw [topNormSq_eq, ent_gam_top, ent_gam_top, norm_neg, norm_neg]
      simp only [hRdef]
      have h0 := hclose b hb v 1 0
      have h1 := hclose b hb v 1 1
      gcongr

    have hrowpos : 0 < rowNormSq ((archComponent F v (glArch (𝓞 F) F ((gp (gam n) : AdelicGL2 (𝓞 F) F) * h)) :
        GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) := rowNormSq_pos _
    unfold xWindowSq
    have hRL : R v ≤ u ^ 2 * L ^ 2 := by
      have h1 : R v / u ^ 2 ≤ L := (le_max_left _ _).trans hLge
      have h2 : R v ≤ L * u ^ 2 := (div_le_iff₀ hu2).mp h1
      have h3 : L ≤ L ^ 2 := by nlinarith
      have h4 : L * u ^ 2 ≤ L ^ 2 * u ^ 2 := mul_le_mul_of_nonneg_right h3 hu2.le
      linarith
    calc topNormSq _ / rowNormSq _ - localHeight _ ^ 2 ≤ topNormSq _ / rowNormSq _ := sub_le_self _ (sq_nonneg _)
      _ ≤ R v / L ^ 2 := by
          rw [div_le_div_iff₀ hrowpos (pow_pos hL0 2)]
          have hR0 : 0 ≤ R v := by simp only [hRdef]; positivity
          calc topNormSq _ * L ^ 2 ≤ R v * L ^ 2 := by gcongr
            _ ≤ R v * rowNormSq _ := by gcongr
      _ ≤ u ^ 2 := by rw [div_le_iff₀ (pow_pos hL0 2)]; exact hRL

  have hcontain : ∀ n : ℕ, n₀ ≤ n → (fun b => (gp (gam n) : AdelicGL2 (𝓞 F) F) * b) '' N
      ⊆ (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
    rintro n hn _ ⟨b, hb, rfl⟩
    refine ⟨(gp (gam n) : AdelicGL2 (𝓞 F) F) * (b * x⁻¹), ?_, by simp only [mul_assoc, inv_mul_cancel, mul_one]⟩
    rw [mem_centreCutSiegelSet_iff]
    refine ⟨glFin_gp_mul_mem hb.1, fun w => hc.trans (localHeight_pos _).le, fun w => hwin b hb n hn w, fun w => ?_⟩
    rw [archDetNorm_gp_mul]
    exact ⟨(hb.2.1 w).1.le, (hb.2.1 w).2.le⟩

  have hdisj : ∀ n n' : ℕ, n ≠ n' → Disjoint ((fun b => (gp (gam n) : AdelicGL2 (𝓞 F) F) * b) '' N)
      ((fun b => (gp (gam n') : AdelicGL2 (𝓞 F) F) * b) '' N) := by
    intro n n' hne
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ ⟨b', hb', heq⟩
    set k : ℤ := (n : ℤ) - n' with hk
    have hgam : gam (n : ℤ) = gam (n' : ℤ) * unip k := by rw [gam_mul_unip]; congr 1; omega
    have hb'' : b' = (gp (unip k) : AdelicGL2 (𝓞 F) F) * b := by
      have h1 : (gp (gam n') : AdelicGL2 (𝓞 F) F) * b' = gp (gam n') * (gp (unip k) * b) := by
        rw [← mul_assoc, ← gp_mul, ← hgam]; exact heq
      exact mul_left_cancel h1
    set j := jv v₀ with hj
    have e_top : ent v₀ (b' * x⁻¹) 0 j = ent v₀ (b * x⁻¹) 0 j + (k : v₀.Completion) * ent v₀ (b * x⁻¹) 1 j := by
      rw [hb'', mul_assoc, ent_unip_top]
    have h1 := hb.2.2.1 v₀ 0 j
    have h2 := hb'.2.2.1 v₀ 0 j
    have h3 : ‖(k : v₀.Completion) * ent v₀ (b * x⁻¹) 1 j‖ < 2 * δ v₀ := by
      have h4 : (k : v₀.Completion) * ent v₀ (b * x⁻¹) 1 j
          = (ent v₀ (b' * x⁻¹) 0 j - ent v₀ s 0 j) - (ent v₀ (b * x⁻¹) 0 j - ent v₀ s 0 j) := by
        rw [e_top]; ring
      rw [h4]
      exact (norm_sub_le _ _).trans_lt (by linarith)
    have hkne : k ≠ 0 := by simp only [hk]; omega
    have h4 : ‖ent v₀ (b * x⁻¹) 1 j‖ ≤ ‖(k : v₀.Completion) * ent v₀ (b * x⁻¹) 1 j‖ := by
      rw [norm_mul, norm_intCast_completion]
      have h5 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hkne
      exact le_mul_of_one_le_left (norm_nonneg _) h5
    have h5 : ρ v₀ - δ v₀ ≤ ‖ent v₀ (b * x⁻¹) 1 j‖ := hfar b hb v₀
    have hρ4 : ρ v₀ = 4 * δ v₀ := by simp only [hδdef]; ring
    have hδ0 := hδ v₀
    linarith

  set S : ℕ → Set (AdelicGL2 (𝓞 F) F) :=
    fun i => (fun b => (gp (gam ((n₀ + i : ℕ) : ℤ)) : AdelicGL2 (𝓞 F) F) * b) '' N with hS
  have hSm : ∀ i, MeasurableSet (S i) := fun i => measurableSet_image_mul_left _ hNmeas
  have hSd : Pairwise (Function.onFun Disjoint S) := fun i i' hii' => hdisj (n₀ + i) (n₀ + i') (by omega)
  have hSsub : ∀ i, S i ⊆ (· * x) '' centreCutSiegelSet F c u d₁ d₂ := fun i => hcontain (n₀ + i) (Nat.le_add_right _ _)
  have hSmass : ∀ i, sqm φ (S i) = sqm φ N := fun i => sqm_image_gp hφ hcont _ hNmeas
  rw [eq_top_iff]
  calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, sqm φ N := (ENNReal.tsum_const_eq_top_of_ne_zero hm).symm
    _ = ∑' i, sqm φ (S i) := by simp_rw [hSmass]
    _ = sqm φ (⋃ i, S i) := (lintegral_iUnion hSm hSd _).symm
    _ ≤ sqm φ ((· * x) '' centreCutSiegelSet F c u d₁ d₂) := sqm_mono φ (Set.iUnion_subset hSsub)

end Core

end NonposFloor

end AutomorphicForm

end

open AutomorphicForm.NonposFloor in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : c ≤ 0) (hd : d₁ < d₂) (hu : u ≠ 0)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ)
    (hL2 : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))) :
    φ = 0 := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  by_contra hne
  have hex : ∃ g, φ g ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨g₁, hg₁⟩ := hex

  obtain ⟨γ₀, z₀, hmem⟩ := hcov g₁
  simp only [Set.mem_iUnion, Set.mem_image] at hmem
  obtain ⟨x, hx, s, hs, hsx⟩ := hmem
  have hφsx : φ (s * x) ≠ 0 := by
    rw [hsx, mul_assoc, mul_centralScalar_comm z₀ g₁, hφ.left_invariant,
      hφ.central_transform ⟨z₀, Subgroup.mem_top z₀⟩]
    exact mul_ne_zero (Units.ne_zero _) hg₁
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  obtain ⟨hsfin, -, -, hsdet⟩ := mem_centreCutSiegelSet_iff.mp hs
  have hd₂ : 0 < d₂ := (archDetNorm_pos w s).trans_le (hsdet w).2

  set e₁ := (max d₁ 0 + d₂) / 2 with he₁def
  set e₂ := (e₁ + d₂) / 2 with he₂def
  have hmax : max d₁ 0 < d₂ := max_lt hd hd₂
  have hm1 := le_max_left d₁ 0
  have hm2 := le_max_right d₁ 0
  have he₁pos : 0 < e₁ := by simp only [he₁def]; linarith
  have hde₁ : d₁ < e₁ := by simp only [he₁def]; linarith
  have he₁d₂ : e₁ < d₂ := by simp only [he₁def]; linarith
  have he : e₁ < e₂ := by simp only [he₂def]; linarith
  have he₂ : e₂ < d₂ := by simp only [he₂def]; linarith
  obtain ⟨z', hz'fin, -, -, hz'P, -⟩ := exists_central_adjust s he₁pos he Finset.univ
  have hs'fin : glFin (𝓞 F) F (centralScalar (𝓞 F) F z' * s) ∈ finiteIntegralGL2 (𝓞 F) F := by
    rw [map_mul, hz'fin, one_mul]; exact hsfin
  have hs'det : ∀ v, d₁ < archDetNorm v (centralScalar (𝓞 F) F z' * s) ∧
      archDetNorm v (centralScalar (𝓞 F) F z' * s) < d₂ := fun v =>
    ⟨hde₁.trans_le (hz'P v (Finset.mem_univ v)).1, (hz'P v (Finset.mem_univ v)).2.trans_lt he₂⟩
  have hφ' : φ (centralScalar (𝓞 F) F z' * s * x) ≠ 0 := by
    rw [mul_assoc, hφ.central_transform ⟨z', Subgroup.mem_top z'⟩]
    exact mul_ne_zero (Units.ne_zero _) hφsx
  have hcore := core hc hu hφ hcont x _ hs'fin hs'det hφ'
  have hfin : sqm φ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) < ⊤ := sqm_lt_top_of_memLp hL2
  have hle : sqm φ ((· * x) '' centreCutSiegelSet F c u d₁ d₂)
      ≤ sqm φ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
    refine sqm_mono φ ?_
    intro g hg
    simp only [Set.mem_iUnion]
    exact ⟨x, hx, hg⟩
  rw [hcore, top_le_iff] at hle
  exact hfin.ne hle

end S_AutomorphicForm_eq_zero_of_isLsXiFunction_of_memLp_of_nonpos_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_eq_zero_of_isLsXiFunction_of_memLp_of_nonpos_of_coversModCentre (solution)
