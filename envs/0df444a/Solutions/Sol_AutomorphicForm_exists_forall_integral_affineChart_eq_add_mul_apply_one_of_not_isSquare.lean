-- Prove2me | solution 1 for AutomorphicForm.exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/dd816b23-ab24-528f-89a1-14bb1e9c6fa0

import Mathlib
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace P2mGermChart

section Chart

variable {F : Type*} [Field F]

def Y (t a b : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; (t - a ^ 2) / b, -a]

@[scoped simp] theorem Y_apply_00 (t a b : F) : Y t a b 0 0 = a := rfl
@[scoped simp] theorem Y_apply_01 (t a b : F) : Y t a b 0 1 = b := rfl
@[scoped simp] theorem Y_apply_10 (t a b : F) : Y t a b 1 0 = (t - a ^ 2) / b := rfl
@[scoped simp] theorem Y_apply_11 (t a b : F) : Y t a b 1 1 = -a := rfl

def E10 (x : F) : Matrix (Fin 2) (Fin 2) F := !![0, 0; x, 0]

@[scoped simp] theorem E10_apply_00 (x : F) : E10 x 0 0 = 0 := rfl
@[scoped simp] theorem E10_apply_01 (x : F) : E10 x 0 1 = 0 := rfl
@[scoped simp] theorem E10_apply_10 (x : F) : E10 x 1 0 = x := rfl
@[scoped simp] theorem E10_apply_11 (x : F) : E10 x 1 1 = 0 := rfl

def AB (a b : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; 0, -a]

@[scoped simp] theorem AB_apply_00 (a b : F) : AB a b 0 0 = a := rfl
@[scoped simp] theorem AB_apply_01 (a b : F) : AB a b 0 1 = b := rfl
@[scoped simp] theorem AB_apply_10 (a b : F) : AB a b 1 0 = 0 := rfl
@[scoped simp] theorem AB_apply_11 (a b : F) : AB a b 1 1 = -a := rfl

theorem Y_eq_E10_add_AB (t a b : F) : Y t a b = E10 ((t - a ^ 2) / b) + AB a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Y, E10, AB]

theorem Y_sub_Y (t t' a b : F) : Y t a b - Y t' a b = E10 ((t - t') / b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Y, E10] ; ring

theorem one_add_Y_eq (t a b : F) : (1 : Matrix (Fin 2) (Fin 2) F) + Y t a b =
    (1 + E10 ((t - a ^ 2) / b)) + AB a b := by
  rw [Y_eq_E10_add_AB, add_assoc]

end Chart

section Bounds

variable {F : Type*} [NontriviallyNormedField F]

def EntryLE (M : Matrix (Fin 2) (Fin 2) F) (δ : ℝ) : Prop := ∀ i j, ‖M i j‖ ≤ δ

theorem EntryLE.mono {M : Matrix (Fin 2) (Fin 2) F} {δ δ' : ℝ} (h : EntryLE M δ) (hδ : δ ≤ δ') :
    EntryLE M δ' := fun i j => (h i j).trans hδ

theorem EntryLE.neg {M : Matrix (Fin 2) (Fin 2) F} {δ : ℝ} (h : EntryLE M δ) : EntryLE (-M) δ :=
  fun i j => by rw [Matrix.neg_apply, norm_neg]; exact h i j

variable [IsUltrametricDist F]

theorem EntryLE.add {M N : Matrix (Fin 2) (Fin 2) F} {δ : ℝ} (hM : EntryLE M δ) (hN : EntryLE N δ) :
    EntryLE (M + N) δ :=
  fun i j => by
    rw [Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hM i j) (hN i j))

theorem EntryLE.sub {M N : Matrix (Fin 2) (Fin 2) F} {δ : ℝ} (hM : EntryLE M δ) (hN : EntryLE N δ) :
    EntryLE (M - N) δ := by
  rw [sub_eq_add_neg]; exact hM.add hN.neg

omit [IsUltrametricDist F] in
theorem entryLE_E10 {x : F} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ‖x‖ ≤ δ) : EntryLE (E10 x) δ := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E10, hδ, hx]

omit [IsUltrametricDist F] in
theorem entryLE_AB {a b : F} {δ : ℝ} (ha : ‖a‖ ≤ δ) (hb : ‖b‖ ≤ δ) : EntryLE (AB a b) δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans ha
  intro i j; fin_cases i <;> fin_cases j <;> simp [AB, hδ, ha, hb]

theorem entryLE_of_entryLE_one_add {M : Matrix (Fin 2) (Fin 2) F} {B : ℝ} (hB : 1 ≤ B)
    (h : EntryLE (1 + M) B) : EntryLE M B := by
  have h1 : EntryLE (1 : Matrix (Fin 2) (Fin 2) F) B := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [(zero_le_one.trans hB), hB]
  have := h.sub h1
  rwa [add_sub_cancel_left] at this

theorem norm_sub_le_max (x y : F) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_sub_sq_of_lt {t a : F} (h : ‖t‖ < ‖a‖ ^ 2) : ‖t - a ^ 2‖ = ‖a‖ ^ 2 := by
  rw [← norm_pow] at h ⊢
  rw [← norm_neg (a ^ 2)] at h
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne, max_eq_right h.le, norm_neg]

theorem norm_sub_sq_of_gt {t a : F} (h : ‖a‖ ^ 2 < ‖t‖) : ‖t - a ^ 2‖ = ‖t‖ := by
  rw [← norm_pow] at h
  rw [← norm_neg (a ^ 2)] at h
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem norm_sub_sq_le (t a : F) : ‖t - a ^ 2‖ ≤ max ‖t‖ (‖a‖ ^ 2) := by
  rw [← norm_pow]; exact norm_sub_le_max _ _

theorem norm_four_le_one : ‖(4 : F)‖ ≤ 1 := by
  have : (4 : F) = 1 + 1 + 1 + 1 := by norm_num
  rw [this]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_one]))
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_one]))
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rw [norm_one]) (by rw [norm_one]))

end Bounds

section LocalSquare

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]

theorem isSquare_of_norm_sub_one_lt {s : F} (hs : ‖s - 1‖ < ‖(4 : F)‖) : IsSquare s := by
  have h4 : (4 : F) ≠ 0 := by
    intro h; rw [h, norm_zero] at hs; exact (not_lt.2 (norm_nonneg _)) hs
  set w : F := (s - 1) / 4 with hw
  have hwn : ‖w‖ < 1 := by
    rw [hw, norm_div, div_lt_one (norm_pos_iff.2 h4)]; exact hs

  set D : Set F := Metric.closedBall (0 : F) ‖w‖ with hD
  have hDmem : ∀ {y : F}, y ∈ D ↔ ‖y‖ ≤ ‖w‖ := by
    intro y; rw [hD, Metric.mem_closedBall, dist_zero_right]
  have hmaps : ∀ y ∈ D, w - y ^ 2 ∈ D := by
    intro y hy
    rw [hDmem] at hy ⊢
    refine (norm_sub_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_pow]
    calc ‖y‖ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
      _ ≤ ‖w‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hwn.le one_le_two
      _ = ‖w‖ := pow_one _
  haveI : CompleteSpace D := (Metric.isClosed_closedBall.completeSpace_coe)
  set T : D → D := fun y => ⟨w - (y : F) ^ 2, hmaps y y.2⟩ with hT
  have hK : ContractingWith ⟨‖w‖, norm_nonneg _⟩ T := by
    refine ⟨by exact_mod_cast hwn, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    change dist (w - (y : F) ^ 2) (w - (y' : F) ^ 2) ≤ ‖w‖ * dist (y : F) (y' : F)
    rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_left]
    have hfac : (y' : F) ^ 2 - (y : F) ^ 2 = ((y' : F) + y) * ((y' : F) - y) := by ring
    rw [hfac, norm_mul, ← norm_neg ((y' : F) - y), neg_sub]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hDmem.1 y'.2) (hDmem.1 y.2))
  haveI : Nonempty D := ⟨⟨0, by rw [hDmem, norm_zero]; exact norm_nonneg _⟩⟩
  obtain ⟨y, hy, -⟩ := hK.exists_fixedPoint (Classical.arbitrary D) (edist_ne_top _ _)
  have hfix : (y : F) = w - (y : F) ^ 2 := by
    have := congrArg (fun z : D => (z : F)) hy
    simpa [hT] using this.symm
  refine ⟨1 + 2 * (y : F), ?_⟩
  have : s = 1 + 4 * w := by rw [hw]; field_simp; ring
  clear_value w
  rw [this]
  linear_combination (-4 : F) * hfix

theorem isSquare_of_norm_sub_sq_lt {t a : F} (h : ‖t - a ^ 2‖ < ‖(4 : F) * t‖) : IsSquare t := by
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, mul_zero, norm_zero] at h; exact (not_lt.2 (norm_nonneg _)) h
  have h4t : ‖(4 : F) * t‖ ≤ ‖t‖ := by
    rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) norm_four_le_one
  have ha2 : ‖a ^ 2‖ = ‖t‖ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [norm_pow] at hlt
      have := norm_sub_sq_of_gt hlt
      rw [this] at h; exact (not_lt.2 h4t) h
    · rw [norm_pow] at hgt
      have := norm_sub_sq_of_lt hgt
      rw [this] at h
      exact (not_lt.2 (h4t.trans hgt.le)) h
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, zero_pow two_ne_zero, norm_zero] at ha2; exact ht0 (norm_eq_zero.1 ha2.symm)
  have ha20 : a ^ 2 ≠ 0 := pow_ne_zero _ ha0

  have hs : ‖t / a ^ 2 - 1‖ < ‖(4 : F)‖ := by
    have : t / a ^ 2 - 1 = (t - a ^ 2) / a ^ 2 := by field_simp
    rw [this, norm_div, ha2, div_lt_iff₀ (norm_pos_iff.2 ht0), ← norm_mul]
    exact h
  obtain ⟨r, hr⟩ := isSquare_of_norm_sub_one_lt hs
  refine ⟨r * a, ?_⟩
  calc t = t / a ^ 2 * a ^ 2 := by field_simp
    _ = r * a * (r * a) := by rw [hr]; ring

end LocalSquare

section Fibres

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

def fibre (D : ℝ) (t : F) (ε' : ℝ) : Set F := {a | ‖a‖ ≤ D ∧ ‖t - a ^ 2‖ ≤ ε'}

omit [IsUltrametricDist F] in
theorem mem_fibre {D : ℝ} {t : F} {ε' : ℝ} {a : F} : a ∈ fibre D t ε' ↔ ‖a‖ ≤ D ∧ ‖t - a ^ 2‖ ≤ ε' :=
  Iff.rfl

omit [IsUltrametricDist F] in
theorem fibre_zero (D ε' : ℝ) : fibre D (0 : F) ε' = {a | ‖a‖ ≤ D ∧ ‖a‖ ^ 2 ≤ ε'} := by
  ext a; rw [mem_fibre, zero_sub, norm_neg, norm_pow]; rfl

theorem fibre_eq_of_le {D ε' : ℝ} {t : F} (h : ‖t‖ ≤ ε') : fibre D t ε' = fibre D 0 ε' := by
  rw [fibre_zero]
  ext a
  simp only [mem_fibre, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h2 => ?_, fun h2 => ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    have := norm_sub_sq_of_lt (h.trans_lt hlt)
    rw [this] at h2
    exact (not_lt.2 h2) hlt
  · exact (norm_sub_sq_le t a).trans (max_le h h2)

theorem fibre_eq_image_add {D ε' : ℝ} {t : F} (h4 : ‖(4 : F) * t‖ ≤ ε') (hlt : ε' < ‖t‖)
    {a₀ : F} (ha₀ : a₀ ∈ fibre D t ε') :
    fibre D t ε' = (fun h => a₀ + h) '' fibre D 0 ε' := by
  obtain ⟨ha₀D, ha₀t⟩ := ha₀
  have hε0 : 0 ≤ ε' := (norm_nonneg _).trans ha₀t

  have ha₀2 : ‖a₀‖ ^ 2 = ‖t‖ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hg
    · rw [norm_sub_sq_of_gt hl] at ha₀t; exact (not_lt.2 ha₀t) hlt
    · rw [norm_sub_sq_of_lt hg] at ha₀t; exact (not_lt.2 (ha₀t.trans hlt.le)) hg
  have h2a₀ : ‖2 * a₀‖ ^ 2 = ‖(4 : F) * t‖ := by
    rw [← norm_pow, norm_mul (4 : F), ← ha₀2, ← norm_pow, ← norm_mul]; congr 1; ring

  have key : ∀ h : F, ‖t - (a₀ + h) ^ 2‖ ≤ ε' ↔ ‖h‖ ^ 2 ≤ ε' := by
    intro h
    have hexp : t - (a₀ + h) ^ 2 = (t - a₀ ^ 2) + -(h * (h + 2 * a₀)) := by ring
    constructor
    · intro hle

      have hprod : ‖h * (h + 2 * a₀)‖ ≤ ε' := by
        have : h * (h + 2 * a₀) = (t - a₀ ^ 2) - (t - (a₀ + h) ^ 2) := by ring
        rw [this]; exact (norm_sub_le_max _ _).trans (max_le ha₀t hle)
      by_cases hh : ‖h‖ ≤ ‖2 * a₀‖
      · calc ‖h‖ ^ 2 ≤ ‖2 * a₀‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
          _ = ‖(4 : F) * t‖ := h2a₀
          _ ≤ ε' := h4
      · rw [not_le] at hh
        have hn : ‖h + 2 * a₀‖ = ‖h‖ :=
          by rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hh.ne', max_eq_left hh.le]
        rw [norm_mul, hn, ← sq] at hprod
        exact hprod
    · intro hh
      rw [hexp]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha₀t ?_)
      rw [norm_neg, norm_mul]
      have hh1 : ‖h‖ * ‖h + 2 * a₀‖ ≤ ‖h‖ * max ‖h‖ ‖2 * a₀‖ :=
        mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_add_le_max _ _) (norm_nonneg _)
      refine hh1.trans ?_
      rcases le_total ‖h‖ ‖2 * a₀‖ with hc | hc
      · rw [max_eq_right hc]

        have hsq : (‖h‖ * ‖2 * a₀‖) ^ 2 ≤ ε' ^ 2 := by
          rw [mul_pow, h2a₀, sq ε']
          exact mul_le_mul hh h4 (norm_nonneg _) hε0
        exact (pow_le_pow_iff_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hε0 two_ne_zero).1 hsq
      · rw [max_eq_left hc, ← sq]; exact hh
  ext a
  simp only [Set.mem_image, mem_fibre]
  constructor
  · rintro ⟨haD, hat⟩
    refine ⟨a - a₀, ⟨?_, ?_⟩, by ring⟩
    ·
      exact (norm_sub_le_max _ _).trans (max_le haD ha₀D)
    · rw [zero_sub, norm_neg, norm_pow]
      have := (key (a - a₀)).1 (by rwa [add_sub_cancel])
      exact this
  · rintro ⟨h, ⟨hhD, hh0⟩, rfl⟩
    rw [zero_sub, norm_neg, norm_pow] at hh0
    refine ⟨?_, (key h).2 hh0⟩

    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha₀D hhD)

end Fibres

section Functional

variable {F : Type*} [NontriviallyNormedField F]

theorem secondCountableTopology_units [SecondCountableTopology F] : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

attribute [local instance] secondCountableTopology_units

def chartFn (Θ : Matrix (Fin 2) (Fin 2) F → ℂ) (t : F) : Fˣ × F → ℂ :=
  fun q => Θ (1 + Y t q.2 (q.1 : F))

theorem chartFn_apply (Θ : Matrix (Fin 2) (Fin 2) F → ℂ) (t : F) (b : Fˣ) (a : F) :
    chartFn Θ t (b, a) = Θ (1 + Y t a b) := rfl

theorem continuous_chart (t : F) :
    Continuous fun q : Fˣ × F => (1 : Matrix (Fin 2) (Fin 2) F) + Y t q.2 (q.1 : F) := by
  refine continuous_const.add (continuous_matrix fun i j => ?_)
  have hb : Continuous fun q : Fˣ × F => ((q.1 : Fˣ) : F) := Units.continuous_val.comp continuous_fst
  have hbi : Continuous fun q : Fˣ × F => (((q.1⁻¹ : Fˣ) : Fˣ) : F) :=
    Units.continuous_val.comp (continuous_fst.inv)
  have ha : Continuous fun q : Fˣ × F => q.2 := continuous_snd
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · show Continuous fun q : Fˣ × F => (t - q.2 ^ 2) / ((q.1 : Fˣ) : F)
    have : (fun q : Fˣ × F => (t - q.2 ^ 2) / ((q.1 : Fˣ) : F)) =
        fun q : Fˣ × F => (t - q.2 ^ 2) * (((q.1⁻¹ : Fˣ) : Fˣ) : F) := by
      funext q; rw [div_eq_mul_inv, Units.val_inv_eq_inv_val]
    rw [this]
    exact (continuous_const.sub (ha.pow 2)).mul hbi
  · show Continuous fun q : Fˣ × F => -q.2
    exact ha.neg

theorem continuous_quot (t : F) : Continuous fun q : Fˣ × F => (t - q.2 ^ 2) / ((q.1 : Fˣ) : F) := by
  have h := (continuous_chart t).matrix_elem 1 0
  convert h using 1
  funext q
  simp [Matrix.add_apply, Y]

theorem isCompact_units_annulus [ProperSpace F] {r₁ : ℝ} (r₂ : ℝ) (hr₁ : 0 < r₁) :
    IsCompact {b : Fˣ | r₁ ≤ ‖(b : F)‖ ∧ ‖(b : F)‖ ≤ r₂} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have himg : ((↑) : Fˣ → F) '' {b : Fˣ | r₁ ≤ ‖(b : F)‖ ∧ ‖(b : F)‖ ≤ r₂} =
      {x : F | r₁ ≤ ‖x‖} ∩ Metric.closedBall (0 : F) r₂ := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨b, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hx : x ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact (lt_irrefl _ (hr₁.trans_le h1))
      exact ⟨Units.mk0 x hx, ⟨h1, h2⟩, rfl⟩
  rw [himg]
  exact (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const continuous_norm)

def Rset (D : ℝ) (t : F) : Set (Fˣ × F) :=
  {q | ‖q.2‖ ≤ D ∧ ‖((q.1 : Fˣ) : F)‖ ≤ D ∧ ‖t - q.2 ^ 2‖ ≤ D * ‖((q.1 : Fˣ) : F)‖}

theorem mem_Rset {D : ℝ} {t : F} {q : Fˣ × F} :
    q ∈ Rset D t ↔ ‖q.2‖ ≤ D ∧ ‖((q.1 : Fˣ) : F)‖ ≤ D ∧ ‖t - q.2 ^ 2‖ ≤ D * ‖((q.1 : Fˣ) : F)‖ :=
  Iff.rfl

theorem isClosed_Rset (D : ℝ) (t : F) : IsClosed (Rset D t) := by
  have h1 : Continuous fun q : Fˣ × F => ‖q.2‖ := continuous_norm.comp continuous_snd
  have h2 : Continuous fun q : Fˣ × F => ‖((q.1 : Fˣ) : F)‖ :=
    continuous_norm.comp (Units.continuous_val.comp continuous_fst)
  have h3 : Continuous fun q : Fˣ × F => ‖t - q.2 ^ 2‖ :=
    continuous_norm.comp (continuous_const.sub ((continuous_snd).pow 2))
  exact (isClosed_le h1 continuous_const).inter
    ((isClosed_le h2 continuous_const).inter (isClosed_le h3 (continuous_const.mul h2)))

theorem preimage_mk_Rset (D : ℝ) (t : F) (b : Fˣ) :
    Prod.mk b ⁻¹' Rset D t = if ‖(b : F)‖ ≤ D then fibre D t (D * ‖(b : F)‖) else ∅ := by
  ext a
  simp only [Set.mem_preimage, mem_Rset, mem_fibre]
  split_ifs with hb
  · simp only [mem_fibre]; tauto
  · simp only [Set.mem_empty_iff_false, iff_false]; tauto

variable [IsUltrametricDist F]

theorem exists_pos_le_norm_sub_sq [ProperSpace F] {t : F} (ht : ¬ IsSquare t) (D : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ a : F, ‖a‖ ≤ D → m ≤ ‖t - a ^ 2‖ := by
  by_cases hD : (Metric.closedBall (0 : F) D).Nonempty
  · have hcont : Continuous fun a : F => ‖t - a ^ 2‖ := continuous_norm.comp (continuous_const.sub (continuous_id.pow 2))
    obtain ⟨a₀, -, hmin⟩ := (isCompact_closedBall (0 : F) D).exists_isMinOn hD hcont.continuousOn
    refine ⟨‖t - a₀ ^ 2‖, norm_pos_iff.2 (fun h => ht ⟨a₀, by rw [sub_eq_zero.1 h, sq]⟩), fun a ha => ?_⟩
    exact hmin (by simpa using ha)
  · refine ⟨1, one_pos, fun a ha => ?_⟩
    exact absurd ⟨a, by simpa using ha⟩ hD

theorem Rset_subset_compact [ProperSpace F] {t : F} (ht : ¬ IsSquare t) {D : ℝ} (hD : 0 < D) :
    ∃ S : Set (Fˣ × F), IsCompact S ∧ Rset D t ⊆ S := by
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_norm_sub_sq ht D
  refine ⟨{b : Fˣ | m / D ≤ ‖(b : F)‖ ∧ ‖(b : F)‖ ≤ D} ×ˢ Metric.closedBall (0 : F) D,
    (isCompact_units_annulus D (div_pos hm hD)).prod (isCompact_closedBall _ _), ?_⟩
  rintro ⟨b, a⟩ ⟨ha, hb, hc⟩
  refine ⟨⟨?_, hb⟩, by simpa using ha⟩
  rw [div_le_iff₀ hD, mul_comm]
  exact (hmle a ha).trans hc

variable [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]

omit [IsUltrametricDist F] in
theorem measurableSet_Rset (D : ℝ) (t : F) : MeasurableSet (Rset D t) :=
  (isClosed_Rset D t).measurableSet

theorem measure_Rset_eq_lintegral (D : ℝ) (t : F) :
    (ν.prod μ) (Rset D t) =
      ∫⁻ b, {b : Fˣ | ‖(b : F)‖ ≤ D}.indicator (fun b => μ (fibre D t (D * ‖(b : F)‖))) b ∂ν := by
  rw [Measure.prod_apply (measurableSet_Rset D t)]
  refine lintegral_congr fun b => ?_
  rw [preimage_mk_Rset]
  by_cases hb : ‖(b : F)‖ ≤ D
  · rw [if_pos hb, Set.indicator_of_mem (by exact hb)]
  · rw [if_neg hb, Set.indicator_of_notMem (by exact hb), measure_empty]

theorem measure_Rset_lt_top_of_not_isSquare {t : F} (ht : ¬ IsSquare t) {D : ℝ} (hD : 0 < D) :
    (ν.prod μ) (Rset D t) < ⊤ := by
  obtain ⟨S, hS, hsub⟩ := Rset_subset_compact ht hD
  exact (measure_mono hsub).trans_lt hS.measure_lt_top

omit [IsUltrametricDist F] [MeasurableSpace Fˣ] [BorelSpace Fˣ] in

theorem exists_measure_image_mul (π : F) (hπ : π ≠ 0) :
    ∃ c : ℝ≥0∞, ∀ S : Set F, μ ((fun a => π * a) '' S) = c * μ S := by
  set e : F ≃+ F := AddAut.mulLeft' (Units.mk0 π hπ)⁻¹ with he
  have hecoe : ∀ a, e a = π⁻¹ * a := fun a => rfl
  have hec : Continuous e := continuous_const.mul continuous_id
  have hesc : Continuous e.symm := by
    have : (e.symm : F → F) = fun a => π * a := by
      funext a; apply e.injective
      rw [e.apply_symm_apply, hecoe, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
    rw [this]; exact continuous_const.mul continuous_id
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ hec hesc
  set θ := (Measure.map e μ).addHaarScalarFactor μ with hθ
  have hmap : Measure.map e μ = θ • μ := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨θ, fun S => ?_⟩
  have hme : MeasurableEmbedding e := by
    have : (e : F → F) = (Homeomorph.mulLeft₀ π⁻¹ (inv_ne_zero hπ) : F → F) := by funext a; rfl
    rw [this]; exact (Homeomorph.mulLeft₀ π⁻¹ (inv_ne_zero hπ)).measurableEmbedding
  have himg : (fun a => π * a) '' S = e ⁻¹' S := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, hecoe]
    constructor
    · rintro ⟨a, ha, rfl⟩; rwa [← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
    · intro hx; exact ⟨π⁻¹ * x, hx, by rw [← mul_assoc, mul_inv_cancel₀ hπ, one_mul]⟩
  rw [himg, ← hme.map_apply, hmap, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

omit [ProperSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ] in

theorem scale_le_half {π : F} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) {c : ℝ≥0∞}
    (hc : ∀ S : Set F, μ ((fun a => π * a) '' S) = c * μ S) {x₁ : F} (hx₁ : x₁ ≠ 0)
    (hfin : μ (Metric.closedBall (0 : F) ‖x₁‖) < ⊤) : c ≤ 2⁻¹ := by
  set D : ℝ := ‖x₁‖ with hD
  have hDpos : 0 < D := norm_pos_iff.2 hx₁
  set b₀ : Set F := Metric.closedBall (0 : F) D with hb₀
  set b₁ : Set F := (fun a => π * a) '' b₀ with hb₁
  have hb₁sub : b₁ ⊆ b₀ := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [hb₀, Metric.mem_closedBall, dist_zero_right, norm_mul] at ha ⊢
    calc ‖π‖ * ‖a‖ ≤ 1 * D := mul_le_mul hπ1.le ha (norm_nonneg _) zero_le_one
      _ = D := one_mul D
  have hb₁norm : ∀ y ∈ b₁, ‖y‖ < D := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [hb₀, Metric.mem_closedBall, dist_zero_right] at ha
    rw [norm_mul]
    calc ‖π‖ * ‖a‖ ≤ ‖π‖ * D := mul_le_mul_of_nonneg_left ha (norm_nonneg _)
      _ < 1 * D := mul_lt_mul_of_pos_right hπ1 hDpos
      _ = D := one_mul D
  set b₂ : Set F := (fun y => -x₁ + y) ⁻¹' b₁ with hb₂
  have hb₂norm : ∀ y ∈ b₂, ‖y‖ = D := by
    intro y hy
    have h1 := hb₁norm _ hy
    have : y = x₁ + (-x₁ + y) := by rw [add_neg_cancel_left]
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne', max_eq_left h1.le]
  have hb₂sub : b₂ ⊆ b₀ := by
    intro y hy
    simp only [hb₀, Metric.mem_closedBall, dist_zero_right]
    exact (hb₂norm y hy).le
  have hdisj : Disjoint b₁ b₂ := by
    rw [Set.disjoint_left]
    intro y hy hy'
    have h1 := hb₁norm _ hy
    rw [hb₂norm y hy'] at h1; exact lt_irrefl _ h1
  have hb₂meas : μ b₂ = μ b₁ := by rw [hb₂, measure_preimage_add]
  have hb₁meas : MeasurableSet b₁ := by
    have : b₁ = (fun a => π⁻¹ * a) ⁻¹' b₀ := by
      ext x
      simp only [hb₁, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨a, ha, rfl⟩; rwa [← mul_assoc, inv_mul_cancel₀ hπ0, one_mul]
      · intro hx; exact ⟨π⁻¹ * x, hx, by rw [← mul_assoc, mul_inv_cancel₀ hπ0, one_mul]⟩
    rw [this]; exact measurableSet_closedBall.preimage (measurable_const_mul _)
  have hb₂m : MeasurableSet b₂ := hb₁meas.preimage (measurable_const_add _)
  have hkey : μ b₁ + μ b₁ ≤ μ b₀ := by
    calc μ b₁ + μ b₁ = μ b₁ + μ b₂ := by rw [hb₂meas]
      _ = μ (b₁ ∪ b₂) := (measure_union hdisj hb₂m).symm
      _ ≤ μ b₀ := measure_mono (Set.union_subset hb₁sub hb₂sub)
  have hpos : μ b₀ ≠ 0 := (Metric.measure_closedBall_pos μ _ hDpos).ne'
  have h1 : μ b₀ * (2 * c) ≤ μ b₀ * 1 := by
    rw [mul_one, mul_comm, two_mul, add_mul, ← hc b₀]; exact hkey
  have h2 : 2 * c ≤ 1 := (ENNReal.mul_le_mul_iff_right hpos hfin.ne).1 h1
  calc c = 2⁻¹ * (2 * c) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2⁻¹ * 1 := mul_le_mul_right h2 _
    _ = 2⁻¹ := mul_one _

omit [IsUltrametricDist F] [ProperSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ] in

theorem measure_image_pow_mul {π : F} {c : ℝ≥0∞} (hc : ∀ S : Set F, μ ((fun a => π * a) '' S) = c * μ S)
    (k : ℕ) (S : Set F) : μ ((fun a => π ^ k * a) '' S) = c ^ k * μ S := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : (fun a : F => π ^ (k + 1) * a) '' S = (fun a => π * a) '' ((fun a => π ^ k * a) '' S) := by
      rw [Set.image_image]; congr 1; funext a; ring
    rw [this, hc, ih, pow_succ]; ring

omit [IsUltrametricDist F] [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ]
  [BorelSpace Fˣ] in
theorem closedBall_mul_pow_eq_image {π : F} (hπ : π ≠ 0) (D : ℝ) (k : ℕ) :
    Metric.closedBall (0 : F) (D * ‖π‖ ^ k) = (fun a => π ^ k * a) '' Metric.closedBall (0 : F) D := by
  ext y
  simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_image]
  have hπk : π ^ k ≠ 0 := pow_ne_zero _ hπ
  have hπkn : 0 < ‖π ^ k‖ := norm_pos_iff.2 hπk
  constructor
  · intro hy
    refine ⟨(π ^ k)⁻¹ * y, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hπk, one_mul]⟩
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hπkn, norm_pow, mul_comm]; exact hy
  · rintro ⟨a, ha, rfl⟩
    rw [norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right ha (pow_nonneg (norm_nonneg _) _)

theorem measure_Rset_zero_lt_top {D : ℝ} (hD : 0 < D) : (ν.prod μ) (Rset D (0 : F)) < ⊤ := by

  obtain ⟨x₁, hx₁⟩ := NormedField.exists_lt_norm F D
  set D' : ℝ := ‖x₁‖ with hD'
  have hDD' : D ≤ D' := hx₁.le
  have hD'pos : 0 < D' := hD.trans hx₁
  have hx₁0 : x₁ ≠ 0 := norm_pos_iff.1 hD'pos
  have hsub0 : Rset D (0 : F) ⊆ Rset D' 0 := by
    rintro ⟨b, a⟩ ⟨ha, hb, hc⟩
    exact ⟨ha.trans hDD', hb.trans hDD', hc.trans (mul_le_mul_of_nonneg_right hDD' (norm_nonneg _))⟩
  refine (measure_mono hsub0).trans_lt ?_

  obtain ⟨π, hπ0, hπ1⟩ := NormedField.exists_norm_lt_one F
  have hπne : π ≠ 0 := norm_pos_iff.1 hπ0
  obtain ⟨c, hc⟩ := exists_measure_image_mul μ π hπne
  have hchalf : c ≤ 2⁻¹ := scale_le_half μ hπne hπ1 hc hx₁0 (isCompact_closedBall _ _).measure_lt_top
  set r : ℝ := ‖π‖ ^ 2 with hr
  have hr0 : 0 < r := pow_pos hπ0 2
  have hr1 : r < 1 := pow_lt_one₀ (norm_nonneg _) hπ1 two_ne_zero

  set T : ℕ → Set Fˣ := fun n => {b | D' * r ^ (n + 1) < ‖(b : F)‖ ∧ ‖(b : F)‖ ≤ D' * r ^ n} with hT
  set A : ℕ → Set F := fun n => Metric.closedBall (0 : F) (D' * ‖π‖ ^ n) with hA

  have hcover : Rset D' (0 : F) ⊆ ⋃ n, T n ×ˢ A n := by
    rintro ⟨b, a⟩ ⟨ha, hb, hc⟩
    simp only [zero_sub, norm_neg, norm_pow] at hc
    have hbpos : 0 < ‖(b : F)‖ := norm_pos_iff.2 b.ne_zero
    have hex : ∃ n : ℕ, D' * r ^ (n + 1) < ‖(b : F)‖ := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hbpos hD'pos) hr1
      refine ⟨n, ?_⟩
      rw [lt_div_iff₀ hD'pos] at hn
      calc D' * r ^ (n + 1) ≤ D' * r ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_succ n)) hD'pos.le
        _ = r ^ n * D' := mul_comm _ _
        _ < ‖(b : F)‖ := hn
    classical
    set n := Nat.find hex with hn
    have hn1 : D' * r ^ (n + 1) < ‖(b : F)‖ := Nat.find_spec hex
    have hn2 : ‖(b : F)‖ ≤ D' * r ^ n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, pow_zero, mul_one]; exact hb
      · have hlt : n - 1 < Nat.find hex := by rw [← hn]; omega
        have := Nat.find_min hex hlt
        rw [Nat.sub_add_cancel hpos] at this
        exact not_lt.1 this
    refine Set.mem_iUnion.2 ⟨n, ⟨hn1, hn2⟩, ?_⟩
    simp only [hA, Metric.mem_closedBall, dist_zero_right]
    have h2 : ‖a‖ ^ 2 ≤ (D' * ‖π‖ ^ n) ^ 2 := by
      calc ‖a‖ ^ 2 ≤ D' * ‖(b : F)‖ := hc
        _ ≤ D' * (D' * r ^ n) := mul_le_mul_of_nonneg_left hn2 hD'pos.le
        _ = (D' * ‖π‖ ^ n) ^ 2 := by rw [hr, ← pow_mul, mul_comm 2 n, pow_mul]; ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

  have hT0fin : ν (T 0) < ⊤ := by
    refine (measure_mono ?_).trans_lt ((isCompact_units_annulus (D' * r ^ 0) (mul_pos hD'pos (pow_pos hr0 1))).measure_lt_top)
    intro b hb; exact ⟨hb.1.le, hb.2⟩
  have hTn : ∀ n, ν (T n) = ν (T 0) := by
    intro n
    set u : Fˣ := Units.mk0 π hπne ^ (2 * n) with hu
    have hun : ‖(u : F)‖ = r ^ n := by rw [hu, Units.val_pow_eq_pow_val, Units.val_mk0, norm_pow, hr, ← pow_mul]
    have : T n = (fun b => u⁻¹ * b) ⁻¹' T 0 := by
      ext b
      simp only [hT, Set.mem_setOf_eq, Set.mem_preimage, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
        norm_inv, hun, pow_zero, mul_one, zero_add, pow_one]
      have hrn : 0 < r ^ n := pow_pos hr0 n
      rw [← div_eq_inv_mul, lt_div_iff₀ hrn, div_le_iff₀ hrn]
      constructor
      · rintro ⟨h1, h2⟩; refine ⟨?_, ?_⟩ <;> [rw [pow_succ] at h1; skip] <;> nlinarith
      · rintro ⟨h1, h2⟩; refine ⟨?_, ?_⟩ <;> [rw [pow_succ]; skip] <;> nlinarith
    rw [this, measure_preimage_mul]
  have hAn : ∀ n, μ (A n) = c ^ n * μ (Metric.closedBall (0 : F) D') := by
    intro n; rw [hA]; simp only; rw [closedBall_mul_pow_eq_image hπne, measure_image_pow_mul μ hc]
  have hA0fin : μ (Metric.closedBall (0 : F) D') < ⊤ := (isCompact_closedBall _ _).measure_lt_top

  calc (ν.prod μ) (Rset D' (0 : F)) ≤ (ν.prod μ) (⋃ n, T n ×ˢ A n) := measure_mono hcover
    _ ≤ ∑' n, (ν.prod μ) (T n ×ˢ A n) := measure_iUnion_le _
    _ = ∑' n, ν (T 0) * μ (Metric.closedBall (0 : F) D') * c ^ n := by
        congr 1; funext n; rw [Measure.prod_prod, hTn, hAn]; ring
    _ = ν (T 0) * μ (Metric.closedBall (0 : F) D') * ∑' n, c ^ n := ENNReal.tsum_mul_left
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hT0fin hA0fin) ?_
        rw [ENNReal.tsum_geometric]
        refine ENNReal.inv_lt_top.2 (tsub_pos_of_lt (hchalf.trans_lt ?_))
        norm_num

end Functional

section ClaimB

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
  [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]

attribute [local instance] secondCountableTopology_units

omit [IsUltrametricDist F] [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ]
  [BorelSpace Fˣ] in

theorem exists_norm_lt_ne_zero {m : ℝ} (hm : 0 < m) : ∃ y : F, y ≠ 0 ∧ ‖y‖ < m := by
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one F
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hm hx1
  exact ⟨x ^ n, pow_ne_zero _ (norm_pos_iff.1 hx0), by rw [norm_pow]; exact hn⟩

theorem measure_fibre_le {δ : ℝ} {t : F} (ht : ¬ IsSquare t) (b : Fˣ) :
    μ (Prod.mk b ⁻¹' Rset δ t) ≤
      {b : Fˣ | ‖(4 : F) * t‖ ≤ δ * ‖(b : F)‖}.indicator (fun b => μ (Prod.mk b ⁻¹' Rset δ (0 : F))) b := by
  by_cases hb : ‖(b : F)‖ ≤ δ
  · by_cases hQ : ‖(4 : F) * t‖ ≤ δ * ‖(b : F)‖
    · rw [Set.indicator_of_mem (by exact hQ)]
      rw [preimage_mk_Rset, preimage_mk_Rset, if_pos hb, if_pos hb]
      by_cases hle : ‖t‖ ≤ δ * ‖(b : F)‖
      · rw [fibre_eq_of_le hle]
      · rw [not_le] at hle
        by_cases hne : (fibre δ t (δ * ‖(b : F)‖)).Nonempty
        · obtain ⟨a₀, ha₀⟩ := hne
          rw [fibre_eq_image_add hQ hle ha₀]
          have : (fun h => a₀ + h) '' fibre δ (0 : F) (δ * ‖(b : F)‖) =
              (fun x => -a₀ + x) ⁻¹' fibre δ (0 : F) (δ * ‖(b : F)‖) := by
            ext x; simp only [Set.mem_image, Set.mem_preimage]
            constructor
            · rintro ⟨h, hh, rfl⟩; rwa [neg_add_cancel_left]
            · intro hx; exact ⟨-a₀ + x, hx, by rw [add_neg_cancel_left]⟩
          rw [this, measure_preimage_add]
        · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]; exact bot_le
    · rw [Set.indicator_of_notMem (by exact hQ), preimage_mk_Rset, if_pos hb]
      rw [not_le] at hQ
      have hempty : fibre δ t (δ * ‖(b : F)‖) = ∅ := by
        ext a
        simp only [mem_fibre, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hat
        exact ht (isSquare_of_norm_sub_sq_lt (hat.trans_lt hQ))
      rw [hempty, measure_empty]
  · rw [preimage_mk_Rset, if_neg hb, measure_empty]; exact bot_le

theorem measure_Rset_lt {δ : ℝ} (hδ : 0 < δ) {t : F} (ht : ¬ IsSquare t) (h4 : (4 : F) ≠ 0) :
    (ν.prod μ) (Rset δ t) < (ν.prod μ) (Rset δ (0 : F)) := by
  have ht0 : t ≠ 0 := fun h => ht ⟨0, by rw [h, mul_zero]⟩
  have h4t : 0 < ‖(4 : F) * t‖ := norm_pos_iff.2 (mul_ne_zero h4 ht0)
  set f : F → Fˣ → ℝ≥0∞ := fun s b => μ (Prod.mk b ⁻¹' Rset δ s) with hf
  have hfm : ∀ s, Measurable (f s) := fun s => measurable_measure_prodMk_left (measurableSet_Rset δ s)
  have hRs : ∀ s, (ν.prod μ) (Rset δ s) = ∫⁻ b, f s b ∂ν := fun s => Measure.prod_apply (measurableSet_Rset δ s)
  set Q : Set Fˣ := {b | ‖(4 : F) * t‖ ≤ δ * ‖(b : F)‖} with hQ
  have hQm : MeasurableSet Q :=
    (isClosed_le continuous_const (continuous_const.mul (continuous_norm.comp Units.continuous_val))).measurableSet

  have hle : (ν.prod μ) (Rset δ t) ≤ ∫⁻ b, Q.indicator (f 0) b ∂ν := by
    rw [hRs]
    exact lintegral_mono fun b => measure_fibre_le μ ht b

  have hsplit : (ν.prod μ) (Rset δ (0 : F)) = (∫⁻ b, Q.indicator (f 0) b ∂ν) + ∫⁻ b, Qᶜ.indicator (f 0) b ∂ν := by
    rw [hRs, ← lintegral_add_left ((hfm 0).indicator hQm)]
    congr 1; funext b; exact (Set.indicator_self_add_compl_apply Q (f 0) b).symm

  have hfin : (∫⁻ b, Q.indicator (f 0) b ∂ν) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_Rset_zero_lt_top μ ν hδ).ne ?_
    rw [hRs]
    exact lintegral_mono fun b => Set.indicator_le_self _ _ _

  have hpos : (∫⁻ b, Qᶜ.indicator (f 0) b ∂ν) ≠ 0 := by
    obtain ⟨y, hy0, hy⟩ := exists_norm_lt_ne_zero (F := F) (lt_min hδ (div_pos h4t hδ))
    set b₀ : Fˣ := Units.mk0 y hy0 with hb₀
    have hb₀n : ‖(b₀ : F)‖ = ‖y‖ := rfl
    have hyδ : ‖y‖ ≤ δ := (hy.trans_le (min_le_left _ _)).le
    have hyQ : δ * ‖y‖ < ‖(4 : F) * t‖ := by
      have := hy.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ hδ, mul_comm] at this
    set P₀ : Set Fˣ := {b | ‖(b : F)‖ = ‖y‖} with hP₀
    have hP₀m : MeasurableSet P₀ := by
      have hopen : IsOpen P₀ := by
        have := (IsUltrametricDist.isOpen_sphere (0 : F) (norm_pos_iff.2 hy0).ne').preimage Units.continuous_val
        convert this using 1; ext b; simp [hP₀]
      exact hopen.measurableSet
    have hP₀pos : ν P₀ ≠ 0 := by
      have hopen : IsOpen P₀ := by
        have := (IsUltrametricDist.isOpen_sphere (0 : F) (norm_pos_iff.2 hy0).ne').preimage Units.continuous_val
        convert this using 1; ext b; simp [hP₀]
      exact (hopen.measure_pos ν ⟨b₀, by simp [hP₀, hb₀n]⟩).ne'

    set r : ℝ := min δ (min 1 (δ * ‖y‖)) with hr
    have hr0 : 0 < r := lt_min hδ (lt_min one_pos (mul_pos hδ (norm_pos_iff.2 hy0)))
    set v₀ : ℝ≥0∞ := μ (Metric.closedBall (0 : F) r) with hv₀
    have hv₀pos : v₀ ≠ 0 := (Metric.measure_closedBall_pos μ _ hr0).ne'
    have hlow : ∀ b, P₀.indicator (fun _ => v₀) b ≤ Qᶜ.indicator (f 0) b := by
      intro b
      by_cases hb : b ∈ P₀
      · have hbn : ‖(b : F)‖ = ‖y‖ := hb
        have hbQ : b ∈ Qᶜ := by
          simp only [Set.mem_compl_iff, hQ, Set.mem_setOf_eq, not_le, hbn]; exact hyQ
        rw [Set.indicator_of_mem hb, Set.indicator_of_mem hbQ, hf]
        simp only
        rw [preimage_mk_Rset, if_pos (by rw [hbn]; exact hyδ)]
        refine measure_mono fun a ha => ?_
        simp only [Metric.mem_closedBall, dist_zero_right] at ha
        rw [fibre_zero]
        refine ⟨ha.trans (min_le_left _ _), ?_⟩
        have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
        have hrε : r ≤ δ * ‖y‖ := (min_le_right _ _).trans (min_le_right _ _)
        rw [hbn]
        calc ‖a‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
          _ ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1 one_le_two
          _ = r := pow_one r
          _ ≤ δ * ‖y‖ := hrε
      · rw [Set.indicator_of_notMem hb]; exact bot_le
    have hlow' : v₀ * ν P₀ ≤ ∫⁻ b, Qᶜ.indicator (f 0) b ∂ν := by
      rw [← lintegral_indicator_const hP₀m]
      exact lintegral_mono hlow
    exact fun h0 => (mul_ne_zero hv₀pos hP₀pos) (le_zero_iff.1 (h0 ▸ hlow'))
  calc (ν.prod μ) (Rset δ t) ≤ ∫⁻ b, Q.indicator (f 0) b ∂ν := hle
    _ < (∫⁻ b, Q.indicator (f 0) b ∂ν) + ∫⁻ b, Qᶜ.indicator (f 0) b ∂ν := ENNReal.lt_add_right hfin hpos
    _ = (ν.prod μ) (Rset δ (0 : F)) := hsplit.symm

end ClaimB

section ClaimA

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
  [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]

attribute [local instance] secondCountableTopology_units

omit [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ] in

theorem bounds_of_chartFn_ne_zero {Ψ : Matrix (Fin 2) (Fin 2) F → ℂ} {B : ℝ} (hB : 1 ≤ B)
    (hsupp : ∀ M, Ψ M ≠ 0 → EntryLE M B) {s : F} {b : Fˣ} {a : F} (h : chartFn Ψ s (b, a) ≠ 0) :
    ‖a‖ ≤ B ∧ ‖(b : F)‖ ≤ B ∧ ‖s - a ^ 2‖ ≤ B * ‖(b : F)‖ := by
  have hE := entryLE_of_entryLE_one_add hB (hsupp _ h)
  refine ⟨by simpa using hE 0 0, by simpa using hE 0 1, ?_⟩
  have h10 : ‖(s - a ^ 2) / (b : F)‖ ≤ B := by simpa using hE 1 0
  rwa [norm_div, div_le_iff₀ (norm_pos_iff.2 b.ne_zero)] at h10

theorem integrable_of_bounded_of_support_subset {X : Type*} [MeasurableSpace X] {ρ : Measure X} {f : X → ℂ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {S : Set X} (hS : ρ S ≠ ⊤)
    (hsupp : Function.support f ⊆ S) : Integrable f ρ := by
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  exact Measure.integrableOn_of_bounded hS hf.aestronglyMeasurable (ae_of_all _ fun x => hC x)

def SII (δ B : ℝ) (s : F) : Set (Fˣ × F) :=
  {q | ‖q.2‖ ≤ δ ∧ δ * ‖((q.1 : Fˣ) : F)‖ < ‖s - q.2 ^ 2‖ ∧ ‖s - q.2 ^ 2‖ ≤ B * ‖((q.1 : Fˣ) : F)‖}

omit [IsUltrametricDist F] in
theorem measurableSet_SII (δ B : ℝ) (s : F) : MeasurableSet (SII δ B s) := by
  have h1 : Continuous fun q : Fˣ × F => ‖q.2‖ := continuous_norm.comp continuous_snd
  have h2 : Continuous fun q : Fˣ × F => ‖((q.1 : Fˣ) : F)‖ :=
    continuous_norm.comp (Units.continuous_val.comp continuous_fst)
  have h3 : Continuous fun q : Fˣ × F => ‖s - q.2 ^ 2‖ :=
    continuous_norm.comp (continuous_const.sub ((continuous_snd).pow 2))
  refine (isClosed_le h1 continuous_const).measurableSet.inter
    ((isOpen_lt (continuous_const.mul h2) h3).measurableSet.inter (isClosed_le h3 (continuous_const.mul h2)).measurableSet)

theorem measure_SII_lt_top {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) (s : F) : (ν.prod μ) (SII δ B s) < ⊤ := by
  set Ann : Set Fˣ := {b' | δ * ‖(b' : F)‖ < 1 ∧ 1 ≤ B * ‖(b' : F)‖} with hAnn
  have hAnnfin : ν Ann < ⊤ := by
    refine (measure_mono ?_).trans_lt ((isCompact_units_annulus (1 / δ) (r₁ := 1 / B) (by positivity)).measure_lt_top)
    rintro b' ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hB, mul_comm]; exact h2
    · rw [le_div_iff₀ hδ, mul_comm]; exact h1.le
  have hfib : ∀ a : F, ν ((fun b : Fˣ => (b, a)) ⁻¹' SII δ B s) ≤
      (Metric.closedBall (0 : F) δ).indicator (fun _ => ν Ann) a := by
    intro a
    by_cases ha : ‖a‖ ≤ δ
    · rw [Set.indicator_of_mem (by simpa using ha)]
      by_cases hκ : s - a ^ 2 = 0
      · have : (fun b : Fˣ => (b, a)) ⁻¹' SII δ B s = ∅ := by
          ext b
          simp only [Set.mem_preimage, SII, Set.mem_setOf_eq, hκ, norm_zero, Set.mem_empty_iff_false, iff_false,
            not_and, not_le]
          intro _ h
          exact absurd h (not_lt.2 (mul_nonneg hδ.le (norm_nonneg _)))
        rw [this, measure_empty]; exact bot_le
      · set u : Fˣ := Units.mk0 (s - a ^ 2) hκ with hu
        have hun : 0 < ‖(u : F)‖ := norm_pos_iff.2 hκ
        have hu' : ((u : Fˣ) : F) = s - a ^ 2 := rfl
        have : (fun b : Fˣ => (b, a)) ⁻¹' SII δ B s = (fun b => u⁻¹ * b) ⁻¹' Ann := by
          ext b
          have hmem1 : b ∈ (fun b : Fˣ => (b, a)) ⁻¹' SII δ B s ↔
              δ * ‖(b : F)‖ < ‖(u : F)‖ ∧ ‖(u : F)‖ ≤ B * ‖(b : F)‖ := by
            rw [hu']; exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨ha, h.1, h.2⟩⟩
          have hmem2 : b ∈ (fun b => u⁻¹ * b) ⁻¹' Ann ↔
              δ * (‖(b : F)‖ / ‖(u : F)‖) < 1 ∧ 1 ≤ B * (‖(b : F)‖ / ‖(u : F)‖) := by
            simp only [Set.mem_preimage, hAnn, Set.mem_setOf_eq, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
              norm_inv, inv_mul_eq_div, Units.val_div_eq_div_val, norm_div]
          rw [hmem1, hmem2, mul_div_assoc', mul_div_assoc', div_lt_one hun, le_div_iff₀ hun, one_mul]
        rw [this, measure_preimage_mul]
    · rw [Set.indicator_of_notMem (by simpa using ha)]
      have : (fun b : Fˣ => (b, a)) ⁻¹' SII δ B s = ∅ := by
        ext b
        simp only [Set.mem_preimage, SII, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h; exact absurd h ha
      rw [this, measure_empty]
  rw [Measure.prod_apply_symm (measurableSet_SII δ B s)]
  calc ∫⁻ a, ν ((fun b : Fˣ => (b, a)) ⁻¹' SII δ B s) ∂μ
      ≤ ∫⁻ a, (Metric.closedBall (0 : F) δ).indicator (fun _ => ν Ann) a ∂μ := lintegral_mono hfib
    _ = ν Ann * μ (Metric.closedBall (0 : F) δ) := lintegral_indicator_const measurableSet_closedBall _
    _ < ⊤ := ENNReal.mul_lt_top hAnnfin (isCompact_closedBall _ _).measure_lt_top

variable {μ ν}

theorem integrable_chartFn {Ψ : Matrix (Fin 2) (Fin 2) F → ℂ} {δ B C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hB : 1 ≤ B) (hinv : ∀ M E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Ψ (M + E) = Ψ M)
    (hsupp : ∀ M, Ψ M ≠ 0 → EntryLE M B) (hbdd : ∀ M, ‖Ψ M‖ ≤ C)
    (hvan1 : ∀ E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Ψ (1 + E) = 0) (hcont : Continuous Ψ)
    {t : F} (ht0 : t ≠ 0) (htB : ‖t‖ * B ≤ δ ^ 3) {s : F} (hs : ‖s‖ ≤ ‖t‖) :
    Integrable (chartFn Ψ s) (ν.prod μ) := by
  have hB0 : 0 < B := one_pos.trans_le hB
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht0
  set ρ : ℝ := ‖t‖ / δ with hρ
  have hρ0 : 0 < ρ := div_pos htn hδ
  have ht2 : ‖t‖ ≤ δ ^ 2 := by
    have h1 : ‖t‖ ≤ ‖t‖ * B := le_mul_of_one_le_right (norm_nonneg _) hB
    have h2 : δ ^ 3 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num)
    exact h1.trans (htB.trans h2)
  have hρδ : ρ ≤ δ := by rw [hρ, div_le_iff₀ hδ]; nlinarith [ht2]
  refine integrable_of_bounded_of_support_subset ((hcont.comp (continuous_chart s)).measurable) (fun q => hbdd _)
    (S := ({b : Fˣ | ρ ≤ ‖(b : F)‖ ∧ ‖(b : F)‖ ≤ B} ×ˢ Metric.closedBall (0 : F) B) ∪ SII δ B s) ?_ ?_
  · exact (measure_union_lt_top
      (by rw [Measure.prod_prod]
          exact ENNReal.mul_lt_top ((isCompact_units_annulus B hρ0).measure_lt_top)
            ((isCompact_closedBall _ _).measure_lt_top))
      (measure_SII_lt_top μ ν hδ hB0 s)).ne
  · rintro ⟨b, a⟩ hq
    rw [Function.mem_support] at hq
    obtain ⟨haB, hbB, hcB⟩ := bounds_of_chartFn_ne_zero hB hsupp hq
    by_cases hb : ρ ≤ ‖(b : F)‖
    · exact Or.inl ⟨⟨hb, hbB⟩, by simpa using haB⟩
    · right
      rw [not_le] at hb

      have haδ : ‖a‖ ≤ δ := by
        have h1 : ‖s - a ^ 2‖ ≤ δ ^ 2 := by
          calc ‖s - a ^ 2‖ ≤ B * ‖(b : F)‖ := hcB
            _ ≤ B * ρ := mul_le_mul_of_nonneg_left hb.le hB0.le
            _ = ‖t‖ * B / δ := by rw [hρ]; ring
            _ ≤ δ ^ 3 / δ := div_le_div_of_nonneg_right htB hδ.le
            _ = δ ^ 2 := by field_simp
        have h2 : ‖a‖ ^ 2 ≤ δ ^ 2 := by
          have : a ^ 2 = s - (s - a ^ 2) := by ring
          rw [← norm_pow, this]
          exact (norm_sub_le_max _ _).trans (max_le (hs.trans ht2) h1)
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).1 h2
      refine ⟨haδ, ?_, hcB⟩

      have hval : chartFn Ψ s (b, a) = Ψ (1 + E10 ((s - a ^ 2) / (b : F))) := by
        rw [chartFn_apply, one_add_Y_eq]
        exact hinv _ _ (entryLE_AB haδ (hb.le.trans hρδ))
      rw [hval] at hq
      by_contra hle
      rw [not_lt] at hle
      apply hq
      apply hvan1
      refine entryLE_E10 hδ.le ?_
      rw [norm_div, div_le_iff₀ (norm_pos_iff.2 b.ne_zero)]
      exact hle

theorem setIntegral_comp_div (ν : Measure Fˣ) [ν.IsHaarMeasure] (g : F → ℂ) (κ : Fˣ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ b in {b : Fˣ | ‖(b : F)‖ < ρ}, g ((κ : F) / (b : F)) ∂ν =
      ∫ b in {b : Fˣ | ‖(κ : F)‖ / ρ < ‖(b : F)‖}, g b ∂ν := by
  set e : Fˣ ≃ₜ Fˣ := (Homeomorph.inv Fˣ).trans (Homeomorph.mulLeft κ) with he
  have hecoe : ∀ b : Fˣ, e b = κ * b⁻¹ := fun b => rfl
  have hmp : MeasurePreserving e ν ν := by
    have : (e : Fˣ → Fˣ) = (fun b => κ * b) ∘ (fun b => b⁻¹) := by funext b; rfl
    rw [this]
    exact (measurePreserving_mul_left ν κ).comp (Measure.measurePreserving_inv ν)
  have hpre : e ⁻¹' {b : Fˣ | ‖(κ : F)‖ / ρ < ‖(b : F)‖} = {b : Fˣ | ‖(b : F)‖ < ρ} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hecoe, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
      norm_inv]
    have hκ : 0 < ‖(κ : F)‖ := norm_pos_iff.2 κ.ne_zero
    have hb : 0 < ‖(b : F)‖ := norm_pos_iff.2 b.ne_zero
    rw [← div_eq_mul_inv, div_lt_div_iff_of_pos_left hκ hρ hb]
  have key := hmp.setIntegral_preimage_emb e.measurableEmbedding (fun b : Fˣ => g (b : F))
    {b : Fˣ | ‖(κ : F)‖ / ρ < ‖(b : F)‖}
  rw [hpre] at key
  rw [← key]
  refine setIntegral_congr_fun ?_ (fun b _ => ?_)
  · exact (isOpen_lt (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
  · simp only [hecoe, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]

theorem setIntegral_tail_eq (ν : Measure Fˣ) [ν.IsHaarMeasure] (g : F → ℂ) {δ : ℝ}
    (hg : ∀ x : F, ‖x‖ ≤ δ → g x = 0) {θ : ℝ} (hθ : θ ≤ δ) :
    ∫ b in {b : Fˣ | θ < ‖(b : F)‖}, g b ∂ν = ∫ b, g b ∂ν := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun b hb => hg _ ?_)
  simp only [Set.mem_setOf_eq, not_lt] at hb
  exact hb.trans hθ

theorem inner_integral_eq (ν : Measure Fˣ) [ν.IsHaarMeasure] (g : F → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hg : ∀ x : F, ‖x‖ ≤ δ → g x = 0) {t : F} (ht0 : t ≠ 0) {a : F} (ha0 : a ≠ 0) (hta : t - a ^ 2 ≠ 0) :
    ∫ b in {b : Fˣ | ‖(b : F)‖ < ‖t‖ / δ}, g ((t - a ^ 2) / (b : F)) ∂ν =
      ∫ b in {b : Fˣ | ‖(b : F)‖ < ‖t‖ / δ}, g ((0 - a ^ 2) / (b : F)) ∂ν := by
  set ρ : ℝ := ‖t‖ / δ with hρdef
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht0
  have hρ : 0 < ρ := div_pos htn hδ
  have h0a : (0 : F) - a ^ 2 ≠ 0 := by rw [zero_sub, neg_ne_zero]; exact pow_ne_zero _ ha0
  set κ : Fˣ := Units.mk0 _ hta with hκ
  set κ' : Fˣ := Units.mk0 _ h0a with hκ'
  have h1 := setIntegral_comp_div ν g κ hρ
  have h1' := setIntegral_comp_div ν g κ' hρ
  simp only [hκ, hκ', Units.val_mk0] at h1 h1'
  rw [h1, h1']
  have hρid : ‖t‖ / ρ = δ := by rw [hρdef]; field_simp
  have hn0 : ‖(0 : F) - a ^ 2‖ = ‖a‖ ^ 2 := by rw [zero_sub, norm_neg, norm_pow]
  rcases lt_trichotomy (‖a‖ ^ 2) ‖t‖ with hlt | heq | hgt
  ·
    have hk : ‖t - a ^ 2‖ / ρ ≤ δ := by rw [norm_sub_sq_of_gt hlt, hρid]
    have hk' : ‖(0 : F) - a ^ 2‖ / ρ ≤ δ := by
      rw [hn0]
      calc ‖a‖ ^ 2 / ρ ≤ ‖t‖ / ρ := div_le_div_of_nonneg_right hlt.le hρ.le
        _ = δ := hρid
    rw [setIntegral_tail_eq ν g hg hk, setIntegral_tail_eq ν g hg hk']
  ·
    have hk : ‖t - a ^ 2‖ / ρ ≤ δ := by
      calc ‖t - a ^ 2‖ / ρ ≤ ‖t‖ / ρ := div_le_div_of_nonneg_right ((norm_sub_sq_le t a).trans (max_le le_rfl heq.le)) hρ.le
        _ = δ := hρid
    have hk' : ‖(0 : F) - a ^ 2‖ / ρ ≤ δ := by rw [hn0, heq, hρid]
    rw [setIntegral_tail_eq ν g hg hk, setIntegral_tail_eq ν g hg hk']
  ·
    rw [norm_sub_sq_of_lt hgt, hn0]

theorem integral_chartFn_eq_zero_param {Ψ : Matrix (Fin 2) (Fin 2) F → ℂ} {δ B C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hB : 1 ≤ B) (hinv : ∀ M E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Ψ (M + E) = Ψ M)
    (hsupp : ∀ M, Ψ M ≠ 0 → EntryLE M B) (hbdd : ∀ M, ‖Ψ M‖ ≤ C)
    (hvan1 : ∀ E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Ψ (1 + E) = 0) (hcont : Continuous Ψ)
    {t : F} (ht0 : t ≠ 0) (htB : ‖t‖ * B ≤ δ ^ 3) :
    ∫ q, chartFn Ψ t q ∂(ν.prod μ) = ∫ q, chartFn Ψ 0 q ∂(ν.prod μ) := by
  have hB0 : 0 < B := one_pos.trans_le hB
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht0
  set ρ : ℝ := ‖t‖ / δ with hρdef
  have hρ : 0 < ρ := div_pos htn hδ
  have ht2 : ‖t‖ ≤ δ ^ 2 := by
    have h1 : ‖t‖ ≤ ‖t‖ * B := le_mul_of_one_le_right (norm_nonneg _) hB
    have h2 : δ ^ 3 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num)
    exact h1.trans (htB.trans h2)
  have hρδ : ρ ≤ δ := by rw [hρdef, div_le_iff₀ hδ]; nlinarith [ht2]
  have h0t : ‖(0 : F)‖ ≤ ‖t‖ := by rw [norm_zero]; exact norm_nonneg _
  have hint : Integrable (chartFn Ψ t) (ν.prod μ) :=
    integrable_chartFn hδ hδ1 hB hinv hsupp hbdd hvan1 hcont ht0 htB le_rfl
  have hint0 : Integrable (chartFn Ψ 0) (ν.prod μ) :=
    integrable_chartFn hδ hδ1 hB hinv hsupp hbdd hvan1 hcont ht0 htB h0t

  set R₁ : Set (Fˣ × F) := {q | ρ ≤ ‖((q.1 : Fˣ) : F)‖} with hR₁
  have hcont1 : Continuous fun q : Fˣ × F => ‖((q.1 : Fˣ) : F)‖ :=
    continuous_norm.comp (Units.continuous_val.comp continuous_fst)
  have hR₁m : MeasurableSet R₁ := (isClosed_le continuous_const hcont1).measurableSet
  have hR₁c : R₁ᶜ = {b : Fˣ | ‖(b : F)‖ < ρ} ×ˢ (Set.univ : Set F) := by
    ext q; simp [hR₁, not_le]
  rw [← integral_add_compl hR₁m hint, ← integral_add_compl hR₁m hint0]

  set ψ : F → ℂ := fun x => Ψ (1 + E10 x) with hψdef
  have hψ0 : ∀ x : F, ‖x‖ ≤ δ → ψ x = 0 := fun x hx => hvan1 _ (entryLE_E10 hδ.le hx)
  set G : F → Fˣ × F → ℂ := fun s q =>
    (Metric.closedBall (0 : F) δ).indicator (fun a => ψ ((s - a ^ 2) / ((q.1 : Fˣ) : F))) q.2 with hG

  have hred : ∀ {s : F}, ‖s‖ ≤ ‖t‖ → ∀ q : Fˣ × F, q ∈ R₁ᶜ → chartFn Ψ s q = G s q := by
    intro s hs q hq
    obtain ⟨b, a⟩ := q
    have hb : ‖(b : F)‖ < ρ := by simpa [hR₁] using hq
    by_cases ha : ‖a‖ ≤ δ
    · rw [hG]; simp only
      rw [Set.indicator_of_mem (by simpa using ha), chartFn_apply, one_add_Y_eq]
      exact hinv _ _ (entryLE_AB ha (hb.le.trans hρδ))
    · rw [hG]; simp only
      rw [Set.indicator_of_notMem (by simpa using ha)]
      by_contra hne
      obtain ⟨-, -, hcB⟩ := bounds_of_chartFn_ne_zero hB hsupp hne
      apply ha
      have h1 : ‖s - a ^ 2‖ ≤ δ ^ 2 := by
        calc ‖s - a ^ 2‖ ≤ B * ‖(b : F)‖ := hcB
          _ ≤ B * ρ := mul_le_mul_of_nonneg_left hb.le hB0.le
          _ = ‖t‖ * B / δ := by rw [hρdef]; ring
          _ ≤ δ ^ 3 / δ := div_le_div_of_nonneg_right htB hδ.le
          _ = δ ^ 2 := by field_simp
      have h2 : ‖a‖ ^ 2 ≤ δ ^ 2 := by
        have : a ^ 2 = s - (s - a ^ 2) := by ring
        rw [← norm_pow, this]
        exact (norm_sub_le_max _ _).trans (max_le (hs.trans ht2) h1)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).1 h2

  have hiter : ∀ {s : F}, ‖s‖ ≤ ‖t‖ → Integrable (chartFn Ψ s) (ν.prod μ) →
      ∫ q in R₁ᶜ, chartFn Ψ s q ∂(ν.prod μ) =
        ∫ a, ∫ b in {b : Fˣ | ‖(b : F)‖ < ρ}, G s (b, a) ∂ν ∂μ := by
    intro s hs hints
    have hEq : Set.EqOn (chartFn Ψ s) (G s) R₁ᶜ := fun q hq => hred hs q hq
    rw [setIntegral_congr_fun hR₁m.compl hEq]
    have hGint : IntegrableOn (G s) R₁ᶜ (ν.prod μ) := (hints.integrableOn).congr_fun hEq hR₁m.compl
    rw [hR₁c] at hGint ⊢
    change ∫ q in {b : Fˣ | ‖(b : F)‖ < ρ} ×ˢ (Set.univ : Set F), G s q ∂(ν.prod μ) = _
    rw [← Measure.restrict_prod_eq_prod_univ]
    have hGint' : Integrable (G s) ((ν.restrict {b : Fˣ | ‖(b : F)‖ < ρ}).prod μ) := by
      rw [Measure.restrict_prod_eq_prod_univ]; exact hGint
    rw [integral_prod_symm (G s) hGint']
  rw [hiter le_rfl hint, hiter h0t hint0]
  congr 1
  ·
    refine setIntegral_congr_fun hR₁m (fun q hq => ?_)
    obtain ⟨b, a⟩ := q
    have hb : ρ ≤ ‖(b : F)‖ := hq
    rw [chartFn_apply, chartFn_apply]
    have hY : Y t a b = Y 0 a b + E10 ((t - 0) / b) := by rw [← Y_sub_Y]; abel
    rw [hY, ← add_assoc]
    refine hinv _ _ (entryLE_E10 hδ.le ?_)
    rw [sub_zero, norm_div]
    calc ‖t‖ / ‖(b : F)‖ ≤ ‖t‖ / ρ := div_le_div_of_nonneg_left (norm_nonneg _) hρ hb
      _ = δ := by rw [hρdef]; field_simp
  ·
    refine integral_congr_ae ?_
    have hbad : μ ({a : F | a = 0 ∨ t - a ^ 2 = 0}) = 0 := by
      refine Set.Finite.measure_zero ?_ μ
      by_cases hex : ∃ a₁ : F, t - a₁ ^ 2 = 0
      · obtain ⟨a₁, ha₁⟩ := hex
        refine (((Set.finite_singleton (-a₁)).insert a₁).insert 0).subset ?_
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases ha with h | h
        · exact Or.inl h
        · right
          have : a ^ 2 = a₁ ^ 2 := by rw [sub_eq_zero] at h ha₁; rw [← h, ← ha₁]
          exact sq_eq_sq_iff_eq_or_eq_neg.1 this
      · refine (Set.finite_singleton (0 : F)).subset ?_
        intro a ha
        simp only [Set.mem_singleton_iff]
        rcases ha with h | h
        · exact h
        · exact absurd ⟨a, h⟩ hex
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hbad] with a ha
    simp only [Set.mem_setOf_eq, not_or] at ha
    obtain ⟨ha0, hta⟩ := ha
    rw [hG]; simp only
    by_cases haδ : a ∈ Metric.closedBall (0 : F) δ
    · simp only [Set.indicator_of_mem haδ]
      exact inner_integral_eq ν ψ hδ hψ0 ht0 ha0 hta
    · simp only [Set.indicator_of_notMem haδ]

end ClaimA

section Main

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

def chi (δ : ℝ) : Matrix (Fin 2) (Fin 2) F → ℂ := {M | EntryLE (M - 1) δ}.indicator fun _ => 1

theorem chi_of_mem {δ : ℝ} {M : Matrix (Fin 2) (Fin 2) F} (h : EntryLE (M - 1) δ) : chi δ M = 1 :=
  Set.indicator_of_mem (by exact h) _

theorem chi_of_not_mem {δ : ℝ} {M : Matrix (Fin 2) (Fin 2) F} (h : ¬ EntryLE (M - 1) δ) : chi δ M = 0 :=
  Set.indicator_of_notMem (by exact h) _

theorem norm_chi_le (δ : ℝ) (M : Matrix (Fin 2) (Fin 2) F) : ‖chi δ M‖ ≤ 1 := by
  by_cases h : EntryLE (M - 1) δ
  · rw [chi_of_mem h, norm_one]
  · rw [chi_of_not_mem h, norm_zero]; exact zero_le_one

theorem chi_add {δ : ℝ} (M E : Matrix (Fin 2) (Fin 2) F) (hE : EntryLE E δ) : chi δ (M + E) = chi δ M := by
  by_cases h : EntryLE (M - 1) δ
  · rw [chi_of_mem h, chi_of_mem]
    have : M + E - 1 = (M - 1) + E := by abel
    rw [this]; exact h.add hE
  · rw [chi_of_not_mem h, chi_of_not_mem]
    intro h'
    apply h
    have : M - 1 = (M + E - 1) - E := by abel
    rw [this]; exact h'.sub hE

theorem chi_one_add {δ : ℝ} (E : Matrix (Fin 2) (Fin 2) F) (hE : EntryLE E δ) : chi δ (1 + E) = 1 :=
  chi_of_mem (by rwa [add_sub_cancel_left])

theorem entryLE_of_chi_ne_zero {δ : ℝ} (hδ1 : δ ≤ 1) {M : Matrix (Fin 2) (Fin 2) F} (h : chi δ M ≠ 0) :
    EntryLE M 1 := by
  by_cases hM : EntryLE (M - 1) δ
  · have h1 : EntryLE (1 : Matrix (Fin 2) (Fin 2) F) 1 := by
      intro i j; fin_cases i <;> fin_cases j <;> simp
    have := (hM.mono hδ1).add h1
    rwa [sub_add_cancel] at this
  · exact absurd (chi_of_not_mem hM) h

omit [IsUltrametricDist F] in
theorem entryLE_Y_iff (δ : ℝ) (t a : F) (b : F) :
    EntryLE (Y t a b) δ ↔ ‖a‖ ≤ δ ∧ ‖b‖ ≤ δ ∧ ‖(t - a ^ 2) / b‖ ≤ δ := by
  constructor
  · intro h; exact ⟨by simpa using h 0 0, by simpa using h 0 1, by simpa using h 1 0⟩
  · rintro ⟨ha, hb, hc⟩ i j
    fin_cases i <;> fin_cases j
    · simpa using ha
    · simpa using hb
    · simpa using hc
    · simpa using ha

theorem chartFn_chi (δ : ℝ) (t : F) : chartFn (chi δ) t = (Rset δ t).indicator fun _ => (1 : ℂ) := by
  funext q
  obtain ⟨b, a⟩ := q
  rw [chartFn_apply]
  have hiff : EntryLE (1 + Y t a b - 1) δ ↔ (b, a) ∈ Rset δ t := by
    rw [add_sub_cancel_left, entryLE_Y_iff, mem_Rset, norm_div, div_le_iff₀ (norm_pos_iff.2 b.ne_zero)]
  by_cases h : (b, a) ∈ Rset δ t
  · rw [Set.indicator_of_mem h, chi_of_mem (hiff.2 h)]
  · rw [Set.indicator_of_notMem h, chi_of_not_mem (fun h' => h (hiff.1 h'))]

theorem continuous_of_invariant {Φ : Matrix (Fin 2) (Fin 2) F → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hinv : ∀ M E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Φ (M + E) = Φ M) : Continuous Φ := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro M
  refine ⟨{N | ∀ i j, ‖(N - M) i j‖ < δ}, ?_, ?_, ?_⟩
  · have : {N : Matrix (Fin 2) (Fin 2) F | ∀ i j, ‖(N - M) i j‖ < δ} =
        ⋂ i : Fin 2, ⋂ j : Fin 2, {N | ‖(N - M) i j‖ < δ} := by
      ext N; simp
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact isOpen_lt (continuous_norm.comp ((continuous_id.sub continuous_const).matrix_elem i j)) continuous_const
  · intro i j; simp [hδ]
  · intro N hN
    have := hinv M (N - M) (fun i j => (hN i j).le)
    rwa [add_sub_cancel] at this

theorem isCompact_entryBox [ProperSpace F] (B : ℝ) : IsCompact {M : Matrix (Fin 2) (Fin 2) F | EntryLE M B} := by
  set S : Set (Fin 2 → Fin 2 → F) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => Metric.closedBall (0 : F) B with hS
  have hSc : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : F) B
  have hcont : Continuous (Matrix.of : (Fin 2 → Fin 2 → F) → Matrix (Fin 2) (Fin 2) F) :=
    continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)
  have heq : {M : Matrix (Fin 2) (Fin 2) F | EntryLE M B} = Matrix.of '' S := by
    rw [Equiv.image_eq_preimage_symm]
    ext M
    simp [hS, EntryLE, Set.mem_pi]
  rw [heq]
  exact hSc.image hcont

variable [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]

attribute [local instance] secondCountableTopology_units

theorem integral_chartFn_chi (δ : ℝ) (t : F) :
    ∫ q, chartFn (chi δ) t q ∂(ν.prod μ) = ((((ν.prod μ) (Rset δ t)).toReal : ℝ) : ℂ) := by
  rw [chartFn_chi, integral_indicator_const _ (measurableSet_Rset δ t), Complex.real_smul, mul_one, measureReal_def]

theorem integrable_chartFn_chi {δ : ℝ} {t : F} (h : (ν.prod μ) (Rset δ t) < ⊤) :
    Integrable (chartFn (chi δ) t) (ν.prod μ) := by
  rw [chartFn_chi, integrable_indicator_iff (measurableSet_Rset δ t)]
  exact integrableOn_const h.ne

theorem main (δ B : ℝ) (hδ : 0 < δ) (h4 : (4 : F) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : F, ‖t‖ < ε → ¬ IsSquare t →
      ∃ α : ℂ, α ≠ 0 ∧
        ∀ Φ : Matrix (Fin 2) (Fin 2) F → ℂ,
          (∀ M E : Matrix (Fin 2) (Fin 2) F, (∀ i j, ‖E i j‖ ≤ δ) → Φ (M + E) = Φ M) →
          (∀ M : Matrix (Fin 2) (Fin 2) F, Φ M ≠ 0 → ∀ i j, ‖M i j‖ ≤ B) →
          ∀ J : F → ℂ,
            (∀ s : F, J s = ∫ q : Fˣ × F, Φ (1 + !![q.2, ((q.1 : Fˣ) : F); (s - q.2 ^ 2) / ((q.1 : Fˣ) : F), -q.2])
              ∂(ν.prod μ)) →
            J t = J 0 + α * Φ 1 := by

  set δ' : ℝ := min δ 1 with hδ'def
  set B' : ℝ := max B 1 with hB'def
  have hδ' : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hB' : 1 ≤ B' := le_max_right _ _
  have hBB' : B ≤ B' := le_max_left _ _
  have hB'0 : 0 < B' := one_pos.trans_le hB'
  refine ⟨δ' ^ 3 / B', div_pos (pow_pos hδ' 3) hB'0, fun t ht hts => ?_⟩
  have ht0 : t ≠ 0 := fun h => hts ⟨0, by rw [h, mul_zero]⟩
  have htB : ‖t‖ * B' ≤ δ' ^ 3 := by rw [← le_div_iff₀ hB'0]; exact ht.le

  have hfin_t : (ν.prod μ) (Rset δ' t) < ⊤ := measure_Rset_lt_top_of_not_isSquare μ ν hts hδ'
  have hfin_0 : (ν.prod μ) (Rset δ' (0 : F)) < ⊤ := measure_Rset_zero_lt_top μ ν hδ'
  have hlt : ((ν.prod μ) (Rset δ' t)).toReal < ((ν.prod μ) (Rset δ' (0 : F))).toReal :=
    (ENNReal.toReal_lt_toReal hfin_t.ne hfin_0.ne).2 (measure_Rset_lt μ ν hδ' hts h4)
  refine ⟨((((ν.prod μ) (Rset δ' t)).toReal : ℝ) : ℂ) - ((((ν.prod μ) (Rset δ' (0 : F))).toReal : ℝ) : ℂ), ?_, ?_⟩
  · rw [sub_ne_zero]
    intro h
    exact hlt.ne (by exact_mod_cast h)
  intro Φ hΦδ hΦB J hJ

  have hinvΦ : ∀ M E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ' → Φ (M + E) = Φ M :=
    fun M E hE => hΦδ M E (fun i j => (hE i j).trans hδ'δ)
  have hsuppΦ : ∀ M, Φ M ≠ 0 → EntryLE M B' := fun M hM i j => (hΦB M hM i j).trans hBB'
  have hcontΦ : Continuous Φ := continuous_of_invariant hδ' hinvΦ
  have hcsΦ : HasCompactSupport Φ :=
    HasCompactSupport.intro (isCompact_entryBox B') fun M hM => by
      by_contra hne; exact hM (hsuppΦ M hne)
  obtain ⟨C, hCΦ⟩ := hcontΦ.bounded_above_of_compact_support hcsΦ

  set Ψ : Matrix (Fin 2) (Fin 2) F → ℂ := fun M => Φ M - Φ 1 * chi δ' M with hΨdef
  have hinvΨ : ∀ M E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ' → Ψ (M + E) = Ψ M := by
    intro M E hE; simp only [hΨdef, hinvΦ M E hE, chi_add M E hE]
  have hsuppχ : ∀ M : Matrix (Fin 2) (Fin 2) F, chi δ' M ≠ 0 → EntryLE M B' :=
    fun M h => (entryLE_of_chi_ne_zero hδ'1 h).mono hB'
  have hsuppΨ : ∀ M, Ψ M ≠ 0 → EntryLE M B' := by
    intro M hM
    by_cases h1 : Φ M ≠ 0
    · exact hsuppΦ M h1
    · rw [not_ne_iff] at h1
      have : chi δ' M ≠ 0 := by
        intro h2; apply hM; simp only [hΨdef, h1, h2, mul_zero, sub_zero]
      exact hsuppχ M this
  have hbddΨ : ∀ M, ‖Ψ M‖ ≤ C + ‖Φ 1‖ := by
    intro M
    calc ‖Ψ M‖ ≤ ‖Φ M‖ + ‖Φ 1 * chi δ' M‖ := norm_sub_le _ _
      _ ≤ C + ‖Φ 1‖ * 1 := add_le_add (hCΦ M)
          (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_chi_le δ' M) (norm_nonneg _))
      _ = C + ‖Φ 1‖ := by rw [mul_one]
  have hvan1 : ∀ E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ' → Ψ (1 + E) = 0 := by
    intro E hE
    simp only [hΨdef, hinvΦ 1 E hE, chi_one_add E hE, mul_one, sub_self]
  have hcontΨ : Continuous Ψ := continuous_of_invariant hδ' hinvΨ

  have hA := integral_chartFn_eq_zero_param (μ := μ) (ν := ν) hδ' hδ'1 hB' hinvΨ hsuppΨ hbddΨ hvan1 hcontΨ ht0 htB
  have h0t : ‖(0 : F)‖ ≤ ‖t‖ := by rw [norm_zero]; exact norm_nonneg _
  have hintΨt : Integrable (chartFn Ψ t) (ν.prod μ) :=
    integrable_chartFn hδ' hδ'1 hB' hinvΨ hsuppΨ hbddΨ hvan1 hcontΨ ht0 htB le_rfl
  have hintΨ0 : Integrable (chartFn Ψ 0) (ν.prod μ) :=
    integrable_chartFn hδ' hδ'1 hB' hinvΨ hsuppΨ hbddΨ hvan1 hcontΨ ht0 htB h0t
  have hintχt : Integrable (chartFn (chi δ') t) (ν.prod μ) := integrable_chartFn_chi μ ν hfin_t
  have hintχ0 : Integrable (chartFn (chi δ') 0) (ν.prod μ) := integrable_chartFn_chi μ ν hfin_0
  have hΨchart : ∀ s : F, chartFn Φ s = fun q => Φ 1 * chartFn (chi δ') s q + chartFn Ψ s q := by
    intro s; funext q; simp only [chartFn, hΨdef]; ring
  have hlin : ∀ {s : F}, Integrable (chartFn (chi δ') s) (ν.prod μ) → Integrable (chartFn Ψ s) (ν.prod μ) →
      ∫ q, chartFn Φ s q ∂(ν.prod μ) =
        Φ 1 * ∫ q, chartFn (chi δ') s q ∂(ν.prod μ) + ∫ q, chartFn Ψ s q ∂(ν.prod μ) := by
    intro s hχ hΨ
    rw [hΨchart s, integral_add (hχ.const_mul _) hΨ, integral_const_mul]
  have hJt : J t = ∫ q, chartFn Φ t q ∂(ν.prod μ) := hJ t
  have hJ0 : J 0 = ∫ q, chartFn Φ 0 q ∂(ν.prod μ) := hJ 0
  rw [hJt, hJ0, hlin hintχt hintΨt, hlin hintχ0 hintΨ0, hA, integral_chartFn_chi, integral_chartFn_chi]
  ring

end Main

end P2mGermChart
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare.P2mGermChart"

section KvInstances

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem charZero_adicCompletion' : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

end KvInstances
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare.P2mGermChart"

open MeasureTheory NumberField IsDedekindDomain in
open scoped Valued in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
    (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]
    (δ B : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion K, ‖t‖ < ε → ¬ IsSquare t →
      ∃ α : ℂ, α ≠ 0 ∧
        ∀ Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ,
          (∀ M E : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, ‖E i j‖ ≤ δ) → Φ (M + E) = Φ M) →
          (∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Φ M ≠ 0 → ∀ i j, ‖M i j‖ ≤ B) →
          ∀ J : v.adicCompletion K → ℂ,
            (∀ s : v.adicCompletion K, J s = ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
              Φ (1 + !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
                (s - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) ∂(ν.prod μ)) →
            J t = J 0 + α * Φ 1 := by
  haveI := charZero_adicCompletion' K v
  have h4 : (4 : v.adicCompletion K) ≠ 0 := by norm_num
  exact P2mGermChart.main μ ν δ B hδ h4

end
end S_AutomorphicForm_exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare (solution)
