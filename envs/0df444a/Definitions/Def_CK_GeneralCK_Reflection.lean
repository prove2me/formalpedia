-- Prove2me | Definitions.Def_CK_GeneralCK_Reflection
-- name    : CK_GeneralCK_Reflection
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T02:51:09.376364+00:00
-- url     : https://prove2.me/theorems/aa6e1dc1-775f-440f-b541-7acb604615ae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Reflection` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Reflection` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Reflection` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Reflection (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Reflection.lean)

import Definitions.Def_CK_GeneralCK_CorrectionBasics
import Definitions.Def_CK_GeneralCK_SmallMeanAnalytic
import Definitions.Def_CK_GeneralCK_PerspectiveCurve
import Definitions.Def_CK_GeneralCK_ReflectionContactCurvature
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK.Reflection
open Set Filter
open scoped Topology












theorem meanEntropy_pos {a b : ℝ} (ha : -1 < a) (ha' : a < 1)
    (hb : -1 < b) (hb' : b < 1) : 0 < meanEntropy a b := by
  have := H_pos (p := (1-a)/2) (by linarith) (by linarith)
  have := H_pos (p := (1-b)/2) (by linarith) (by linarith)
  unfold meanEntropy E
  positivity

theorem hasDerivAt_E {a : ℝ} (ha : -1 < a) (ha' : a < 1) :
    HasDerivAt E (-SmallMean.A a/Real.log 2) a := by
  have h := ((Comparison.hasDerivAt_H (p := (1-a)/2) (by linarith) (by linarith)).comp a
    (((hasDerivAt_id a).const_sub 1).div_const 2))
  convert! h using 1
  rw [SmallMean.A_eq_J]
  field_simp

theorem hasDerivAt_meanEntropy {a : ℝ} (b : ℝ) (ha : -1 < a) (ha' : a < 1) :
    HasDerivAt (fun a => meanEntropy a b) (-SmallMean.A a/(2*Real.log 2)) a := by
  convert! ((hasDerivAt_E ha ha').add_const (E b)).div_const 2 using 1
  ring

theorem D_eq_atom_difference {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    D a b = Real.log 2 *
      (atomCorrection (1-(1-a)/2) ((1-b)/2)-atomCorrection ((1-a)/2) ((1-b)/2)) := by
  have habs₁ : |1-(1-a)/2-(1-b)/2| = (a+b)/2 := by
    rw [abs_of_nonneg (by linarith)]
    ring
  have habs₂ : |(1-a)/2-(1-b)/2| = (a-b)/2 := by
    rw [abs_of_nonpos (by linarith)]
    ring
  simp only [D, atomCorrection, interiorCost, J_complement, H_complement, habs₁, habs₂,
    meanEntropy, E, SmallMean.A_eq_J]
  ring

@[simp] theorem D_zero (a : ℝ) : D a 0 = 0 := by simp [D]

theorem D_diagonal {b : ℝ} (hb : 0 ≤ b) (hb' : b < 1) : D b b = 0 := by
  rcases hb.eq_or_lt with rfl | hb
  · simp
  have he : 0 < E b := H_pos (by linarith) (by linarith)
  have hc : radialContact b (E b) = (1-b)/2 :=
    radialContact_eq_of_equation hb he (by linarith) (by linarith) (by dsimp [E]; ring)
  simp only [D, meanEntropy, show (E b+E b)/2=E b by ring,
    show (b+b)/2=b by ring, sub_self, zero_div, F, hb.ne', ↓reduceIte, hc,
    SmallMean.A_eq_J]
  ring

theorem F_bias_entropy {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    F a (E a) = 2*a*SmallMean.A a/Real.log 2 := by
  have he : 0 < E a := H_pos (by linarith) (by linarith)
  have hc : radialContact a (E a) = (1-a)/2 :=
    radialContact_eq_of_equation ha he (by linarith) (by linarith) (by dsimp [E]; ring)
  simp only [F,ha.ne',↓reduceIte,hc,SmallMean.A_eq_J]
  field_simp

theorem perspectiveSlope_diagonal {b : ℝ} (hb : 0 < b) (hb' : b < 1) :
    Real.log 2*perspectiveSlope b (E b) (1/2) (-SmallMean.A b/(2*Real.log 2)) =
      SmallMean.A b+b/(1-b^2) := by
  have he : 0 < E b := H_pos (by linarith) (by linarith)
  have hc := hasDerivAt_F_curve (hasDerivAt_id b) (hasDerivAt_E (by linarith) hb') hb he
  have hd := (((hasDerivAt_id b).mul (SmallMean.hasDerivAt_A (by linarith) hb')).const_mul 2).div_const (Real.log 2)
  have heq : (fun a => F a (E a)) =ᶠ[𝓝 b] (fun a => 2*(a*SmallMean.A a)/Real.log 2) := by
    filter_upwards [Ioo_mem_nhds hb hb'] with a ha
    rw [F_bias_entropy ha.1 ha.2]
    ring
  have h := hc.unique (hd.congr_of_eventuallyEq heq)
  dsimp only [id_eq,perspectiveSlope] at h ⊢
  have hL := log_two_pos.ne'
  field_simp at h ⊢
  nlinarith [h]

/-- Explicit derivative of the reflection difference off its diagonal. -/
noncomputable def slope (a b : ℝ) : ℝ :=
  SmallMean.A b+b/(1-a^2)
    -Real.log 2*perspectiveSlope ((a+b)/2) (meanEntropy a b) (1/2) (-SmallMean.A a/(2*Real.log 2))
    +Real.log 2*perspectiveSlope ((a-b)/2) (meanEntropy a b) (1/2) (-SmallMean.A a/(2*Real.log 2))










@[simp] theorem curvature_zero (a : ℝ) : curvature a 0 = 0 := by simp [curvature]

theorem hasDerivAt_D {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (ha : a < 1) :
    HasDerivAt (fun a => D a b) (slope a b) a := by
  have he := hasDerivAt_meanEntropy b (by linarith) ha
  have he0 := meanEntropy_pos (by linarith) ha (by linarith) (hba.trans ha)
  have hp := hasDerivAt_F_curve (((hasDerivAt_id a).add_const b).div_const 2) he
    (by dsimp; linarith) he0
  have hm := hasDerivAt_F_curve (((hasDerivAt_id a).sub_const b).div_const 2) he
    (by dsimp; linarith) he0
  have hc := ((hasDerivAt_id a).mul_const (SmallMean.A b)).add
    ((SmallMean.hasDerivAt_A (by linarith) ha).const_mul b)
  convert! (hc.sub (hp.const_mul (Real.log 2))).add (hm.const_mul (Real.log 2)) using 1
  dsimp [slope]
  ring

theorem hasDerivAt_D_diagonal {b : ℝ} (hb : 0 ≤ b) (hb' : b < 1) :
    HasDerivAt (fun a => D a b) 0 b := by
  rcases hb.eq_or_lt with rfl | hb
  · simpa only [D_zero] using (hasDerivAt_const (0:ℝ) (0:ℝ))
  have he := hasDerivAt_meanEntropy b (by linarith) hb'
  have he0 := meanEntropy_pos (by linarith) hb' (by linarith) hb'
  have hp := hasDerivAt_F_curve (((hasDerivAt_id b).add_const b).div_const 2) he
    (by dsimp; linarith) he0
  have hm := hasDerivAt_F_curve_zero (((hasDerivAt_id b).sub_const b).div_const 2) he
    (by dsimp; ring) he0
  have hc := ((hasDerivAt_id b).mul_const (SmallMean.A b)).add
    ((SmallMean.hasDerivAt_A (by linarith) hb').const_mul b)
  have hd := (hc.sub (hp.const_mul (Real.log 2))).add (hm.const_mul (Real.log 2))
  have hcap := perspectiveSlope_diagonal hb hb'
  convert! hd using 1
  simp only [id_eq, one_mul, meanEntropy, show (E b+E b)/2=E b by ring,
    show (b+b)/2=b by ring, mul_zero, add_zero]
  rw [hcap]
  ring

theorem hasDerivAt_slope {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (ha : a < 1) :
    HasDerivAt (fun a => slope a b) (curvature a b) a := by
  have he := hasDerivAt_meanEntropy b (by linarith) ha
  have he0 := meanEntropy_pos (by linarith) ha (by linarith) (hba.trans ha)
  have hed : HasDerivAt (fun a => -SmallMean.A a/(2*Real.log 2))
      (-(1/(1-a^2))/(2*Real.log 2)) a :=
    ((SmallMean.hasDerivAt_A (by linarith) ha).neg).div_const _
  have hds : HasDerivAt (fun _ : ℝ => (1/2:ℝ)) 0 a := hasDerivAt_const _ _
  have hsp : HasDerivAt (fun a : ℝ => (a+b)/2) ((fun _ : ℝ => (1/2:ℝ)) a) a :=
    ((hasDerivAt_id a).add_const b).div_const 2
  have hsm : HasDerivAt (fun a : ℝ => (a-b)/2) ((fun _ : ℝ => (1/2:ℝ)) a) a :=
    ((hasDerivAt_id a).sub_const b).div_const 2
  have hp := (hasDerivAt_perspectiveSlope hsp he hds hed (by linarith) he0).const_mul (Real.log 2)
  have hm := (hasDerivAt_perspectiveSlope hsm he hds hed (by linarith) he0).const_mul (Real.log 2)
  rw [reflection_curvature_eq_contact (by linarith) he0] at hp hm
  have hc := (hasDerivAt_const a b).div (((hasDerivAt_id a).pow 2).const_sub 1)
    (by nlinarith : 1-a^2 ≠ 0)
  convert! ((hc.const_add (SmallMean.A b)).sub hp).add hm using 1
  dsimp [curvature]
  ring

theorem deriv2_D {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (ha : a < 1) :
    deriv (deriv (fun a => D a b)) a = curvature a b := by
  have heq : deriv (fun a => D a b) =ᶠ[𝓝 a] (fun a => slope a b) := by
    filter_upwards [Ioo_mem_nhds hba ha] with t ht
    exact (hasDerivAt_D hb ht.1 ht.2).deriv
  exact ((hasDerivAt_slope hb hba ha).congr_of_eventuallyEq heq).deriv

/-- The only sign input in the reflection reduction is the off-diagonal curvature. -/
theorem D_nonneg_of_curvature_nonneg {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha : a < 1)
    (hc : ∀ t ∈ Ioo b a, 0 ≤ curvature t b) : 0 ≤ D a b := by
  rcases hba.eq_or_lt with rfl | hba
  · rw [D_diagonal hb ha]
  have hcont : ContinuousOn (fun t => D t b) (Icc b a) := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hbt
    · exact (hasDerivAt_D_diagonal hb (hba.trans ha)).continuousAt.continuousWithinAt
    · exact (hasDerivAt_D hb hbt (ht.2.trans_lt ha)).continuousAt.continuousWithinAt
  have hconv : ConvexOn ℝ (Icc b a) (fun t => D t b) := by
    apply convexOn_of_deriv2_nonneg (convex_Icc b a) hcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hasDerivAt_D hb ht.1 (ht.2.trans ha)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have heq : deriv (fun t => D t b) =ᶠ[𝓝 t] (fun t => slope t b) := by
        filter_upwards [Ioo_mem_nhds ht.1 (ht.2.trans ha)] with u hu
        exact (hasDerivAt_D hb hu.1 hu.2).deriv
      exact ((hasDerivAt_slope hb ht.1 (ht.2.trans ha)).congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      change 0 ≤ deriv (deriv (fun t => D t b)) t
      rw [deriv2_D hb ht.1 (ht.2.trans ha)]
      exact hc t ht
  have hs := hconv.le_slope_of_hasDerivAt ⟨le_rfl,hba.le⟩ ⟨hba.le,le_rfl⟩ hba
    (hasDerivAt_D_diagonal hb (hba.trans ha))
  rw [slope_def_field,D_diagonal hb (hba.trans ha),sub_zero] at hs
  simpa only [zero_mul] using (le_div_iff₀ (sub_pos.mpr hba)).mp hs

/-- A proof of the ordered bias comparison covers every interior atom pair. -/
theorem atom_reflection_of_D_nonneg
    (hD : ∀ a b : ℝ, 0 ≤ b → b ≤ a → a < 1 → 0 ≤ D a b)
    {u v : ℝ} (hu : 0 < u) (hu' : u < 1) (hv : 0 < v) (hv' : v < 1) :
    entropyCorrection (H u) (H v) ≤ atomCorrection u v := by
  have hcross : ∀ x y : ℝ, 0 < x → x ≤ 1/2 → 0 < y → y ≤ 1/2 →
      atomCorrection x y ≤ atomCorrection (1-x) y := by
    intro x y hx hx' hy hy'
    have hord : ∀ x y : ℝ, 0 < x → x ≤ y → y ≤ 1/2 →
        atomCorrection x y ≤ atomCorrection (1-x) y := by
      intro x y hx hxy hy'
      have hd := hD (1-2*x) (1-2*y) (by linarith) (by linarith) (by linarith)
      rw [D_eq_atom_difference (by linarith) (by linarith)] at hd
      rw [show (1-(1-2*x))/2=x by ring, show (1-(1-2*y))/2=y by ring] at hd
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left log_two_pos).mp hd)
    rcases le_total x y with hxy | hyx
    · exact hord x y hx hxy hy'
    · have hh := hord y x hy hyx hx'
      rw [atomCorrection_comm y x] at hh
      have he : atomCorrection (1-y) x = atomCorrection (1-x) y := by
        rw [atomCorrection_comm, ← atomCorrection_complement x (1-y)]
        congr 1
        ring
      rwa [he] at hh
  rcases le_or_gt u (1/2) with hul | hul
  · rcases le_or_gt v (1/2) with hvl | hvl
    · rw [entropyCorrection_of_lower_half hu hul hv hvl]
    · rw [← H_complement v, entropyCorrection_of_lower_half hu hul (by linarith) (by linarith)]
      have hh := hcross (1-v) u (by linarith) (by linarith) hu hul
      rw [atomCorrection_comm (1-v) u, atomCorrection_comm (1-(1-v)) u,
        show 1-(1-v)=v by ring] at hh
      exact hh
  · rcases le_or_gt v (1/2) with hvl | hvl
    · rw [← H_complement u, entropyCorrection_of_lower_half (by linarith) (by linarith) hv hvl]
      simpa only [sub_sub_cancel] using hcross (1-u) v (by linarith) (by linarith) hv hvl
    · rw [← H_complement u, ← H_complement v,
        entropyCorrection_of_lower_half (by linarith) (by linarith) (by linarith) (by linarith),
        atomCorrection_complement]

theorem atom_reflection_of_curvature_nonneg
    (hc : ∀ a b : ℝ, 0 ≤ b → b < a → a < 1 → 0 ≤ curvature a b)
    {u v : ℝ} (hu : 0 < u) (hu' : u < 1) (hv : 0 < v) (hv' : v < 1) :
    entropyCorrection (H u) (H v) ≤ atomCorrection u v := by
  apply atom_reflection_of_D_nonneg (fun a b hb hba ha =>
    D_nonneg_of_curvature_nonneg hb hba ha (fun t ht => hc t b hb ht.1 (ht.2.trans ha))) hu hu' hv hv'

/-- Zero bias is an identity, so certificates are needed only for positive biases. -/
theorem atom_reflection_of_positive_curvature_nonneg
    (hc : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ curvature a b)
    {u v : ℝ} (hu : 0 < u) (hu' : u < 1) (hv : 0 < v) (hv' : v < 1) :
    entropyCorrection (H u) (H v) ≤ atomCorrection u v := by
  apply atom_reflection_of_curvature_nonneg (fun a b hb hba ha => ?_) hu hu' hv hv'
  rcases hb.eq_or_lt with rfl | hb
  · simp
  · exact hc a b hb hba ha

end GeneralCK.Reflection


