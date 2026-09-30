-- Prove2me | Definitions.Def_CK_CKLaneP_ThetaLip
-- name    : CK_CKLaneP_ThetaLip
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:54:47.317321+00:00
-- url     : https://prove2.me/theorems/73ec81ac-7541-475c-aaf1-e0a83cc3aa05
-- title:
--   Courtade–Kumar proof module `CKLaneP.ThetaLip` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.ThetaLip` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.ThetaLip` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.ThetaLip (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/ThetaLip.lean)

import Definitions.Def_CK_CKLaneP_SeamDip
import Definitions.Def_CK_CKLaneP_SeamQBase

-- ===== source module CKLaneP.ThetaLip =====
section
/-
Lane P — a uniform slope bound for Θ: `Θ(y) − Θ(x) ≤ Mglob·(y − x)` for `0 < x ≤ y ≤ Xglob`,
`Mglob = 11.545 > 8/log 2 = Θ'(0⁺)`, `Xglob = 16`.

Certificate: a partition `(0, x1] ∪ [x1, r1] ∪ … ∪ [·, 16]` with contact brackets on which the
interval bound `PsiUB ≥ Θ'` is `≤ Mglob` (checked by the kernel), glued by `ThetaLipOn.glue`.
`Mof xb nx2` is the slope constant used by the W/T cell checkers: `Mglob` when `xb ≤ Xglob`,
otherwise the single-interval bound `PsiUB (dy nx2) (dy dhN)`.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

/-- `Θ` is `M`-Lipschitz (from above) on `[l, r] ∩ (0, ∞)`. -/
def ThetaLipOn (M l r : ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → l ≤ x → x ≤ y → y ≤ r → e8Theta y - e8Theta x ≤ M * (y - x)

theorem ThetaLipOn.glue {M l m r : ℝ} (hm : 0 < m) (h1 : ThetaLipOn M l m)
    (h2 : ThetaLipOn M m r) : ThetaLipOn M l r := by
  intro x y hx hlx hxy hyr
  rcases le_total y m with hym | hym
  · exact h1 x y hx hlx hxy hym
  rcases le_total x m with hxm | hxm
  · have a := h1 x m hx hlx hxm le_rfl
    have b := h2 m y hm le_rfl hym hyr
    linarith
  · exact h2 x y hx hxm hxy hyr

/-- Segment list: `(r, na, nb)` certifies `[l, r]`: `na` a lower contact bracket at `r`,
`nb` an upper contact bracket at `l`, and `PsiUB (dy na) (dy nb) ≤ M`. -/
def lipList (M : ℚ) : ℚ → List (ℚ × ℕ × ℕ) → Bool
  | _, [] => true
  | l, (r, na, nb) :: rest =>
      decide (VD.okDy 60 na = true ∧ VD.okDy 60 nb = true ∧ 0 < l ∧ l ≤ r ∧
        2 * r * (dy na).Hhi ≤ 1 - 2 * (dy na).v ∧ 1 - 2 * (dy nb).v ≤ 2 * l * (dy nb).Hlo ∧
        0 < (dy nb).kapLo ∧ PsiUB (dy na) (dy nb) ≤ M) && lipList M r rest

/-- Right end of a segment list. -/
def lipEnd : ℚ → List (ℚ × ℕ × ℕ) → ℚ
  | l, [] => l
  | _, (r, _, _) :: rest => lipEnd r rest

theorem lipList_sound (M : ℚ) : ∀ (L : List (ℚ × ℕ × ℕ)) (l : ℚ), lipList M l L = true →
    ThetaLipOn (M : ℝ) (l : ℝ) ((lipEnd l L : ℚ) : ℝ) := by
  intro L
  induction L with
  | nil =>
      intro l _ x y _ hlx hxy hyr
      simp only [lipEnd] at hyr
      have hxy' : x = y := le_antisymm hxy (le_trans hyr hlx)
      rw [hxy', sub_self, sub_self, mul_zero]
  | cons hd rest ih =>
      obtain ⟨r, na, nb⟩ := hd
      intro l h
      simp only [lipList, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨okna, oknb, hl0, hlr, hA, hB, hk, hPsi⟩ := of_decide_eq_true h1
      have dna := dy_sound okna
      have dnb := dy_sound oknb
      have hseg : ThetaLipOn (M : ℝ) (l : ℝ) (r : ℝ) := by
        intro x y _ hlx hxy hyr
        have h := theta_sub_le dna dnb hk hl0 hA hB hlx hxy hyr
        have hPsiR : ((PsiUB (dy na) (dy nb) : ℚ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hPsi
        have := mul_le_mul_of_nonneg_right hPsiR (sub_nonneg.mpr hxy)
        linarith
      have hr0 : (0 : ℝ) < (r : ℝ) := by
        have : (0 : ℚ) < r := lt_of_lt_of_le hl0 hlr
        exact_mod_cast this
      have hrest := ih r h2
      simp only [lipEnd]
      exact ThetaLipOn.glue hr0 hseg hrest

/-- First segment `(0, x1]`: `na` a lower contact bracket at `x1`, compared with `v = 1/2`. -/
def lipFirst (M x1 : ℚ) (na : ℕ) : Bool :=
  decide (VD.okDy 60 na = true ∧ 0 < x1 ∧ 2 * x1 * (dy na).Hhi ≤ 1 - 2 * (dy na).v ∧
    0 < (dy dhN).kapLo ∧ PsiUB (dy na) (dy dhN) ≤ M)

theorem lipFirst_sound {M x1 : ℚ} {na : ℕ} (h : lipFirst M x1 na = true) :
    ThetaLipOn (M : ℝ) 0 (x1 : ℝ) := by
  obtain ⟨okna, _, hA, hk, hPsi⟩ := of_decide_eq_true h
  have dna := dy_sound okna
  intro x y hx _ hxy hyr
  have h := theta_slope_small dna (dy_sound dh_ok) hk dh_v hA hx hxy hyr
  have hPsiR : ((PsiUB (dy na) (dy dhN) : ℚ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hPsi
  have := mul_le_mul_of_nonneg_right hPsiR (sub_nonneg.mpr hxy)
  linarith

/-- The uniform slope constant and range. -/
def Mglob : ℚ := 11545 / 1000
def Xglob : ℚ := 16

def lipX1 : ℚ := 327 / 62500
def lipNa1 : ℕ := 570429143357925312
def lipSegs : List (ℚ × ℕ × ℕ) :=
  [((4421 / 500000 : ℚ), 566268919050850816, 570429143369988544),
   ((1313 / 100000 : ℚ), 561330416374095936, 566268919071234432),
   ((233 / 12500 : ℚ), 554991802085698752, 561330416404356544),
   ((2593 / 100000 : ℚ), 546623297274429056, 554991802128636608),
   ((3573 / 100000 : ℚ), 535417626917753728, 546623297334103936),
   ((4903 / 100000 : ℚ), 520320363143782656, 535417626999840000),
   ((6719 / 100000 : ℚ), 499982389722304192, 520320363256063488),
   ((9219 / 100000 : ℚ), 472671888265930816, 499982389875260864),
   ((127 / 1000 : ℚ), 436342829232726080, 472671888473508544),
   ((441 / 2500 : ℚ), 388901956395874368, 436342829512961984),
   ((2489 / 10000 : ℚ), 328933493049703616, 388901956770991936),
   ((1807 / 5000 : ℚ), 257317596096982880, 328933493544758080),
   ((5519 / 10000 : ℚ), 179488799177005792, 257317596611618080),
   ((9191 / 10000 : ℚ), 106279421250120624, 179488799535983392),
   ((1769 / 1000 : ℚ), 50138269621368640, 106279421462679472),
   ((173 / 40 : ℚ), 17253004973652616, 50138269721645184),
   ((389 / 25 : ℚ), 3799866684780181, 17253005008158624),
   ((16 : ℚ), 3678312419187613, 3799866692379915)]

theorem lipFirst_cert : lipFirst Mglob lipX1 lipNa1 = true := by decide +kernel

theorem lipList_cert : lipList Mglob lipX1 lipSegs = true := by decide +kernel

theorem lipEnd_cert : lipEnd lipX1 lipSegs = Xglob := by decide +kernel

theorem lipX1_pos : (0 : ℝ) < ((lipX1 : ℚ) : ℝ) := by unfold lipX1; norm_num

/-- The uniform slope bound. -/
theorem theta_lip_glob {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ ((Xglob : ℚ) : ℝ)) :
    e8Theta y - e8Theta x ≤ ((Mglob : ℚ) : ℝ) * (y - x) := by
  have h1 := lipFirst_sound lipFirst_cert
  have h2 := lipList_sound Mglob lipSegs lipX1 lipList_cert
  rw [lipEnd_cert] at h2
  exact ThetaLipOn.glue lipX1_pos h1 h2 x y hx hx.le hxy hy

/-- Slope constant used by the W/T checkers. -/
def Mof (xb : ℚ) (nx2 : ℕ) : ℚ := if xb ≤ Xglob then Mglob else PsiUB (dy nx2) (dy dhN)

theorem slope_Mof {xb : ℚ} {nx2 : ℕ} (hok : VD.okDy 60 nx2 = true) (hk : 0 < (dy dhN).kapLo)
    (hbr : 2 * xb * (dy nx2).Hhi ≤ 1 - 2 * (dy nx2).v) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ ((xb : ℚ) : ℝ)) :
    e8Theta y - e8Theta x ≤ ((Mof xb nx2 : ℚ) : ℝ) * (y - x) := by
  unfold Mof
  split_ifs with hX
  · have hXR : ((xb : ℚ) : ℝ) ≤ ((Xglob : ℚ) : ℝ) := by exact_mod_cast hX
    exact theta_lip_glob hx hxy (hy.trans hXR)
  · exact theta_slope_small (dy_sound hok) (dy_sound dh_ok) hk dh_v hbr hx hxy hy

theorem Mof_nonneg_of {xb : ℚ} {nx2 : ℕ} (h : 0 ≤ PsiUB (dy nx2) (dy dhN)) : 0 ≤ Mof xb nx2 := by
  unfold Mof
  split_ifs
  · unfold Mglob; norm_num
  · exact h

end CKLaneP

end


