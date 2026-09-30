-- Prove2me | Definitions.Def_CK_CKLaneC_S3_SlopeChain
-- name    : CK_CKLaneC_S3_SlopeChain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:55:12.264009+00:00
-- url     : https://prove2.me/theorems/a9bf4963-d123-4652-bbf1-b7d8a1419afe
-- title:
--   Courtade–Kumar proof module `CKLaneC.S3.SlopeChain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.S3.SlopeChain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.S3.SlopeChain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.S3.SlopeChain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/S3/SlopeChain.lean)

import Definitions.Def_CK_CKLaneC_S3_TaylorForm

-- ===== source module CKLaneC.S3.SlopeChain =====
section

/-!
# Lane C3 (snapshot copied into Lane C, namespace CKLaneC.S3) — slope-table chains and piece jets

A chunked table `T : List (List Piece)` of checked pieces.  `chainJet T refs lo hi`
returns one inverse-jet enclosure valid at every slope of `[lo, hi]`, built as the hull of
Taylor forms of the referenced pieces, provided the references cover `[lo, hi]`
contiguously.  A point `y` is the degenerate interval `[y, y]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC.S3.SlopeChain

open Set GeneralCK GeneralCK.Certificates DyadicInterval
open E8TAxisDeltaDirectionalJet CKLaneC.S3.SlopeTable CKLaneC.S3.TaylorForm

/-- Every piece of every chunk passes its executable check. -/
def TableValid (T : List (List Piece)) : Prop := ∀ c ∈ T, ∀ p ∈ c, p.check = true

def getPiece (T : List (List Piece)) (r : ℕ × ℕ) : Option Piece :=
  match T[r.1]? with
  | some c => c[r.2]?
  | none => none

theorem getPiece_valid {T : List (List Piece)} (hT : TableValid T) {r : ℕ × ℕ} {p : Piece}
    (h : getPiece T r = some p) : p.Valid := by
  unfold getPiece at h
  cases hc : T[r.1]? with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
    rw [hc] at h
    have hcm : c ∈ T := List.mem_of_getElem? hc
    have hpm : p ∈ c := List.mem_of_getElem? h
    exact Piece.check_sound (hT c hcm p hpm)

/-- Offset box `⊇ [S·ya - ystar.hi, S·yb - ystar.lo]` (all at scale `2^160`). -/
def deltaBox (p : Piece) (ya yb : ℚ) : DyadicInterval P :=
  ⟨⌊(scale P : ℚ) * ya⌋ - p.ystar.hi, ⌈(scale P : ℚ) * yb⌉ - p.ystar.lo⟩

def pieceJet (p : Piece) (ya yb : ℚ) : DyadicJet5Enclosure P :=
  tf p.cenJet p.whlJet (deltaBox p ya yb)

theorem pieceJet_sound {p : Piece} (hv : p.Valid) {ya yb : ℚ}
    (h0 : p.y0 ≤ ya) (h1 : yb ≤ p.y1) {y : ℝ} (hya : (ya : ℝ) ≤ y) (hyb : y ≤ yb) :
    (pieceJet p ya yb).Contains qJet y := by
  obtain ⟨ys, hys, hys0, hys1, hcen⟩ := hv.center
  have h0R : (p.y0 : ℝ) ≤ ya := by exact_mod_cast h0
  have h1R : (yb : ℝ) ≤ p.y1 := by exact_mod_cast h1
  have hs := scale_cast_pos P
  apply tf_sound (y0 := p.y0) (y1 := p.y1) (ys := ys)
  · intro z hz0 hz1
    exact qJet_soundAt (hv.range z hz0 hz1)
  · intro z hz0 hz1
    exact (hv.whole z hz0 hz1).2.2.2.2.2
  · exact hcen
  · exact ⟨hys0, hys1⟩
  · exact ⟨h0R.trans hya, hyb.trans h1R⟩
  · -- δ-box containment
    obtain ⟨hl, hu⟩ := hys
    have hfl : ((⌊(scale P : ℚ) * ya⌋ : ℤ) : ℝ) ≤ (scale P : ℝ) * ya := by
      have := Int.floor_le ((scale P : ℚ) * ya)
      exact_mod_cast this
    have hce : (scale P : ℝ) * yb ≤ ((⌈(scale P : ℚ) * yb⌉ : ℤ) : ℝ) := by
      have := Int.le_ceil ((scale P : ℚ) * yb)
      exact_mod_cast this
    constructor
    · simp only [deltaBox]
      push_cast
      nlinarith
    · simp only [deltaBox]
      push_cast
      nlinarith

/-- Componentwise interval hull. -/
def hullI (a b : DyadicInterval P) : DyadicInterval P := ⟨min a.lo b.lo, max a.hi b.hi⟩

theorem hullI_left {a b : DyadicInterval P} {x : ℝ} (h : a.Contains x) : (hullI a b).Contains x := by
  obtain ⟨hl, hu⟩ := h
  constructor
  · have : ((min a.lo b.lo : ℤ) : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast min_le_left _ _
    simp only [hullI]; linarith
  · have : (a.hi : ℝ) ≤ ((max a.hi b.hi : ℤ) : ℝ) := by exact_mod_cast le_max_left _ _
    simp only [hullI]; linarith

theorem hullI_right {a b : DyadicInterval P} {x : ℝ} (h : b.Contains x) : (hullI a b).Contains x := by
  obtain ⟨hl, hu⟩ := h
  constructor
  · have : ((min a.lo b.lo : ℤ) : ℝ) ≤ (b.lo : ℝ) := by exact_mod_cast min_le_right _ _
    simp only [hullI]; linarith
  · have : (b.hi : ℝ) ≤ ((max a.hi b.hi : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
    simp only [hullI]; linarith

def hullJ (a b : DyadicJet5Enclosure P) : DyadicJet5Enclosure P :=
  ⟨hullI a.d0 b.d0, hullI a.d1 b.d1, hullI a.d2 b.d2, hullI a.d3 b.d3, hullI a.d4 b.d4,
    hullI a.d5 b.d5⟩

theorem hullJ_left {a b : DyadicJet5Enclosure P} {j : Jet5} {y : ℝ} (h : a.Contains j y) :
    (hullJ a b).Contains j y :=
  ⟨hullI_left h.1, hullI_left h.2.1, hullI_left h.2.2.1, hullI_left h.2.2.2.1,
    hullI_left h.2.2.2.2.1, hullI_left h.2.2.2.2.2⟩

theorem hullJ_right {a b : DyadicJet5Enclosure P} {j : Jet5} {y : ℝ} (h : b.Contains j y) :
    (hullJ a b).Contains j y :=
  ⟨hullI_right h.1, hullI_right h.2.1, hullI_right h.2.2.1, hullI_right h.2.2.2.1,
    hullI_right h.2.2.2.2.1, hullI_right h.2.2.2.2.2⟩

/-- Jet enclosure on `[lo, hi]` from a contiguous chain of piece references. -/
def chainJet (T : List (List Piece)) : List (ℕ × ℕ) → ℚ → ℚ → Option (DyadicJet5Enclosure P)
  | [], _, _ => none
  | [r], lo, hi =>
    match getPiece T r with
    | some p => if p.y0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ p.y1 then some (pieceJet p lo hi) else none
    | none => none
  | r :: r' :: rs, lo, hi =>
    match getPiece T r with
    | some p =>
      if p.y0 ≤ lo ∧ lo ≤ p.y1 ∧ p.y1 < hi then
        match chainJet T (r' :: rs) p.y1 hi with
        | some J => some (hullJ (pieceJet p lo p.y1) J)
        | none => none
      else none
    | none => none

theorem chainJet_sound {T : List (List Piece)} (hT : TableValid T) :
    ∀ (refs : List (ℕ × ℕ)) (lo hi : ℚ) (J : DyadicJet5Enclosure P),
      chainJet T refs lo hi = some J →
      ∀ y : ℝ, (lo : ℝ) ≤ y → y ≤ hi → J.Contains qJet y ∧ y ∈ e8SlopeRange := by
  intro refs
  induction refs with
  | nil => intro lo hi J h; simp [chainJet] at h
  | cons r rs ih =>
    intro lo hi J h y hy0 hy1
    cases rs with
    | nil =>
      simp only [chainJet] at h
      cases hp : getPiece T r with
      | none => simp [hp] at h
      | some p =>
        simp only [hp] at h
        have hv := getPiece_valid hT hp
        split_ifs at h with hc
        · have hJ : J = pieceJet p lo hi := (Option.some.inj h).symm
          subst hJ
          refine ⟨pieceJet_sound hv hc.1 hc.2.2 hy0 hy1, ?_⟩
          have h0 : (p.y0 : ℝ) ≤ lo := by exact_mod_cast hc.1
          have h1 : (hi : ℝ) ≤ p.y1 := by exact_mod_cast hc.2.2
          exact hv.range y (h0.trans hy0) (hy1.trans h1)
    | cons r' rs' =>
      simp only [chainJet] at h
      cases hp : getPiece T r with
      | none => simp [hp] at h
      | some p =>
        simp only [hp] at h
        have hv := getPiece_valid hT hp
        split_ifs at h with hc
        · cases hrest : chainJet T (r' :: rs') p.y1 hi with
          | none => simp [hrest] at h
          | some J' =>
            simp only [hrest] at h
            have hJ : J = hullJ (pieceJet p lo p.y1) J' := (Option.some.inj h).symm
            subst hJ
            have h0 : (p.y0 : ℝ) ≤ lo := by exact_mod_cast hc.1
            by_cases hy : y ≤ (p.y1 : ℝ)
            · exact ⟨hullJ_left (pieceJet_sound hv hc.1 le_rfl hy0 hy),
                hv.range y (h0.trans hy0) hy⟩
            · have hy' : (p.y1 : ℝ) ≤ y := le_of_lt (lt_of_not_ge hy)
              obtain ⟨hJc, hr⟩ := ih p.y1 hi J' hrest y hy' hy1
              exact ⟨hullJ_right hJc, hr⟩

#print axioms pieceJet_sound
#print axioms chainJet_sound

end CKLaneC.S3.SlopeChain

end


