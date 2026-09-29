-- Prove2me | Definitions.Def_CK_CKLaneA1_BSStrip
-- name    : CK_CKLaneA1_BSStrip
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:14:49.316176+00:00
-- url     : https://prove2.me/theorems/6f25b052-95f2-411d-b222-5bf5fb2fdf91
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSStrip` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSStrip` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSStrip` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSStrip (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSStrip.lean)

import Definitions.Def_CK_CKLaneA1_BSCore

/-!
# CKLaneA1.BSStrip — cells, strips and the cover checker for the both-small chart

Cells are boxes in `(w, r)` with `r = u/w`: a `w`-strip `[w₁, w₂] ⊆ [0, 1/4]` carries a list of
`r`-cells covering `[0, 1]`.  All enclosures are computed from verified logarithms at the
dyadic corners and elementary monotone bounds; see `bsCell_sound`.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
open GeneralCK.Certificates
open GeneralCK.Certificates.Reflection (biasE biasB)

/-- A node on the `r` axis: `r = ra / 2^64`, with the exponent for `log(ra/2^64)`. -/
structure RNode where
  ra : ℤ
  e : ℕ
  deriving Repr

def rnodeOK (A : RNode) : Bool := decide (0 < A.ra ∧ A.ra ≤ SCz) && logOK A.ra SCz A.e
def rlog (n : ℕ) (L2 : DI) (A : RNode) : DI := logIv L2 A.ra SCz A.e n
noncomputable def RNode.r (A : RNode) : ℝ := (A.ra:ℝ) / (DyadicInterval.scale 64 : ℝ)

theorem rnode_facts {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {A : RNode}
    (h : rnodeOK A = true) : 0 < A.r ∧ A.r ≤ 1 ∧ (rlog n L2 A).Contains (Real.log A.r) := by
  have hs := SC_pos
  have h1 := Bool.and_eq_true_iff.mp h
  have hg : 0 < A.ra ∧ A.ra ≤ SCz := of_decide_eq_true h1.1
  refine ⟨div_pos (by exact_mod_cast hg.1) hs, ?_, ?_⟩
  · unfold RNode.r; rw [div_le_one hs]
    have : (A.ra:ℝ) ≤ (SCz:ℝ) := by exact_mod_cast hg.2
    simpa [SCz_real] using this
  · have := logIv_contains (n := n) hL h1.2
    unfold RNode.r; rw [← SCz_real]; exact this

structure BSCell where
  r : RNode
  two : Bool
  cd : CData
  deriving Repr

structure BSStrip where
  w1 : Node
  w2 : Node
  cells : List BSCell
  deriving Repr

noncomputable def BSStrip.lo (s : BSStrip) : ℝ := (s.w1.xa:ℝ) / (DyadicInterval.scale 64 : ℝ)
noncomputable def BSStrip.hi (s : BSStrip) : ℝ := (s.w2.xa:ℝ) / (DyadicInterval.scale 64 : ℝ)

/-! ## `w`-atoms of a strip -/

def bsStripOK (n : ℕ) (L2 : DI) (s : BSStrip) : Bool :=
  nodeOK s.w2 && decide (0 ≤ s.w1.xa ∧ s.w1.xa < s.w2.xa ∧ 4 * s.w2.xa ≤ SCz ∧
    0 < (nodeJ n L2 s.w2).lo ∧ 0 < (Iv.one.sub (Iv.pt s.w2.xa)).lo) &&
  (decide (s.w1.xa = 0) || (nodeOK s.w1 && decide (0 < (nodeJ n L2 s.w1).lo)))

def bsP (n : ℕ) (L2 : DI) (s : BSStrip) : DI :=
  if s.w1.xa = 0 then Iv.mk 0 (nodeJ n L2 s.w2).recip.hi
  else Iv.mk (nodeJ n L2 s.w1).recip.lo (nodeJ n L2 s.w2).recip.hi

def bsOm (n : ℕ) (L2 : DI) (s : BSStrip) : DI :=
  if s.w1.xa = 0 then Iv.mk 0 ((Iv.pt s.w2.xa).mul ((nodeJ n L2 s.w2).sub (nodeL n L2 s.w2))).hi
  else Iv.mk ((Iv.pt s.w1.xa).mul (nodeJ n L2 s.w2)).lo ((Iv.pt s.w2.xa).mul (nodeJ n L2 s.w1)).hi

def bsW (s : BSStrip) : DI := Iv.mk s.w1.xa s.w2.xa

def bsLw (s : BSStrip) : DI := Iv.mk SCz (Iv.one.sub (Iv.pt s.w2.xa)).recip.hi

theorem one_contains_SCz : (Iv.mk SCz SCz).Contains (1:ℝ) := by
  refine ⟨?_, ?_⟩ <;> simp [Iv.mk, SCz_real]

theorem bs_w_atoms {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {s : BSStrip}
    (h : bsStripOK n L2 s = true) {w : ℝ} (hw : 0 < w) (hw1 : s.lo ≤ w) (hw2 : w ≤ s.hi) :
    (bsP n L2 s).Contains (1 / jn w) ∧ (bsOm n L2 s).Contains (w * jn w) ∧
      (bsW s).Contains w ∧ (bsLw s).Contains ((-Real.log (1 - w)) / w) ∧ w ≤ 1/4 ∧
      0 < jn w ∧ 0 ≤ s.lo := by
  have hs := SC_pos
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have hg : 0 ≤ s.w1.xa ∧ s.w1.xa < s.w2.xa ∧ 4 * s.w2.xa ≤ SCz ∧ 0 < (nodeJ n L2 s.w2).lo ∧
      0 < (Iv.one.sub (Iv.pt s.w2.xa)).lo :=
    of_decide_eq_true h2.2
  obtain ⟨hx2, hx2h, hJ2, hL2, -, -⟩ := node_facts (n := n) hL h2.1
  have hquart : s.w2.x ≤ 1/4 := by
    unfold Node.x; rw [div_le_iff₀ hs]
    have : (4:ℝ) * s.w2.xa ≤ (SCz:ℝ) := by exact_mod_cast hg.2.2.1
    rw [SCz_real] at this; linarith
  have hwle : w ≤ s.w2.x := hw2
  have hw14 : w ≤ 1/4 := hwle.trans hquart
  have hJw2 : 0 < jn s.w2.x := jn_pos hx2 (by linarith)
  have hJwa : jn s.w2.x ≤ jn w := jn_anti hw hwle (by linarith)
  have hJw : 0 < jn w := jn_pos hw (by linarith)
  have hrec2 := DyadicInterval.recip_sound hg.2.2.2.1 hJ2
  have hlo0 : 0 ≤ s.lo := div_nonneg (by exact_mod_cast hg.1) hs.le
  have hWI : (bsW s).Contains w := by
    refine ⟨?_, ?_⟩
    · have : (s.w1.xa:ℝ) = (DyadicInterval.scale 64 : ℝ) * s.lo := by unfold BSStrip.lo; field_simp
      change (s.w1.xa:ℝ) ≤ _; rw [this]; exact mul_le_mul_of_nonneg_left hw1 hs.le
    · have : (s.w2.xa:ℝ) = (DyadicInterval.scale 64 : ℝ) * s.hi := by unfold BSStrip.hi; field_simp
      change _ ≤ (s.w2.xa:ℝ); rw [this]; exact mul_le_mul_of_nonneg_left hw2 hs.le
  have hLw : (bsLw s).Contains ((-Real.log (1 - w)) / w) := by
    have hb := neglog1m_bounds hw.le (by linarith)
    have hr := DyadicInterval.recip_sound hg.2.2.2.2
      (DyadicInterval.sub_sound Iv.one_contains (Iv.pt_contains s.w2.xa))
    refine ⟨?_, ?_⟩
    · change (SCz:ℝ) ≤ _
      rw [SCz_real]
      have : 1 ≤ (-Real.log (1 - w)) / w := by rw [le_div_iff₀ hw]; linarith [hb.1]
      first
        | exact le_mul_of_one_le_right hs.le this
        | nlinarith
    · have hle : (-Real.log (1 - w)) / w ≤ (1 - s.w2.x)⁻¹ := by
        rw [div_le_iff₀ hw]
        have h3 : w / (1 - w) ≤ w * (1 - s.w2.x)⁻¹ := by
          rw [div_eq_mul_inv]
          apply mul_le_mul_of_nonneg_left _ hw.le
          exact inv_anti₀ (by linarith) (by linarith)
        linarith [hb.2]
      have e : (s.w2.xa:ℝ) / (DyadicInterval.scale 64 : ℝ) = s.w2.x := rfl
      rw [e] at hr
      exact (mul_le_mul_of_nonneg_left hle hs.le).trans hr.2
  by_cases h0 : s.w1.xa = 0
  · have hP : (bsP n L2 s).Contains (1 / jn w) := by
      unfold bsP; rw [if_pos h0]
      refine ⟨?_, ?_⟩
      · change ((0:ℤ):ℝ) ≤ _; rw [Int.cast_zero]
        exact mul_nonneg hs.le (div_nonneg zero_le_one hJw.le)
      · have hle : 1 / jn w ≤ (jn s.w2.x)⁻¹ := by rw [one_div]; exact inv_anti₀ hJw2 hJwa
        exact (mul_le_mul_of_nonneg_left hle hs.le).trans hrec2.2
    have hO : (bsOm n L2 s).Contains (w * jn w) := by
      unfold bsOm; rw [if_pos h0]
      have hm := DyadicInterval.mul_sound (Iv.pt_contains s.w2.xa) (DyadicInterval.sub_sound hJ2 hL2)
      refine ⟨?_, ?_⟩
      · change ((0:ℤ):ℝ) ≤ _; rw [Int.cast_zero]; exact mul_nonneg hs.le (mul_nonneg hw.le hJw.le)
      · have hb := wjn_tail hw hwle hquart
        rw [neglog_eq hx2 (by linarith)] at hb
        exact (mul_le_mul_of_nonneg_left hb hs.le).trans hm.2
    exact ⟨hP, hO, hWI, hLw, hw14, hJw, hlo0⟩
  · have h3 := h1.2
    simp only [h0, decide_false, Bool.false_or] at h3
    have h4 := Bool.and_eq_true_iff.mp h3
    have hJ1pos : 0 < (nodeJ n L2 s.w1).lo := of_decide_eq_true h4.2
    obtain ⟨hx1, hx1h, hJ1, -, -, -⟩ := node_facts (n := n) hL h4.1
    have hgew : s.w1.x ≤ w := hw1
    have hJw1 : jn w ≤ jn s.w1.x := jn_anti hx1 hgew (by linarith)
    have hJw1p : 0 < jn s.w1.x := jn_pos hx1 (by linarith)
    have hrec1 := DyadicInterval.recip_sound hJ1pos hJ1
    have hP : (bsP n L2 s).Contains (1 / jn w) := by
      unfold bsP; rw [if_neg h0]
      refine ⟨?_, ?_⟩
      · have hle : (jn s.w1.x)⁻¹ ≤ 1 / jn w := by rw [one_div]; exact inv_anti₀ hJw hJw1
        exact hrec1.1.trans (mul_le_mul_of_nonneg_left hle hs.le)
      · have hle : 1 / jn w ≤ (jn s.w2.x)⁻¹ := by rw [one_div]; exact inv_anti₀ hJw2 hJwa
        exact (mul_le_mul_of_nonneg_left hle hs.le).trans hrec2.2
    have hO : (bsOm n L2 s).Contains (w * jn w) := by
      unfold bsOm; rw [if_neg h0]
      have hm1 := DyadicInterval.mul_sound (Iv.pt_contains s.w1.xa) hJ2
      have hm2 := DyadicInterval.mul_sound (Iv.pt_contains s.w2.xa) hJ1
      exact Iv.hull_contains hm1 hm2 (mul_le_mul hgew hJwa hJw2.le hw.le)
        (mul_le_mul hwle hJw1 hJw.le hx2.le)
    exact ⟨hP, hO, hWI, hLw, hw14, hJw, hlo0⟩

end CKLaneA1


