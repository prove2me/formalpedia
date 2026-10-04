-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Cell
-- name    : CK_CKLaneC_SAxis_Cell
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:18:28.248253+00:00
-- url     : https://prove2.me/theorems/b8b57daf-5105-4239-89a0-0af110504be3
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Cell` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Cell` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Cell` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Cell (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Cell.lean)

import Definitions.Def_CK_CKLaneC_SAxis_RayS
import Definitions.Def_CK_CKLaneC_S3_SlopeChain
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularUnconditionalSource
import Definitions.Def_CK_GeneralCK_AgyE8SlopeRangeFull

-- ===== source module CKLaneC.SAxis.Cell =====
section

/-!
# Lane C (sAxis): corner-monotone cubic cell certificates for the regular second `s` derivative

A cell `[s0,s1] × [t0,t1]` (`0 ≤ s0`, `0 ≤ t0`) is certified by the order-three Taylor identity of
`e8RegularDeltaSS` along the segment from the LOWER-LEFT corner `(s0,t0)`, built from the regular
inverse jet `regularQJet` (sound at every slope `≥ 0`, in particular on the edge `s = 0`):

  `ΔSS(s,t) = m20 + m30 x + m21 y + (m40 x² + 2 m31 x y + m22 y²)/2
               + (r50 x³ + 3 r41 x² y + 3 r32 x y² + r23 y³)/6`,   `x = s - s0 ≥ 0`, `y = t - t0 ≥ 0`,

with corner coefficients `m = mixedS regularQJet s0 t0` and remainder coefficients `r` at an
intermediate point of the cell.  All inverse-jet enclosures come either from the unconditional
regular source polynomial (`regularJetBox`, slopes in `[0, 4/25]`) or from a checked slope table
(Lane C3 snapshot `CKLaneC.S3.SlopeChain.chainJet`).  The check is one executable Boolean
`CellW.check`; a rational split tree covers the sAxis strip.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace CKLaneC.SAxis.Cell

open Set GeneralCK GeneralCK.Certificates DyadicInterval
open E8TAxisDeltaDirectionalJet E8TAxisRegularGermJet E8CompactAnchorInterval
open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain

/-! ## Slope range and the regular jet -/

theorem slope_mem_of_pos {y : ℝ} (hy : 0 < y) : y ∈ e8SlopeRange := by
  rw [AgyE8SlopeRange.e8SlopeRange_eq_Ioi]; exact hy

theorem pos_of_slope_mem {y : ℝ} (hy : y ∈ e8SlopeRange) : 0 < y := by
  rw [AgyE8SlopeRange.e8SlopeRange_eq_Ioi] at hy; exact hy

theorem reg_soundAt {y : ℝ} (hy : 0 ≤ y) : regularQJet.SoundAt y := by
  rcases hy.eq_or_lt with h | h
  · rw [← h]; exact regularQJet_soundAt_zero
  · exact regularQJet_soundAt_of_mem (slope_mem_of_pos h)

theorem reg_agrees (z : ℝ) (hz : 0 < z) (hzm : z ∈ e8SlopeRange) :
    regularQJet.d0 z = e8RegularQ z ∧ regularQJet.d1 z = deriv e8RegularQ z ∧
      regularQJet.d2 z = deriv (deriv e8RegularQ) z := by
  obtain ⟨h0, h1, h2, -⟩ := regularQJet_eq_qJet_at_pos hz
  obtain ⟨a0, a1, a2⟩ := qJet_agrees hzm
  exact ⟨h0.trans a0, h1.trans a1, h2.trans a2⟩

theorem contains_reg_of_qJet {b : DyadicJet5Enclosure P} {y : ℝ} (hy : 0 < y)
    (h : b.Contains qJet y) : b.Contains regularQJet y := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := regularQJet_eq_qJet_at_pos hy
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]; exact c0
  · rw [h1]; exact c1
  · rw [h2]; exact c2
  · rw [h3]; exact c3
  · rw [h4]; exact c4
  · rw [h5]; exact c5

/-! ## Rational offset boxes and regular jet boxes -/

def offBox (lo hi : ℚ) : DyadicInterval P := ⟨⌊(scale P : ℚ) * lo⌋, ⌈(scale P : ℚ) * hi⌉⟩

theorem offBox_contains {lo hi : ℚ} {x : ℝ} (h0 : (lo : ℝ) ≤ x) (h1 : x ≤ hi) :
    (offBox lo hi).Contains x := by
  have hs := scale_cast_pos P
  have hfl : ((⌊(scale P : ℚ) * lo⌋ : ℤ) : ℝ) ≤ (scale P : ℝ) * lo := by
    have := Int.floor_le ((scale P : ℚ) * lo)
    exact_mod_cast this
  have hce : (scale P : ℝ) * hi ≤ ((⌈(scale P : ℚ) * hi⌉ : ℤ) : ℝ) := by
    have := Int.le_ceil ((scale P : ℚ) * hi)
    exact_mod_cast this
  constructor
  · simp only [offBox]; nlinarith
  · simp only [offBox]; nlinarith

/-- Regular inverse-jet enclosure on the rational slope interval `[lo, hi]`. -/
def regJet (lo hi : ℚ) : DyadicJet5Enclosure P :=
  E8TAxisRegularDyadicEvaluator.regularJetBox (offBox lo hi)

theorem regJet_contains {lo hi : ℚ} (h0 : 0 ≤ lo) (h1 : hi ≤ 4 / 25) {y : ℝ}
    (hy0 : (lo : ℝ) ≤ y) (hy1 : y ≤ hi) : (regJet lo hi).Contains regularQJet y := by
  have hl : (0 : ℝ) ≤ lo := by exact_mod_cast h0
  have hh : (hi : ℝ) ≤ 4 / 25 := by
    have := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at this
    linarith
  exact E8TAxisRegularUnconditionalSource.regularJetBox_contains (offBox_contains hy0 hy1)
    (by linarith) (by linarith)

/-! ## Jet sources -/

/-- Where an inverse-jet enclosure comes from: the regular source polynomial, or a chain of
checked slope-table pieces. -/
inductive Src where
  | reg : Src
  | chain : List (ℕ × ℕ) → Src

def srcJet (T : List (List Piece)) : Src → ℚ → ℚ → Option (DyadicJet5Enclosure P)
  | .reg, lo, hi => if 0 ≤ lo ∧ hi ≤ 4 / 25 then some (regJet lo hi) else none
  | .chain refs, lo, hi => chainJet T refs lo hi

theorem srcJet_sound {T : List (List Piece)} (hT : TableValid T) {src : Src} {lo hi : ℚ}
    {J : DyadicJet5Enclosure P} (h : srcJet T src lo hi = some J) {y : ℝ}
    (hy0 : (lo : ℝ) ≤ y) (hy1 : y ≤ hi) : J.Contains regularQJet y := by
  cases src with
  | reg =>
    simp only [srcJet] at h
    split_ifs at h with hc
    · have hJ : J = regJet lo hi := (Option.some.inj h).symm
      subst hJ
      exact regJet_contains hc.1 hc.2 hy0 hy1
  | chain refs =>
    simp only [srcJet] at h
    obtain ⟨hc, hm⟩ := chainJet_sound hT refs lo hi J h y hy0 hy1
    exact contains_reg_of_qJet (pos_of_slope_mem hm) hc

/-! ## Boxes of the four inverse arguments -/

def ContainsReg (b : Boxes P) (s t : ℝ) : Prop :=
  b.a.Contains regularQJet t ∧ b.b.Contains regularQJet (2 * s + t) ∧
    b.c.Contains regularQJet (s + t) ∧ b.d.Contains regularQJet s

theorem coeff_contains {b : Boxes P} {s t : ℝ} (h : ContainsReg b s t) (i j : ℕ) :
    (mixedSBox b.a b.b b.c b.d i j).Contains (mixedS regularQJet s t i j) :=
  mixedSBox_sound h.1 h.2.1 h.2.2.1 h.2.2.2 i j

/-! ## The replay interval -/

def half : DyadicInterval P := (ofInt P 2).recip
def sixth : DyadicInterval P := (ofInt P 6).recip

theorem half_contains : half.Contains (1 / 2 : ℝ) := by
  simpa only [half, one_div, Int.cast_ofNat] using recip_sound
    (show 0 < (ofInt P 2).lo by decide +kernel) (ofInt_sound P 2)

theorem sixth_contains : sixth.Contains (1 / 6 : ℝ) := by
  simpa only [sixth, one_div, Int.cast_ofNat] using recip_sound
    (show 0 < (ofInt P 6).lo by decide +kernel) (ofInt_sound P 6)

/-- Corner coefficients from `pc`, third-order coefficients from `bb`. -/
def replayS (pc bb : Boxes P) (offS offT : DyadicInterval P) : DyadicInterval P :=
  (((mixedSBox pc.a pc.b pc.c pc.d 2 0).add
      (((mixedSBox pc.a pc.b pc.c pc.d 3 0).mul offS).add
        ((mixedSBox pc.a pc.b pc.c pc.d 2 1).mul offT))).add
    (((((mixedSBox pc.a pc.b pc.c pc.d 4 0).mul (offS.mul offS)).add
        ((((ofInt P 2).mul (mixedSBox pc.a pc.b pc.c pc.d 3 1)).mul offS).mul offT)).add
        ((mixedSBox pc.a pc.b pc.c pc.d 2 2).mul (offT.mul offT))).mul half)).add
  ((((((mixedSBox bb.a bb.b bb.c bb.d 5 0).mul ((offS.mul offS).mul offS)).add
        ((((ofInt P 3).mul (mixedSBox bb.a bb.b bb.c bb.d 4 1)).mul (offS.mul offS)).mul offT)).add
        ((((ofInt P 3).mul (mixedSBox bb.a bb.b bb.c bb.d 3 2)).mul offS).mul
          (offT.mul offT))).add
        ((mixedSBox bb.a bb.b bb.c bb.d 2 3).mul ((offT.mul offT).mul offT))).mul sixth)

theorem replayS_contains {pc bb : Boxes P} {offS offT : DyadicInterval P} {x y : ℝ}
    {m r : ℕ → ℕ → ℝ}
    (hm : ∀ i j, (mixedSBox pc.a pc.b pc.c pc.d i j).Contains (m i j))
    (hr : ∀ i j, (mixedSBox bb.a bb.b bb.c bb.d i j).Contains (r i j))
    (hx : offS.Contains x) (hy : offT.Contains y) :
    (replayS pc bb offS offT).Contains
      (m 2 0 + (m 3 0 * x + m 2 1 * y) +
        (m 4 0 * x ^ 2 + 2 * m 3 1 * x * y + m 2 2 * y ^ 2) / 2 +
        (r 5 0 * x ^ 3 + 3 * r 4 1 * x ^ 2 * y + 3 * r 3 2 * x * y ^ 2 + r 2 3 * y ^ 3) / 6) := by
  have h := add_sound
    (add_sound (add_sound (hm 2 0) (add_sound (mul_sound (hm 3 0) hx) (mul_sound (hm 2 1) hy)))
      (mul_sound (add_sound (add_sound (mul_sound (hm 4 0) (mul_sound hx hx))
        (mul_sound (mul_sound (mul_sound (ofInt_sound P 2) (hm 3 1)) hx) hy))
        (mul_sound (hm 2 2) (mul_sound hy hy))) half_contains))
    (mul_sound (add_sound (add_sound (add_sound
        (mul_sound (hr 5 0) (mul_sound (mul_sound hx hx) hx))
        (mul_sound (mul_sound (mul_sound (ofInt_sound P 3) (hr 4 1)) (mul_sound hx hx)) hy))
        (mul_sound (mul_sound (mul_sound (ofInt_sound P 3) (hr 3 2)) hx) (mul_sound hy hy)))
        (mul_sound (hr 2 3) (mul_sound (mul_sound hy hy) hy))) sixth_contains)
  unfold replayS
  convert h using 1
  push_cast
  ring

/-- Order-one replay: corner value, first-order coefficients over the cell. -/
def replayS1 (pc bb : Boxes P) (offS offT : DyadicInterval P) : DyadicInterval P :=
  (mixedSBox pc.a pc.b pc.c pc.d 2 0).add
    (((mixedSBox bb.a bb.b bb.c bb.d 3 0).mul offS).add
      ((mixedSBox bb.a bb.b bb.c bb.d 2 1).mul offT))

/-- Order-two replay: corner value and gradient, second-order coefficients over the cell. -/
def replayS2 (pc bb : Boxes P) (offS offT : DyadicInterval P) : DyadicInterval P :=
  ((mixedSBox pc.a pc.b pc.c pc.d 2 0).add
      (((mixedSBox pc.a pc.b pc.c pc.d 3 0).mul offS).add
        ((mixedSBox pc.a pc.b pc.c pc.d 2 1).mul offT))).add
    (((((mixedSBox bb.a bb.b bb.c bb.d 4 0).mul (offS.mul offS)).add
        ((((ofInt P 2).mul (mixedSBox bb.a bb.b bb.c bb.d 3 1)).mul offS).mul offT)).add
        ((mixedSBox bb.a bb.b bb.c bb.d 2 2).mul (offT.mul offT))).mul half)

theorem replayS1_contains {pc bb : Boxes P} {offS offT : DyadicInterval P} {x y : ℝ}
    {m r : ℕ → ℕ → ℝ}
    (hm : ∀ i j, (mixedSBox pc.a pc.b pc.c pc.d i j).Contains (m i j))
    (hr : ∀ i j, (mixedSBox bb.a bb.b bb.c bb.d i j).Contains (r i j))
    (hx : offS.Contains x) (hy : offT.Contains y) :
    (replayS1 pc bb offS offT).Contains (m 2 0 + (r 3 0 * x + r 2 1 * y)) :=
  add_sound (hm 2 0) (add_sound (mul_sound (hr 3 0) hx) (mul_sound (hr 2 1) hy))

theorem replayS2_contains {pc bb : Boxes P} {offS offT : DyadicInterval P} {x y : ℝ}
    {m r : ℕ → ℕ → ℝ}
    (hm : ∀ i j, (mixedSBox pc.a pc.b pc.c pc.d i j).Contains (m i j))
    (hr : ∀ i j, (mixedSBox bb.a bb.b bb.c bb.d i j).Contains (r i j))
    (hx : offS.Contains x) (hy : offT.Contains y) :
    (replayS2 pc bb offS offT).Contains
      (m 2 0 + (m 3 0 * x + m 2 1 * y) +
        (r 4 0 * x ^ 2 + 2 * r 3 1 * x * y + r 2 2 * y ^ 2) / 2) := by
  have h := add_sound
    (add_sound (hm 2 0) (add_sound (mul_sound (hm 3 0) hx) (mul_sound (hm 2 1) hy)))
    (mul_sound (add_sound (add_sound (mul_sound (hr 4 0) (mul_sound hx hx))
        (mul_sound (mul_sound (mul_sound (ofInt_sound P 2) (hr 3 1)) hx) hy))
        (mul_sound (hr 2 2) (mul_sound hy hy))) half_contains)
  unfold replayS2
  convert h using 1
  push_cast
  ring

/-- Taylor order used by a cell. -/
inductive TOrd where
  | one : TOrd
  | two : TOrd
  | three : TOrd

def replayAny : TOrd → Boxes P → Boxes P → DyadicInterval P → DyadicInterval P →
    DyadicInterval P
  | .one => replayS1
  | .two => replayS2
  | .three => replayS

/-! ## The generic cell theorem -/

theorem cell_positive {pc bb : Boxes P} {offS offT : DyadicInterval P} {s0 t0 : ℝ}
    {InC : ℝ → ℝ → Prop} (ord : TOrd)
    (hs0 : 0 ≤ s0) (ht0 : 0 ≤ t0)
    (hpc : ContainsReg pc s0 t0)
    (hbb : ∀ s t, InC s t → ContainsReg bb s t)
    (hge : ∀ s t, InC s t → s0 ≤ s ∧ t0 ≤ t)
    (hoff : ∀ s t, InC s t → offS.Contains (s - s0) ∧ offT.Contains (t - t0))
    (hseg : ∀ s t v, InC s t → v ∈ Icc (0 : ℝ) 1 →
      InC (s0 + (s - s0) * v) (t0 + (t - t0) * v))
    (hpos : (replayAny ord pc bb offS offT).positiveCheck = true) :
    ∀ s t, InC s t → 0 < s → 0 < t → 0 < e8RegularDeltaSS s t := by
  intro s t hin hs ht
  obtain ⟨hsge, htge⟩ := hge s t hin
  have hx : 0 ≤ s - s0 := by linarith
  have hy : 0 ≤ t - t0 := by linarith
  have hsound : ∀ u ∈ Icc (0 : ℝ) 1,
      regularQJet.SoundAt (t0 + (t - t0) * u) ∧
      regularQJet.SoundAt ((2 * s0 + t0) + (2 * (s - s0) + (t - t0)) * u) ∧
      regularQJet.SoundAt ((s0 + t0) + ((s - s0) + (t - t0)) * u) ∧
      regularQJet.SoundAt (s0 + (s - s0) * u) := by
    intro u hu
    have hu0 := hu.1
    refine ⟨reg_soundAt ?_, reg_soundAt ?_, reg_soundAt ?_, reg_soundAt ?_⟩
    · exact add_nonneg ht0 (mul_nonneg hy hu0)
    · exact add_nonneg (by linarith) (mul_nonneg (by linarith) hu0)
    · exact add_nonneg (by linarith) (mul_nonneg (by linarith) hu0)
    · exact add_nonneg hs0 (mul_nonneg hx hu0)
  have e1 : s0 + (s - s0) * 1 = s := by ring
  have e2 : t0 + (t - t0) * 1 = t := by ring
  have hadm : E8Admissible (s0 + (s - s0) * 1) (t0 + (t - t0) * 1) := by
    rw [e1, e2]
    exact ⟨hs, ht, slope_mem_of_pos hs, slope_mem_of_pos ht, slope_mem_of_pos (by linarith),
      slope_mem_of_pos (by linarith)⟩
  have hd0 := deltaSSJetOf_d0_eq_regular (q := regularQJet) reg_agrees hadm
  rw [e1, e2] at hd0
  cases ord with
  | one =>
    obtain ⟨u, hu, heq⟩ := deltaSSOf_corner_taylor1 (q := regularQJet) hsound
    have hmid := hbb _ _ (hseg s t u hin ⟨hu.1.le, hu.2.le⟩)
    have hrep := replayS1_contains (m := fun i j => mixedS regularQJet s0 t0 i j)
      (r := fun i j => mixedS regularQJet (s0 + (s - s0) * u) (t0 + (t - t0) * u) i j)
      (coeff_contains hpc) (coeff_contains hmid) (hoff s t hin).1 (hoff s t hin).2
    beta_reduce at hrep
    have key : (replayS1 pc bb offS offT).Contains (e8RegularDeltaSS s t) := by
      rw [← hd0, heq]
      exact hrep
    exact positiveCheck_sound hpos key
  | two =>
    obtain ⟨u, hu, heq⟩ := deltaSSOf_corner_taylor2 (q := regularQJet) hsound
    have hmid := hbb _ _ (hseg s t u hin ⟨hu.1.le, hu.2.le⟩)
    have hrep := replayS2_contains (m := fun i j => mixedS regularQJet s0 t0 i j)
      (r := fun i j => mixedS regularQJet (s0 + (s - s0) * u) (t0 + (t - t0) * u) i j)
      (coeff_contains hpc) (coeff_contains hmid) (hoff s t hin).1 (hoff s t hin).2
    beta_reduce at hrep
    have key : (replayS2 pc bb offS offT).Contains (e8RegularDeltaSS s t) := by
      rw [← hd0, heq]
      exact hrep
    exact positiveCheck_sound hpos key
  | three =>
    obtain ⟨u, hu, heq⟩ := deltaSSOf_corner_taylor (q := regularQJet) hsound
    have hmid := hbb _ _ (hseg s t u hin ⟨hu.1.le, hu.2.le⟩)
    have hrep := replayS_contains (m := fun i j => mixedS regularQJet s0 t0 i j)
      (r := fun i j => mixedS regularQJet (s0 + (s - s0) * u) (t0 + (t - t0) * u) i j)
      (coeff_contains hpc) (coeff_contains hmid) (hoff s t hin).1 (hoff s t hin).2
    beta_reduce at hrep
    have key : (replayS pc bb offS offT).Contains (e8RegularDeltaSS s t) := by
      rw [← hd0, heq]
      exact hrep
    exact positiveCheck_sound hpos key

/-! ## Executable cell witnesses -/

structure CellW where
  s0 : ℚ
  s1 : ℚ
  t0 : ℚ
  t1 : ℚ
  pa : Src
  pb : Src
  pc : Src
  wa : Src
  wb : Src
  wc : Src
  ord : TOrd

def CellW.boxes (T : List (List Piece)) (w : CellW) : Option (Boxes P × Boxes P) :=
  match srcJet T w.pa w.t0 w.t0, srcJet T w.pb (2 * w.s0 + w.t0) (2 * w.s0 + w.t0),
      srcJet T w.pc (w.s0 + w.t0) (w.s0 + w.t0), srcJet T w.wa w.t0 w.t1,
      srcJet T w.wb (2 * w.s0 + w.t0) (2 * w.s1 + w.t1),
      srcJet T w.wc (w.s0 + w.t0) (w.s1 + w.t1) with
  | some a, some b, some c, some a', some b', some c' =>
    some (⟨a, b, c, regJet w.s0 w.s0⟩, ⟨a', b', c', regJet w.s0 w.s1⟩)
  | _, _, _, _, _, _ => none

def CellW.check (T : List (List Piece)) (w : CellW) : Bool :=
  decide (0 ≤ w.s0) && decide (w.s0 ≤ w.s1) && decide (w.s1 ≤ 4 / 25) && decide (0 ≤ w.t0) &&
  decide (w.t0 ≤ w.t1) &&
  (match w.boxes T with
   | some (pc, bb) =>
     (replayAny w.ord pc bb (offBox 0 (w.s1 - w.s0)) (offBox 0 (w.t1 - w.t0))).positiveCheck
   | none => false)

theorem CellW.check_sound {T : List (List Piece)} (hT : TableValid T) {w : CellW}
    (h : w.check T = true) :
    ∀ s t : ℝ, (w.s0 : ℝ) ≤ s → s ≤ w.s1 → (w.t0 : ℝ) ≤ t → t ≤ w.t1 → 0 < s → 0 < t →
      0 < e8RegularDeltaSS s t := by
  simp only [CellW.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hs0, hs01⟩, hs1⟩, ht0⟩, ht01⟩, hb⟩ := h
  have hs0R : (0 : ℝ) ≤ w.s0 := by exact_mod_cast hs0
  have hs01R : (w.s0 : ℝ) ≤ w.s1 := by exact_mod_cast hs01
  have hs1R : (w.s1 : ℝ) ≤ 4 / 25 := by
    have := (Rat.cast_le (K := ℝ)).mpr hs1
    push_cast at this
    linarith
  have ht0R : (0 : ℝ) ≤ w.t0 := by exact_mod_cast ht0
  have ht01R : (w.t0 : ℝ) ≤ w.t1 := by exact_mod_cast ht01
  have hs0' : w.s0 ≤ 4 / 25 := le_trans hs01 hs1
  cases hbx : w.boxes T with
  | none => rw [hbx] at hb; exact absurd hb (by simp)
  | some bx =>
    obtain ⟨pc, bb⟩ := bx
    rw [hbx] at hb
    simp only at hb
    unfold CellW.boxes at hbx
    split at hbx
    · rename_i a b c a' b' c' ha hb' hc ha' hb2 hc'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbx
      obtain ⟨rfl, rfl⟩ := hbx
      intro s t h1 h2 h3 h4 hs ht
      apply cell_positive (pc := ⟨a, b, c, regJet w.s0 w.s0⟩) (bb := ⟨a', b', c', regJet w.s0 w.s1⟩)
        (s0 := (w.s0 : ℝ)) (t0 := (w.t0 : ℝ))
        (InC := fun s t => (w.s0 : ℝ) ≤ s ∧ s ≤ w.s1 ∧ (w.t0 : ℝ) ≤ t ∧ t ≤ w.t1)
        w.ord hs0R ht0R
      · refine ⟨srcJet_sound hT ha (by push_cast; linarith) (by push_cast; linarith),
          srcJet_sound hT hb' (by push_cast; linarith) (by push_cast; linarith),
          srcJet_sound hT hc (by push_cast; linarith) (by push_cast; linarith),
          regJet_contains hs0 hs0' le_rfl le_rfl⟩
      · intro s t hin
        obtain ⟨k1, k2, k3, k4⟩ := hin
        exact ⟨srcJet_sound hT ha' (by push_cast; linarith) (by push_cast; linarith),
          srcJet_sound hT hb2 (by push_cast; linarith) (by push_cast; linarith),
          srcJet_sound hT hc' (by push_cast; linarith) (by push_cast; linarith),
          regJet_contains hs0 hs1 k1 k2⟩
      · intro s t hin
        exact ⟨hin.1, hin.2.2.1⟩
      · intro s t hin
        obtain ⟨k1, k2, k3, k4⟩ := hin
        exact ⟨offBox_contains (lo := 0) (hi := w.s1 - w.s0) (by push_cast; linarith)
            (by push_cast; linarith),
          offBox_contains (lo := 0) (hi := w.t1 - w.t0) (by push_cast; linarith)
            (by push_cast; linarith)⟩
      · intro s t v hin hv
        obtain ⟨k1, k2, k3, k4⟩ := hin
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hv.1, hv.2]
      · exact hb
      · exact ⟨h1, h2, h3, h4⟩
      · exact hs
      · exact ht
    · exact absurd hbx (by simp)

/-! ## Rational split trees covering the strip -/

inductive Tree where
  | cell : ℕ → Tree
  | origin : Tree
  | splitS : ℚ → Tree → Tree → Tree
  | splitT : ℚ → Tree → Tree → Tree

/-- Geometric check of a split tree on the node rectangle `[s0,s1] × [t0,t1]`: every leaf is
either contained in a listed cell, or lies in the origin owner's region `s + t ≤ 2/25`. -/
def Tree.check (cells : List CellW) : Tree → ℚ → ℚ → ℚ → ℚ → Bool
  | .cell i, s0, s1, t0, t1 =>
    match cells[i]? with
    | some w => decide (w.s0 ≤ s0) && decide (s1 ≤ w.s1) && decide (w.t0 ≤ t0) &&
        decide (t1 ≤ w.t1)
    | none => false
  | .origin, _, s1, _, t1 => decide (s1 + t1 ≤ 2 / 25)
  | .splitS m l r, s0, s1, t0, t1 =>
    decide (s0 ≤ m) && decide (m ≤ s1) && l.check cells s0 m t0 t1 && r.check cells m s1 t0 t1
  | .splitT m l r, s0, s1, t0, t1 =>
    decide (t0 ≤ m) && decide (m ≤ t1) && l.check cells s0 s1 t0 m && r.check cells s0 s1 m t1

theorem Tree.check_sound {T : List (List Piece)} (hT : TableValid T) {cells : List CellW}
    (hc : ∀ w ∈ cells, w.check T = true) :
    ∀ (tr : Tree) (s0 s1 t0 t1 : ℚ), tr.check cells s0 s1 t0 t1 = true →
      ∀ s t : ℝ, (s0 : ℝ) ≤ s → s ≤ s1 → (t0 : ℝ) ≤ t → t ≤ t1 → 0 < s → 0 < t →
        2 / 25 < s + t → 0 < e8RegularDeltaSS s t := by
  intro tr
  induction tr with
  | cell i =>
    intro s0 s1 t0 t1 h s t h1 h2 h3 h4 hs ht _
    simp only [Tree.check] at h
    cases hw : cells[i]? with
    | none => rw [hw] at h; exact absurd h (by simp)
    | some w =>
      rw [hw] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := h
      have hwm : w ∈ cells := List.mem_of_getElem? hw
      have k1R : (w.s0 : ℝ) ≤ s0 := by exact_mod_cast k1
      have k2R : (s1 : ℝ) ≤ w.s1 := by exact_mod_cast k2
      have k3R : (w.t0 : ℝ) ≤ t0 := by exact_mod_cast k3
      have k4R : (t1 : ℝ) ≤ w.t1 := by exact_mod_cast k4
      exact CellW.check_sound hT (hc w hwm) s t (by linarith) (by linarith) (by linarith)
        (by linarith) hs ht
  | origin =>
    intro s0 s1 t0 t1 h s t h1 h2 h3 h4 hs ht hst
    simp only [Tree.check, decide_eq_true_eq] at h
    have hR : (s1 : ℝ) + t1 ≤ 2 / 25 := by
      have := (Rat.cast_le (K := ℝ)).mpr h
      push_cast at this
      linarith
    linarith
  | splitS m l r ihl ihr =>
    intro s0 s1 t0 t1 h s t h1 h2 h3 h4 hs ht hst
    simp only [Tree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨k1, k2⟩, hl⟩, hr⟩ := h
    by_cases hsm : s ≤ (m : ℝ)
    · exact ihl s0 m t0 t1 hl s t h1 hsm h3 h4 hs ht hst
    · exact ihr m s1 t0 t1 hr s t (le_of_lt (lt_of_not_ge hsm)) h2 h3 h4 hs ht hst
  | splitT m l r ihl ihr =>
    intro s0 s1 t0 t1 h s t h1 h2 h3 h4 hs ht hst
    simp only [Tree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨k1, k2⟩, hl⟩, hr⟩ := h
    by_cases htm : t ≤ (m : ℝ)
    · exact ihl s0 s1 t0 m hl s t h1 h2 h3 htm hs ht hst
    · exact ihr s0 s1 m t1 hr s t h1 h2 (le_of_lt (lt_of_not_ge htm)) h4 hs ht hst

end CKLaneC.SAxis.Cell

end


