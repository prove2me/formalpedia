-- Prove2me | Definitions.Def_CK_CKLaneA1_FEStrip
-- name    : CK_CKLaneA1_FEStrip
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:20:58.790731+00:00
-- url     : https://prove2.me/theorems/2791b1a4-8ab5-4d73-ba84-ae505d90618f
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEStrip` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEStrip` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEStrip` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEStrip (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEStrip.lean)

import Definitions.Def_CK_CKLaneA1_FECore
import Definitions.Def_CK_CKLaneA1_JnConvex

/-!
# CKLaneA1.FEStrip — strips, cells and the fixedEdge cover checker

A cover of `u ∈ [0, 1/50]`, `w ∈ [1/40, 1/2]` is a list of `u`-strips; each strip carries a
list of `w`-cells.  Corner logarithms are computed (and verified) inside the checker.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
open GeneralCK.Certificates

/-- A breakpoint `x = xa / 2^64` with log exponents for `log(x/(1-x))` and `log(1-x)`. -/
structure Node where
  xa : ℤ
  eJ : ℕ
  eL : ℕ
  deriving Repr

def nodeOK (nd : Node) : Bool :=
  decide (0 < nd.xa ∧ 2 * nd.xa ≤ SCz) && logOK nd.xa (SCz - nd.xa) nd.eJ &&
    logOK (SCz - nd.xa) SCz nd.eL

def nodeJ (n : ℕ) (L2 : DI) (nd : Node) : DI := (logIv L2 nd.xa (SCz - nd.xa) nd.eJ n).neg
def nodeL (n : ℕ) (L2 : DI) (nd : Node) : DI := logIv L2 (SCz - nd.xa) SCz nd.eL n
def nodeQ (nd : Node) : DI := (Iv.pt nd.xa).mul (Iv.one.sub (Iv.pt nd.xa))
def nodeH (n : ℕ) (L2 : DI) (nd : Node) : DI :=
  ((Iv.pt nd.xa).mul (nodeJ n L2 nd)).sub (nodeL n L2 nd)

/-- The real point of a node. -/
noncomputable def Node.x (nd : Node) : ℝ := (nd.xa:ℝ) / (DyadicInterval.scale 64 : ℝ)

theorem node_facts {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {nd : Node}
    (h : nodeOK nd = true) :
    0 < nd.x ∧ nd.x ≤ 1/2 ∧ (nodeJ n L2 nd).Contains (jn nd.x) ∧
      (nodeL n L2 nd).Contains (Real.log (1 - nd.x)) ∧ (nodeQ nd).Contains (qp nd.x) ∧
      (nodeH n L2 nd).Contains (Certificates.Mixed.hn nd.x) := by
  have hs := SC_pos
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have hg : 0 < nd.xa ∧ 2 * nd.xa ≤ SCz := of_decide_eq_true h2.1
  have hx0 : 0 < nd.x := div_pos (by exact_mod_cast hg.1) hs
  have hxh : nd.x ≤ 1/2 := by
    unfold Node.x
    rw [div_le_iff₀ hs]
    have : (2:ℝ) * nd.xa ≤ (SCz:ℝ) := by exact_mod_cast hg.2
    rw [SCz_real] at this
    linarith
  have hx1 : nd.x < 1 := by linarith
  have hJ0 := logIv_contains (n := n) hL h2.2
  have hL0 := logIv_contains (n := n) hL h1.2
  have hjn : (nodeJ n L2 nd).Contains (jn nd.x) := by
    have e1 : jn nd.x = -Real.log ((nd.xa:ℝ) / ((SCz - nd.xa : ℤ):ℝ)) := by
      unfold jn Node.x
      rw [← Real.log_inv, inv_div]
      congr 1
      rw [show (SCz - nd.xa : ℤ) = DyadicInterval.scale 64 - nd.xa from rfl]
      push_cast
      field_simp
    rw [e1]
    exact DyadicInterval.neg_sound hJ0
  have hlog : (nodeL n L2 nd).Contains (Real.log (1 - nd.x)) := by
    have e1 : 1 - nd.x = ((SCz - nd.xa : ℤ):ℝ) / ((SCz:ℤ):ℝ) := by
      unfold Node.x
      rw [show (SCz - nd.xa : ℤ) = DyadicInterval.scale 64 - nd.xa from rfl, SCz_real]
      push_cast
      field_simp
    rw [e1]; exact hL0
  have hq : (nodeQ nd).Contains (qp nd.x) := by
    unfold nodeQ qp
    exact DyadicInterval.mul_sound (Iv.pt_contains nd.xa)
      (DyadicInterval.sub_sound Iv.one_contains (Iv.pt_contains nd.xa))
  have hh : (nodeH n L2 nd).Contains (Certificates.Mixed.hn nd.x) := by
    rw [hn_eq_mul_jn hx0 hx1]
    exact DyadicInterval.sub_sound (DyadicInterval.mul_sound (Iv.pt_contains nd.xa) hjn) hlog
  exact ⟨hx0, hxh, hjn, hlog, hq, hh⟩

/-! ## Strip atoms -/

structure FECell where
  w : Node
  cd : CData
  deriving Repr

structure FEStrip where
  u1 : Node      -- `u1.xa = 0` marks the tail strip `[0, u2]`
  u2 : Node
  w0 : Node
  cells : List FECell
  deriving Repr

def stripT (n : ℕ) (L2 : DI) (s : FEStrip) : DI :=
  if s.u1.xa = 0 then Iv.mk 0 (nodeJ n L2 s.u2).recip.hi
  else Iv.mk (nodeJ n L2 s.u1).recip.lo (nodeJ n L2 s.u2).recip.hi

def stripQ (s : FEStrip) : DI := Iv.mk (nodeQ s.u1).lo (nodeQ s.u2).hi

def stripK (n : ℕ) (L2 : DI) (s : FEStrip) : DI :=
  if s.u1.xa = 0 then Iv.mk 0 ((Iv.pt s.u2.xa).mul ((nodeJ n L2 s.u2).sub (nodeL n L2 s.u2))).hi
  else Iv.mk ((nodeQ s.u1).mul (nodeJ n L2 s.u2)).lo ((nodeQ s.u2).mul (nodeJ n L2 s.u1)).hi

def stripH (n : ℕ) (L2 : DI) (s : FEStrip) : DI :=
  if s.u1.xa = 0 then Iv.mk 0 (nodeH n L2 s.u2).hi
  else Iv.mk (nodeH n L2 s.u1).lo (nodeH n L2 s.u2).hi

def stripU (s : FEStrip) : DI := Iv.mk s.u1.xa s.u2.xa

def stripOKu (n : ℕ) (L2 : DI) (s : FEStrip) : Bool :=
  nodeOK s.u2 && decide (0 ≤ s.u1.xa ∧ s.u1.xa < s.u2.xa ∧ 4 * s.u2.xa ≤ SCz ∧
    0 < (nodeJ n L2 s.u2).lo) &&
  (decide (s.u1.xa = 0) || (nodeOK s.u1 && decide (0 < (nodeJ n L2 s.u1).lo)))

/-- The real `u`-range of a strip. -/
noncomputable def FEStrip.lo (s : FEStrip) : ℝ := (s.u1.xa:ℝ) / (DyadicInterval.scale 64 : ℝ)
noncomputable def FEStrip.hi (s : FEStrip) : ℝ := (s.u2.xa:ℝ) / (DyadicInterval.scale 64 : ℝ)

theorem strip_atoms {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {s : FEStrip}
    (h : stripOKu n L2 s = true) {u : ℝ} (hu : 0 < u) (hu1 : s.lo ≤ u) (hu2 : u ≤ s.hi) :
    (stripT n L2 s).Contains (1 / jn u) ∧ (stripQ s).Contains (qp u) ∧
      (stripK n L2 s).Contains (qp u * jn u) ∧ (stripH n L2 s).Contains (Certificates.Mixed.hn u) ∧
      (stripU s).Contains u ∧ u ≤ 1/4 := by
  have hs := SC_pos
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have hg : 0 ≤ s.u1.xa ∧ s.u1.xa < s.u2.xa ∧ 4 * s.u2.xa ≤ SCz ∧ 0 < (nodeJ n L2 s.u2).lo :=
    of_decide_eq_true h2.2
  obtain ⟨hx2, hx2h, hJ2, hL2, hQ2, hH2⟩ := node_facts (n := n) hL h2.1
  have hu2x : s.hi = s.u2.x := rfl
  have hquart : s.u2.x ≤ 1/4 := by
    unfold Node.x
    rw [div_le_iff₀ hs]
    have : (4:ℝ) * s.u2.xa ≤ (SCz:ℝ) := by exact_mod_cast hg.2.2.1
    rw [SCz_real] at this
    linarith
  have hule : u ≤ s.u2.x := hu2x ▸ hu2
  have hu14 : u ≤ 1/4 := hule.trans hquart
  have hJu2pos : 0 < jn s.u2.x := jn_pos hx2 (by linarith)
  have hJu : jn s.u2.x ≤ jn u := jn_anti hu hule (by linarith)
  have hJupos : 0 < jn u := jn_pos hu (by linarith)
  have hrec2 := DyadicInterval.recip_sound hg.2.2.2 hJ2
  have hUI : (stripU s).Contains u := by
    refine ⟨?_, ?_⟩
    · have : (s.u1.xa:ℝ) = (DyadicInterval.scale 64 : ℝ) * s.lo := by unfold FEStrip.lo; field_simp
      change (s.u1.xa:ℝ) ≤ _; rw [this]; exact mul_le_mul_of_nonneg_left hu1 hs.le
    · have : (s.u2.xa:ℝ) = (DyadicInterval.scale 64 : ℝ) * s.hi := by unfold FEStrip.hi; field_simp
      change _ ≤ (s.u2.xa:ℝ); rw [this]; exact mul_le_mul_of_nonneg_left hu2 hs.le
  by_cases h0 : s.u1.xa = 0
  · -- tail strip
    have hT : (stripT n L2 s).Contains (1 / jn u) := by
      unfold stripT; rw [if_pos h0]
      refine ⟨?_, ?_⟩
      · change ((0:ℤ):ℝ) ≤ _; push_cast; positivity
      · have := hrec2.2
        have hle : 1 / jn u ≤ (jn s.u2.x)⁻¹ := by
          rw [one_div]; exact inv_anti₀ hJu2pos hJu
        exact (mul_le_mul_of_nonneg_left hle hs.le).trans this
    have hQ1 : (nodeQ s.u1).Contains (qp 0) := by
      have := DyadicInterval.mul_sound (Iv.pt_contains s.u1.xa)
        (DyadicInterval.sub_sound Iv.one_contains (Iv.pt_contains s.u1.xa))
      have e : (s.u1.xa:ℝ) / (DyadicInterval.scale 64 : ℝ) = 0 := by rw [h0]; simp
      rw [e] at this
      simpa [qp, nodeQ] using this
    have hQ : (stripQ s).Contains (qp u) :=
      Iv.hull_contains hQ1 hQ2 (qp_mono (le_refl 0) hu.le (by linarith)) (qp_mono hu.le hule hx2h)
    have hK : (stripK n L2 s).Contains (qp u * jn u) := by
      unfold stripK; rw [if_pos h0]
      have hm := DyadicInterval.mul_sound (Iv.pt_contains s.u2.xa) (DyadicInterval.sub_sound hJ2 hL2)
      refine ⟨?_, ?_⟩
      · change ((0:ℤ):ℝ) ≤ _; push_cast
        exact mul_nonneg hs.le (mul_nonneg (by unfold qp; nlinarith) hJupos.le)
      · have hb := ku_tail hu hule hquart
        rw [neglog_eq hx2 (by linarith)] at hb
        exact (mul_le_mul_of_nonneg_left hb hs.le).trans hm.2
    have hH : (stripH n L2 s).Contains (Certificates.Mixed.hn u) := by
      unfold stripH; rw [if_pos h0]
      refine ⟨?_, ?_⟩
      · change ((0:ℤ):ℝ) ≤ _; push_cast
        exact mul_nonneg hs.le (hn_pos hu (by linarith)).le
      · exact (mul_le_mul_of_nonneg_left (hn_mono hu.le hule hx2h) hs.le).trans hH2.2
    exact ⟨hT, hQ, hK, hH, hUI, hu14⟩
  · -- regular strip
    have h3 := h1.2
    simp only [h0, decide_false, Bool.false_or] at h3
    have h4 := Bool.and_eq_true_iff.mp h3
    have hJ1pos : 0 < (nodeJ n L2 s.u1).lo := of_decide_eq_true h4.2
    obtain ⟨hx1, hx1h, hJ1, hL1, hQ1, hH1⟩ := node_facts (n := n) hL h4.1
    have hu1x : s.lo = s.u1.x := rfl
    have hgeu : s.u1.x ≤ u := hu1x ▸ hu1
    have hJu1 : jn u ≤ jn s.u1.x := jn_anti hx1 hgeu (by linarith)
    have hJu1pos : 0 < jn s.u1.x := jn_pos hx1 (by linarith)
    have hrec1 := DyadicInterval.recip_sound hJ1pos hJ1
    have hT : (stripT n L2 s).Contains (1 / jn u) := by
      unfold stripT; rw [if_neg h0]
      refine ⟨?_, ?_⟩
      · have hle : (jn s.u1.x)⁻¹ ≤ 1 / jn u := by
          rw [one_div]; exact inv_anti₀ hJupos hJu1
        exact hrec1.1.trans (mul_le_mul_of_nonneg_left hle hs.le)
      · have hle : 1 / jn u ≤ (jn s.u2.x)⁻¹ := by
          rw [one_div]; exact inv_anti₀ hJu2pos hJu
        exact (mul_le_mul_of_nonneg_left hle hs.le).trans hrec2.2
    have hQ : (stripQ s).Contains (qp u) :=
      Iv.hull_contains hQ1 hQ2 (qp_mono hx1.le hgeu (by linarith)) (qp_mono hu.le hule hx2h)
    have hK : (stripK n L2 s).Contains (qp u * jn u) := by
      unfold stripK; rw [if_neg h0]
      have hm1 := DyadicInterval.mul_sound hQ1 hJ2
      have hm2 := DyadicInterval.mul_sound hQ2 hJ1
      have hq1 : 0 ≤ qp s.u1.x := by unfold qp; nlinarith
      have hqu : 0 ≤ qp u := by unfold qp; nlinarith
      exact Iv.hull_contains hm1 hm2
        (mul_le_mul (qp_mono hx1.le hgeu (by linarith)) hJu hJu2pos.le hqu)
        (mul_le_mul (qp_mono hu.le hule hx2h) hJu1 hJupos.le (by unfold qp; nlinarith))
    have hH : (stripH n L2 s).Contains (Certificates.Mixed.hn u) := by
      unfold stripH; rw [if_neg h0]
      exact Iv.hull_contains hH1 hH2 (hn_mono hx1.le hgeu (by linarith)) (hn_mono hu.le hule hx2h)
    exact ⟨hT, hQ, hK, hH, hUI, hu14⟩

theorem h_stripu1 {n : ℕ} {L2 : DI} {s : FEStrip} (h : stripOKu n L2 s = true)
    (hne : s.u1.xa ≠ 0) : nodeOK s.u1 = true := by
  have h1 := (Bool.and_eq_true_iff.mp h).2
  simp only [hne, decide_false, Bool.false_or] at h1
  exact (Bool.and_eq_true_iff.mp h1).1

/-! ## Walking the `w`-cells of a strip -/

/-- Two-corner divided-difference bracket (convexity of `jn`). -/
def cellJ (n : ℕ) (L2 : DI) (s : FEStrip) (A B : Node) : DI :=
  Iv.mk (((nodeJ n L2 A).sub (nodeJ n L2 s.u1)).mul (Iv.pt (A.xa - s.u1.xa)).recip).lo
    (((nodeJ n L2 B).sub (nodeJ n L2 s.u2)).mul (Iv.pt (B.xa - s.u2.xa)).recip).hi

def cellCheck (n : ℕ) (L2 : DI) (s : FEStrip) (A B : Node) (cd : CData) : Bool :=
  nodeOK B && decide (A.xa < B.xa ∧ s.u2.xa < A.xa) &&
  feCore n L2 cd (stripT n L2 s) (stripQ s) (stripK n L2 s) (stripU s)
    (Iv.mk (nodeJ n L2 B).lo (nodeJ n L2 A).hi) (Iv.mk (nodeQ A).lo (nodeQ B).hi)
    (Iv.mk (A.xa - s.u2.xa) (B.xa - s.u1.xa))
    ((stripH n L2 s).add (Iv.mk (nodeH n L2 A).lo (nodeH n L2 B).hi))
    (decide (s.u1.xa ≠ 0)) (cellJ n L2 s A B)

def cellsCheck (n : ℕ) (L2 : DI) (s : FEStrip) : Node → List FECell → Bool
  | _, [] => true
  | A, c :: rest => cellCheck n L2 s A c.w c.cd && cellsCheck n L2 s c.w rest

def lastNode : Node → List FECell → Node
  | A, [] => A
  | _, c :: rest => lastNode c.w rest

theorem cellCheck_sound {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {s : FEStrip}
    (hs : stripOKu n L2 s = true) {A B : Node} {cd : CData} (hA : nodeOK A = true)
    (h : cellCheck n L2 s A B cd = true)
    {u w : ℝ} (hu : 0 < u) (hu1 : s.lo ≤ u) (hu2 : u ≤ s.hi) (hw1 : A.x ≤ w) (hw2 : w ≤ B.x)
    (hw : w < 1/2) :
    0 < (1 / jn u) * actualDetGapCoefficient u w ∧ 0 < m11 u w := by
  have hsc := SC_pos
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  obtain ⟨hT, hQ, hK, hH, hU, hu14⟩ := strip_atoms hL hs hu hu1 hu2
  obtain ⟨hxA, hxAh, hJA, hLA, hQA, hHA⟩ := node_facts (n := n) hL hA
  obtain ⟨hxB, hxBh, hJB, hLB, hQB, hHB⟩ := node_facts (n := n) hL h2.1
  have hw0 : 0 < w := hxA.trans_le hw1
  -- the core needs u < w; it follows from the positivity of the `s` interval
  have hcore := h1.2
  have hsI : (Iv.mk (A.xa - s.u2.xa) (B.xa - s.u1.xa)).Contains (w - u) := by
    obtain ⟨hU1, hU2⟩ := hU
    refine ⟨?_, ?_⟩
    · have e : (A.xa:ℝ) = (DyadicInterval.scale 64 : ℝ) * A.x := by unfold Node.x; field_simp
      change ((A.xa - s.u2.xa : ℤ):ℝ) ≤ _
      push_cast
      have := mul_le_mul_of_nonneg_left hw1 hsc.le
      change (s.u2.xa:ℝ) ≥ _ at hU2
      nlinarith
    · have e : (B.xa:ℝ) = (DyadicInterval.scale 64 : ℝ) * B.x := by unfold Node.x; field_simp
      change _ ≤ ((B.xa - s.u1.xa : ℤ):ℝ)
      push_cast
      have := mul_le_mul_of_nonneg_left hw2 hsc.le
      change (s.u1.xa:ℝ) ≤ _ at hU1
      nlinarith
  -- positivity of the s interval (checked inside feCore) gives u < w
  have hs0 : 0 < (Iv.mk (A.xa - s.u2.xa) (B.xa - s.u1.xa)).lo := by
    unfold feCore at hcore
    simp only [] at hcore
    have hh := (Bool.and_eq_true_iff.mp hcore).2
    exact (of_decide_eq_true hh).1
  have huw : u < w := by linarith [Iv.contains_pos hsI hs0]
  have hJw : (Iv.mk (nodeJ n L2 B).lo (nodeJ n L2 A).hi).Contains (jn w) :=
    Iv.hull_contains hJB hJA (jn_anti hw0 hw2 (by linarith)) (jn_anti hxA hw1 (by linarith))
  have hQw : (Iv.mk (nodeQ A).lo (nodeQ B).hi).Contains (qp w) :=
    Iv.hull_contains hQA hQB (qp_mono hxA.le hw1 (by linarith)) (qp_mono hw0.le hw2 hxBh)
  have hHw : (Iv.mk (nodeH n L2 A).lo (nodeH n L2 B).hi).Contains (Certificates.Mixed.hn w) :=
    Iv.hull_contains hHA hHB (hn_mono hxA.le hw1 (by linarith)) (hn_mono hw0.le hw2 hxBh)
  have hSI := DyadicInterval.add_sound hH hHw
  have hgs : A.xa < B.xa ∧ s.u2.xa < A.xa := of_decide_eq_true (Bool.and_eq_true_iff.mp h1.1).2
  have hj : decide (s.u1.xa ≠ 0) = true → (cellJ n L2 s A B).Contains ((jn w - jn u) / (w - u)) := by
    intro hne
    have hne' : s.u1.xa ≠ 0 := of_decide_eq_true hne
    have hs1 := h_stripu1 hs hne'
    obtain ⟨hx1, hx1h, hJ1, -, -, -⟩ := node_facts (n := n) hL hs1
    obtain ⟨hx2, hx2h, hJ2, -, -, -⟩ := node_facts (n := n) hL (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hs).1).1
    have hu1x : s.u1.x ≤ u := hu1
    have hu2x : u ≤ s.u2.x := hu2
    have h21 : s.u2.x < A.x := by
      unfold Node.x
      exact div_lt_div_of_pos_right (by exact_mod_cast hgs.2) hsc
    have hbr := jn_divided_difference_bracket hx1 hu1x hu2x h21 hw1 hw2 hxBh
    have hpA : (Iv.pt (A.xa - s.u1.xa)).Contains (A.x - s.u1.x) := by
      have := Iv.pt_contains (A.xa - s.u1.xa)
      unfold Node.x; push_cast at this ⊢; rw [sub_div] at this; exact this
    have hpB : (Iv.pt (B.xa - s.u2.xa)).Contains (B.x - s.u2.x) := by
      have := Iv.pt_contains (B.xa - s.u2.xa)
      unfold Node.x; push_cast at this ⊢; rw [sub_div] at this; exact this
    have hposA : 0 < (Iv.pt (A.xa - s.u1.xa)).lo := by
      change 0 < A.xa - s.u1.xa
      have : s.u1.xa ≤ s.u2.xa := le_of_lt (of_decide_eq_true (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp hs).1).2).2.1
      omega
    have hposB : 0 < (Iv.pt (B.xa - s.u2.xa)).lo := by
      change 0 < B.xa - s.u2.xa
      omega
    have hlo := DyadicInterval.mul_sound (DyadicInterval.sub_sound hJA hJ1)
      (DyadicInterval.recip_sound hposA hpA)
    have hhi := DyadicInterval.mul_sound (DyadicInterval.sub_sound hJB hJ2)
      (DyadicInterval.recip_sound hposB hpB)
    rw [← div_eq_mul_inv] at hlo hhi
    exact Iv.hull_contains hlo hhi hbr.1 hbr.2
  exact feCore_sound hL hcore hu huw hw hT hQ hK hU hJw hQw hsI hSI hj

theorem cellsCheck_sound {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {s : FEStrip}
    (hs : stripOKu n L2 s = true) :
    ∀ (cells : List FECell) (A : Node), nodeOK A = true → cellsCheck n L2 s A cells = true →
    ∀ {u w : ℝ}, 0 < u → s.lo ≤ u → u ≤ s.hi → A.x ≤ w → w ≤ (lastNode A cells).x → w < 1/2 →
      cells ≠ [] →
      0 < (1 / jn u) * actualDetGapCoefficient u w ∧ 0 < m11 u w := by
  intro cells
  induction cells with
  | nil => intro A _ _ u w _ _ _ _ _ _ hne; exact absurd rfl hne
  | cons c rest ih =>
    intro A hA h u w hu hu1 hu2 hw1 hw2 hw _
    have h1 := Bool.and_eq_true_iff.mp h
    have hB : nodeOK c.w = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h1.1).1).1
    by_cases hwc : w ≤ c.w.x
    · exact cellCheck_sound hL hs hA h1.1 hu hu1 hu2 hw1 hwc hw
    · have hlt : c.w.x < w := lt_of_not_ge hwc
      cases rest with
      | nil => simp [lastNode] at hw2; linarith
      | cons c' rest' =>
        exact ih c.w hB h1.2 hu hu1 hu2 hlt.le hw2 hw (List.cons_ne_nil _ _)

/-! ## The whole cover -/

def stripOK (n : ℕ) (L2 : DI) (s : FEStrip) : Bool :=
  stripOKu n L2 s && nodeOK s.w0 && decide (40 * s.w0.xa ≤ SCz) &&
  decide ((lastNode s.w0 s.cells).xa = SCz / 2) && decide (s.cells ≠ []) &&
  cellsCheck n L2 s s.w0 s.cells

/-- Consecutive strips starting at `u = 0`. -/
def chainOK : ℤ → List FEStrip → Bool
  | _, [] => true
  | a, s :: rest => decide (s.u1.xa = a) && chainOK s.u2.xa rest

def lastU : ℤ → List FEStrip → ℤ
  | a, [] => a
  | _, s :: rest => lastU s.u2.xa rest

def feCoverOK (n : ℕ) (strips : List FEStrip) : Bool :=
  chainOK 0 strips && decide (SCz ≤ 50 * lastU 0 strips) && decide (strips ≠ []) &&
    strips.all (stripOK n (ln2Iv n))

theorem strip_sound {n : ℕ} {s : FEStrip} (h : stripOK n (ln2Iv n) s = true)
    {u w : ℝ} (hu : 0 < u) (hu1 : s.lo ≤ u) (hu2 : u ≤ s.hi) (hw1 : 1/40 ≤ w) (hw : w < 1/2) :
    0 < (1 / jn u) * actualDetGapCoefficient u w ∧ 0 < m11 u w := by
  have hL := ln2Iv_contains n
  have hsc := SC_pos
  simp only [stripOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hsu, hw0⟩, hw040⟩, hlast⟩, hne⟩, hcells⟩ := h
  have hA : s.w0.x ≤ w := by
    unfold Node.x
    rw [div_le_iff₀ hsc]
    have : (40:ℝ) * s.w0.xa ≤ (SCz:ℝ) := by exact_mod_cast hw040
    rw [SCz_real] at this
    nlinarith
  have hB : w ≤ (lastNode s.w0 s.cells).x := by
    unfold Node.x
    rw [hlast]
    have h2 : ((SCz / 2 : ℤ):ℝ) = (DyadicInterval.scale 64 : ℝ) / 2 := by
      rw [show SCz / 2 = 2^63 by decide +kernel]
      rw [show (DyadicInterval.scale 64 : ℝ) = ((2^64 : ℤ):ℝ) from rfl]
      push_cast; ring
    rw [h2]
    have : (DyadicInterval.scale 64 : ℝ) / 2 / (DyadicInterval.scale 64 : ℝ) = 1/2 := by
      field_simp
    rw [this]; exact hw.le
  exact cellsCheck_sound hL hsu s.cells s.w0 hw0 hcells hu hu1 hu2 hA hB hw hne

theorem chain_cover : ∀ (strips : List FEStrip) (a : ℤ), chainOK a strips = true → strips ≠ [] →
    ∀ {u : ℝ}, (a:ℝ) / (DyadicInterval.scale 64 : ℝ) ≤ u →
      u ≤ (lastU a strips : ℝ) / (DyadicInterval.scale 64 : ℝ) →
      ∃ s ∈ strips, s.lo ≤ u ∧ u ≤ s.hi := by
  intro strips
  induction strips with
  | nil => intro a _ hne; exact absurd rfl hne
  | cons s rest ih =>
    intro a h _ u hu1 hu2
    have h1 := Bool.and_eq_true_iff.mp h
    have hs1 : s.u1.xa = a := of_decide_eq_true h1.1
    by_cases hus : u ≤ s.hi
    · refine ⟨s, List.mem_cons_self .., ?_, hus⟩
      unfold FEStrip.lo; rw [hs1]; exact hu1
    · cases rest with
      | nil => simp [lastU] at hu2; exact absurd hu2 (by unfold FEStrip.hi at hus; linarith)
      | cons s' rest' =>
        obtain ⟨t, ht, h1t, h2t⟩ := ih s.u2.xa h1.2 (List.cons_ne_nil _ _)
          (by unfold FEStrip.hi at hus; linarith) hu2
        exact ⟨t, List.mem_cons_of_mem _ ht, h1t, h2t⟩

/-- **Pointwise fixedEdge positivity from a checked cover.** -/
theorem fe_pointwise_of_cover {n : ℕ} {strips : List FEStrip} (h : feCoverOK n strips = true) :
    ∀ u w : ℝ, 0 < u → u ≤ 1/50 → 1/40 ≤ w → w < 1/2 →
      0 < (1 / jn u) * actualDetGapCoefficient u w ∧ 0 < m11 u w := by
  intro u w hu hu50 hw40 hw
  have hsc := SC_pos
  simp only [feCoverOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hchain, hlast⟩, hne⟩, hall⟩ := h
  have hu1 : ((0:ℤ):ℝ) / (DyadicInterval.scale 64 : ℝ) ≤ u := by simp; exact hu.le
  have hu2 : u ≤ (lastU 0 strips : ℝ) / (DyadicInterval.scale 64 : ℝ) := by
    rw [le_div_iff₀ hsc]
    have : (SCz:ℝ) ≤ 50 * (lastU 0 strips : ℝ) := by exact_mod_cast hlast
    rw [SCz_real] at this
    nlinarith
  obtain ⟨s, hs, hsu1, hsu2⟩ := chain_cover strips 0 hchain hne hu1 hu2
  exact strip_sound (hall s hs) hu hsu1 hsu2 hw40 hw

#print axioms node_facts
#print axioms strip_atoms
#print axioms cellCheck_sound
#print axioms cellsCheck_sound
#print axioms strip_sound
#print axioms chain_cover
#print axioms fe_pointwise_of_cover

end CKLaneA1


