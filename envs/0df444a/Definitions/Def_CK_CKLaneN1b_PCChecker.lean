-- Prove2me | Definitions.Def_CK_CKLaneN1b_PCChecker
-- name    : CK_CKLaneN1b_PCChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:14:35.084018+00:00
-- url     : https://prove2.me/theorems/aceb816a-cdd7-4f77-aac5-24c967403cb1
-- title:
--   Courtade–Kumar proof module `CKLaneN1b.PCChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1b.PCChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1b.PCChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1b.PCChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1b/PCChecker.lean)

import Definitions.Def_CK_CKLaneN1b_Points

-- ===== source module CKLaneN1b.PCChecker =====
section

/-!
# Lane N1b: the plane-cell checker (PC) and its unconditional soundness

A plane cell certifies `Sem B` on a box `B` with one global contact plane
`cost ≥ lam (b-a) - Ahi e - Bhi f` (`Plane.ok_sound`).  The entropy split is eliminated with
`min Ahi Bhi` (`plane_gap_bound`); the scalar gap is concave in the entropy deficit
(`gap_nonneg_of_ends`), so it suffices to check the two entropy endpoints `θ = t0, t1` of the box.
At each endpoint the gap is bounded below, uniformly over the mean rectangle, by an affine
function of `(a, b)` built from: a chord of the convex profile `P` over the information range,
a tangent of `P` at the lower end of the deficit range (slope from an exact anchor), a tangent of
the concave `H` at the mean-box centre, and chords/tangents of `H` in `a` and `b`.  The affine
bound is minimised over the box intersected with `b - a ≥ 1/50` by a Lagrange multiplier.

`PCCell.ok_sound : PCCell.ok B c = true → Sem B` has no other hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN1b

open GeneralCK GeneralCK.Scalar CKLaneE

/-- Data of one entropy endpoint `θ` of a plane cell. -/
structure PCEnd where
  pLo : ℚ
  pHi : ℚ
  xa : Pt
  xb : Pt
  sL : ℚ
  xc : Pt
  w : Pt
  mu : ℚ
  deriving Repr, DecidableEq

/-- A plane cell: contact plane, log points at the box nodes, two entropy endpoints. -/
structure PCCell where
  pl : Plane
  pa0 : Pt
  pa1 : Pt
  pb0 : Pt
  pb1 : Pt
  pml : Pt
  pmh : Pt
  pmc : Pt
  pac : Pt
  pbc : Pt
  e0 : PCEnd
  e1 : PCEnd
  deriving Repr, DecidableEq

namespace PCCell

def AH (c : PCCell) : ℚ := c.pl.Ahi
def BH (c : PCCell) : ℚ := c.pl.Bhi
def al (c : PCCell) : ℚ := 2 * min c.pl.Ahi c.pl.Bhi
def Clo (c : PCCell) : ℚ := (c.pa0.Hlo + c.pb1.Hlo) / 2
def Chi (c : PCCell) : ℚ := (c.pa1.Hhi + c.pb0.Hhi) / 2
def HmLo (c : PCCell) : ℚ := min c.pml.Hlo c.pmh.Hlo
def Jc (c : PCCell) : ℚ := (c.pmc.Jlo + c.pmc.Jhi) / 2
def eJ (c : PCCell) : ℚ := (c.pmc.Jhi - c.pmc.Jlo) / 2
def wm (B : Box) : ℚ := ((B.a1 + B.b1) / 2 - (B.a0 + B.b0) / 2) / 2
def HmHi (B : Box) (c : PCCell) : ℚ := c.pmc.Hhi + |c.Jc| * wm B + c.eJ * wm B
def mua (B : Box) (c : PCCell) : ℚ := (c.pa1.Hlo - c.pa0.Hlo) / (B.a1 - B.a0)
def mub (B : Box) (c : PCCell) : ℚ := (c.pb1.Hlo - c.pb0.Hlo) / (B.b1 - B.b0)
def Jca (c : PCCell) : ℚ := (c.pac.Jlo + c.pac.Jhi) / 2
def eJa (c : PCCell) : ℚ := (c.pac.Jhi - c.pac.Jlo) / 2
def Jcb (c : PCCell) : ℚ := (c.pbc.Jlo + c.pbc.Jhi) / 2
def eJb (c : PCCell) : ℚ := (c.pbc.Jhi - c.pbc.Jlo) / 2

end PCCell

namespace PCEnd

variable (B : Box) (c : PCCell) (th : ℚ) (e : PCEnd)

def IloB : ℚ := c.HmLo - th * c.Chi - (1 - th) * E0
def IhiB : ℚ := PCCell.HmHi B c - th * c.Clo - (1 - th) * E0
def PuLo : ℚ := (1 - 2 * e.xa.q) * e.xa.Jhi
def PuHi : ℚ := (1 - 2 * e.xb.q) * e.xb.Jhi
def sig : ℚ := (e.PuHi - e.PuLo) / (e.pHi - e.pLo)
def PlS : ℚ := if 0 < e.sL then (1 - 2 * e.xc.q) * e.xc.Jlo else 0
def tau : ℚ :=
  if 0 < e.sL then 2 + (1 - 2 * e.w.q) / (e.w.q * (1 - e.w.q) * (e.w.m1 - e.w.l0)) else 4
def gam : ℚ := (c.al * (1 - th) + e.sig * th + e.tau * (1 - th)) / 2
def ga : ℚ := gam c th e - c.AH
def gb : ℚ := gam c th e - c.BH
def K0 : ℚ :=
  -(c.al * (1 - th) * E0) - e.PuLo + e.sig * (1 - th) * E0 + e.sig * e.pLo + e.PlS -
    e.tau * (1 - th) * E0 - e.tau * e.sL
def aK : ℚ :=
  if 0 ≤ ga c th e then ga c th e * (c.pa0.Hlo - PCCell.mua B c * B.a0)
  else ga c th e * (c.pac.Hhi - c.Jca * c.pac.q + c.eJa * ((B.a1 - B.a0) / 2))
def aS : ℚ := if 0 ≤ ga c th e then ga c th e * PCCell.mua B c else ga c th e * c.Jca
def bK : ℚ :=
  if 0 ≤ gb c th e then gb c th e * (c.pb0.Hlo - PCCell.mub B c * B.b0)
  else gb c th e * (c.pbc.Hhi - c.Jcb * c.pbc.q + c.eJb * ((B.b1 - B.b0) / 2))
def bS : ℚ := if 0 ≤ gb c th e then gb c th e * PCCell.mub B c else gb c th e * c.Jcb
def c0 : ℚ :=
  K0 c th e - e.sig * (c.pmc.Hhi - c.Jc * c.pmc.q + c.eJ * PCCell.wm B) + aK B c th e + bK B c th e
def ca : ℚ := -c.pl.lam - e.sig * c.Jc / 2 + aS B c th e
def cb : ℚ := c.pl.lam - e.sig * c.Jc / 2 + bS B c th e
def fin : ℚ :=
  c0 B c th e + e.mu * DMIN + min ((ca B c th e + e.mu) * B.a0) ((ca B c th e + e.mu) * B.a1) +
    min ((cb B c th e - e.mu) * B.b0) ((cb B c th e - e.mu) * B.b1)

/-- The side condition for the deficit tangent (only used when `sL > 0`). -/
def slopeOk : Bool :=
  if 0 < e.sL then
    e.xc.ok && e.w.ok && decide (2 * e.xc.q ≤ 1 ∧ 1 - e.sL ≤ e.xc.Hlo ∧ 2 * e.w.q < 1 ∧
      0 < e.w.m1 - e.w.l0 ∧ 1 - e.w.Hlo ≤ e.sL)
  else true

/-- The Boolean check of one entropy endpoint. -/
def ok : Bool :=
  decide (0 ≤ th ∧ th ≤ 1) &&
  decide (0 ≤ e.pLo ∧ e.pLo ≤ IloB c th ∧ IhiB B c th ≤ e.pHi ∧ e.pLo < e.pHi ∧ e.pHi < 1) &&
  e.xa.ok && e.xb.ok &&
  decide (2 * e.xa.q ≤ 1 ∧ e.xa.Hhi ≤ 1 - e.pLo ∧ 2 * e.xb.q ≤ 1 ∧ e.xb.Hhi ≤ 1 - e.pHi) &&
  decide (0 ≤ e.sig) &&
  decide (0 ≤ e.sL ∧ e.sL ≤ (1 - th) * (c.Clo - E0)) &&
  e.slopeOk &&
  decide (0 ≤ e.mu ∧ 0 ≤ fin B c th e)

end PCEnd

namespace PCCell

/-- Box sanity, node/point binding, point checks and plane check. -/
def baseOk (B : Box) (c : PCCell) : Bool :=
  decide (0 < B.a0 ∧ B.a0 < B.a1 ∧ B.a1 ≤ 1 / 2 ∧ 1 / 2 ≤ B.b0 ∧ B.b0 < B.b1 ∧ B.b1 < 1 ∧
    0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1) &&
  decide (c.pa0.q = B.a0 ∧ c.pa1.q = B.a1 ∧ c.pb0.q = B.b0 ∧ c.pb1.q = B.b1 ∧
    c.pml.q = (B.a0 + B.b0) / 2 ∧ c.pmh.q = (B.a1 + B.b1) / 2 ∧
    c.pmc.q = ((B.a0 + B.b0) / 2 + (B.a1 + B.b1) / 2) / 2 ∧
    c.pac.q = (B.a0 + B.a1) / 2 ∧ c.pbc.q = (B.b0 + B.b1) / 2) &&
  c.pa0.ok && c.pa1.ok && c.pb0.ok && c.pb1.ok && c.pml.ok && c.pmh.ok && c.pmc.ok &&
  c.pac.ok && c.pbc.ok && c.pl.ok && decide (E0 ≤ c.Clo)

/-- The Boolean plane-cell checker. -/
def ok (B : Box) (c : PCCell) : Bool :=
  baseOk B c && c.e0.ok B c B.t0 && c.e1.ok B c B.t1

end PCCell

/-! ## Soundness -/

theorem cast_le_half {q : ℚ} (h : q ≤ 1 / 2) : (q : ℝ) ≤ 1 / 2 := by
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  exact h'

theorem half_le_cast {q : ℚ} (h : 1 / 2 ≤ q) : (1 / 2 : ℝ) ≤ (q : ℝ) := by
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  exact h'

/-- Error of a tangent with an enclosed slope. -/
theorem tangent_err {Jt Jl Jh u w : ℝ} (h1 : Jl ≤ Jt) (h2 : Jt ≤ Jh) (hu : |u| ≤ w) :
    Jt * u ≤ (Jl + Jh) / 2 * u + (Jh - Jl) / 2 * w := by
  have hw : 0 ≤ w := (abs_nonneg u).trans hu
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at hu
    nlinarith
  · rw [abs_of_nonpos h] at hu
    nlinarith

/-- The upper tangent of `H` at a checked point, uniformly on an interval of half-width `w`. -/
theorem H_tangent_upper {p : Pt} (hp : p.ok = true) {x w : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hxw : |x - (p.q : ℝ)| ≤ w) :
    H x ≤ ((p.Hhi : ℚ) : ℝ) + (((p.Jlo : ℚ) : ℝ) + ((p.Jhi : ℚ) : ℝ)) / 2 * (x - (p.q : ℝ)) +
      (((p.Jhi : ℚ) : ℝ) - ((p.Jlo : ℚ) : ℝ)) / 2 * w := by
  obtain ⟨hq0, hq1, _⟩ := Pt.ok_logs hp
  have hq0' : (0 : ℝ) < (p.q : ℝ) := by exact_mod_cast hq0
  have hq1' : (p.q : ℝ) < 1 := by exact_mod_cast hq1
  have ht := H_le_tangent hq0' hq1' hx0 hx1
  obtain ⟨_, hHh⟩ := Pt.H_bounds hp
  obtain ⟨hJl, hJh⟩ := Pt.J_bounds hp
  have he := tangent_err hJl hJh hxw
  linarith

set_option maxHeartbeats 2000000 in
theorem PCEnd.ok_sound {B : Box} {c : PCCell} {th : ℚ} {e : PCEnd}
    (hbase : PCCell.baseOk B c = true) (h : e.ok B c th = true)
    {a b : ℝ} (ha0 : (B.a0 : ℝ) ≤ a) (ha1 : a ≤ (B.a1 : ℝ)) (hb0 : (B.b0 : ℝ) ≤ b)
    (hb1 : b ≤ (B.b1 : ℝ)) (hd : (DMIN : ℝ) ≤ b - a) :
    0 ≤ gap ((c.pl.lam : ℝ) * (b - a) - (c.pl.Ahi : ℝ) * H a - (c.pl.Bhi : ℝ) * H b)
      (2 * min (c.pl.Ahi : ℝ) (c.pl.Bhi : ℝ)) (H ((a + b) / 2) - (H a + H b) / 2)
      ((1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ))) ∧
    H ((a + b) / 2) - (H a + H b) / 2 + (1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ)) <
      1 := by
  -- unpack the base facts
  unfold PCCell.baseOk at hbase
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbase
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, hq⟩, hpa0⟩, hpa1⟩, hpb0⟩, hpb1⟩, hpml⟩, hpmh⟩, hpmc⟩, hpac⟩, hpbc⟩,
    _hpl⟩, _hC⟩ := hbase
  obtain ⟨s1, s2, s3, s4, s5, s6, _, _, _⟩ := hbox
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := hq
  -- unpack the endpoint facts
  unfold PCEnd.ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hth0, hth1⟩, hp1, hp2, hp3, hp4, hp5⟩, hxa⟩, hxb⟩, hx1, hx2, hx3, hx4⟩, hsig⟩,
    hsL0, hsL1⟩, hslope⟩, hmu, hfin⟩ := h
  -- real versions of box facts
  have ra0 : (0 : ℝ) < (B.a0 : ℝ) := by exact_mod_cast s1
  have ra01 : (B.a0 : ℝ) < (B.a1 : ℝ) := by exact_mod_cast s2
  have ra1 : (B.a1 : ℝ) ≤ 1 / 2 := cast_le_half s3
  have rb0 : (1 / 2 : ℝ) ≤ (B.b0 : ℝ) := half_le_cast s4
  have rb01 : (B.b0 : ℝ) < (B.b1 : ℝ) := by exact_mod_cast s5
  have rb1 : (B.b1 : ℝ) < 1 := by exact_mod_cast s6
  have rth0 : (0 : ℝ) ≤ (th : ℝ) := by exact_mod_cast hth0
  have rth1 : (th : ℝ) ≤ 1 := by exact_mod_cast hth1
  -- entropy values at the nodes
  obtain ⟨Ha0l, _⟩ := Pt.H_bounds hpa0
  obtain ⟨Ha1l, Ha1h⟩ := Pt.H_bounds hpa1
  obtain ⟨Hb0l, Hb0h⟩ := Pt.H_bounds hpb0
  obtain ⟨Hb1l, _⟩ := Pt.H_bounds hpb1
  obtain ⟨Hmll, _⟩ := Pt.H_bounds hpml
  obtain ⟨Hmhl, _⟩ := Pt.H_bounds hpmh
  rw [q1] at Ha0l
  rw [q2] at Ha1l Ha1h
  rw [q3] at Hb0l Hb0h
  rw [q4] at Hb1l
  have ha0' : (0 : ℝ) < a := lt_of_lt_of_le ra0 ha0
  have hb1' : b < 1 := lt_of_le_of_lt hb1 rb1
  have hHa_lo : H (B.a0 : ℝ) ≤ H a := CKLaneD.H_mono_left ra0.le ha0 (ha1.trans ra1)
  have hHa_hi : H a ≤ H (B.a1 : ℝ) := CKLaneD.H_mono_left ha0'.le ha1 ra1
  have hHb_lo : H (B.b1 : ℝ) ≤ H b := CKLaneD.H_anti_right (rb0.trans hb0) hb1 rb1.le
  have hHb_hi : H b ≤ H (B.b0 : ℝ) := CKLaneD.H_anti_right rb0 hb0 hb1'.le
  have eClo : ((c.Clo : ℚ) : ℝ) = (((c.pa0.Hlo : ℚ) : ℝ) + ((c.pb1.Hlo : ℚ) : ℝ)) / 2 := by
    simp only [PCCell.Clo]; push_cast; ring
  have eChi : ((c.Chi : ℚ) : ℝ) = (((c.pa1.Hhi : ℚ) : ℝ) + ((c.pb0.Hhi : ℚ) : ℝ)) / 2 := by
    simp only [PCCell.Chi]; push_cast; ring
  have hClo : ((c.Clo : ℚ) : ℝ) ≤ (H a + H b) / 2 := by rw [eClo]; linarith
  have hChi : (H a + H b) / 2 ≤ ((c.Chi : ℚ) : ℝ) := by rw [eChi]; linarith
  -- the parent mean
  have eml : ((c.pml.q : ℚ) : ℝ) = ((B.a0 : ℝ) + (B.b0 : ℝ)) / 2 := by rw [q5]; push_cast; ring
  have emh : ((c.pmh.q : ℚ) : ℝ) = ((B.a1 : ℝ) + (B.b1 : ℝ)) / 2 := by rw [q6]; push_cast; ring
  have emc : ((c.pmc.q : ℚ) : ℝ) =
      (((B.a0 : ℝ) + (B.b0 : ℝ)) / 2 + ((B.a1 : ℝ) + (B.b1 : ℝ)) / 2) / 2 := by
    rw [q7]; push_cast; ring
  have ewm : ((PCCell.wm B : ℚ) : ℝ) =
      (((B.a1 : ℝ) + (B.b1 : ℝ)) / 2 - ((B.a0 : ℝ) + (B.b0 : ℝ)) / 2) / 2 := by
    simp only [PCCell.wm]; push_cast; ring
  have hm_lo : ((c.pml.q : ℚ) : ℝ) ≤ (a + b) / 2 := by rw [eml]; linarith
  have hm_hi : (a + b) / 2 ≤ ((c.pmh.q : ℚ) : ℝ) := by rw [emh]; linarith
  have hHmLo : ((c.HmLo : ℚ) : ℝ) ≤ H ((a + b) / 2) := by
    have hc := CKLaneD.H_chord_lower (lo := ((c.pml.q : ℚ) : ℝ)) (hi := ((c.pmh.q : ℚ) : ℝ))
      (x := (a + b) / 2) (HL0 := ((c.HmLo : ℚ) : ℝ)) (HL1 := ((c.HmLo : ℚ) : ℝ))
      (by rw [eml]; linarith) hm_lo hm_hi (by rw [emh]; linarith)
      (by unfold PCCell.HmLo; rw [Rat.cast_min]; exact (min_le_left _ _).trans Hmll)
      (by unfold PCCell.HmLo; rw [Rat.cast_min]; exact (min_le_right _ _).trans Hmhl)
    have e0 : ((c.HmLo : ℚ) : ℝ) = ((c.HmLo : ℚ) : ℝ) + (((c.HmLo : ℚ) : ℝ) - ((c.HmLo : ℚ) : ℝ)) /
        (((c.pmh.q : ℚ) : ℝ) - ((c.pml.q : ℚ) : ℝ)) * ((a + b) / 2 - ((c.pml.q : ℚ) : ℝ)) := by ring
    rw [e0]; exact hc
  have hmw : |(a + b) / 2 - ((c.pmc.q : ℚ) : ℝ)| ≤ ((PCCell.wm B : ℚ) : ℝ) := by
    rw [abs_le, emc, ewm]; constructor <;> linarith
  have hHmTan := H_tangent_upper hpmc (x := (a + b) / 2) (by linarith) (by linarith) hmw
  have eJc : ((c.Jc : ℚ) : ℝ) = (((c.pmc.Jlo : ℚ) : ℝ) + ((c.pmc.Jhi : ℚ) : ℝ)) / 2 := by
    simp only [PCCell.Jc]; push_cast; ring
  have eeJ : ((c.eJ : ℚ) : ℝ) = (((c.pmc.Jhi : ℚ) : ℝ) - ((c.pmc.Jlo : ℚ) : ℝ)) / 2 := by
    simp only [PCCell.eJ]; push_cast; ring
  rw [← eJc, ← eeJ] at hHmTan
  have hHmHi : H ((a + b) / 2) ≤ ((PCCell.HmHi B c : ℚ) : ℝ) := by
    have e : ((PCCell.HmHi B c : ℚ) : ℝ) = ((c.pmc.Hhi : ℚ) : ℝ) +
        |((c.Jc : ℚ) : ℝ)| * ((PCCell.wm B : ℚ) : ℝ) + ((c.eJ : ℚ) : ℝ) * ((PCCell.wm B : ℚ) : ℝ) := by
      simp only [PCCell.HmHi]; push_cast; ring
    have hJm : ((c.Jc : ℚ) : ℝ) * ((a + b) / 2 - ((c.pmc.q : ℚ) : ℝ)) ≤
        |((c.Jc : ℚ) : ℝ)| * ((PCCell.wm B : ℚ) : ℝ) := by
      calc ((c.Jc : ℚ) : ℝ) * ((a + b) / 2 - ((c.pmc.q : ℚ) : ℝ)) ≤
            |((c.Jc : ℚ) : ℝ) * ((a + b) / 2 - ((c.pmc.q : ℚ) : ℝ))| := le_abs_self _
        _ = |((c.Jc : ℚ) : ℝ)| * |(a + b) / 2 - ((c.pmc.q : ℚ) : ℝ)| := abs_mul _ _
        _ ≤ |((c.Jc : ℚ) : ℝ)| * ((PCCell.wm B : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left hmw (abs_nonneg _)
    rw [e]; linarith
  -- the information range
  have eIlo : ((PCEnd.IloB c th : ℚ) : ℝ) =
      ((c.HmLo : ℚ) : ℝ) - (th : ℝ) * ((c.Chi : ℚ) : ℝ) - (1 - (th : ℝ)) * (E0 : ℝ) := by
    simp only [PCEnd.IloB]; push_cast; ring
  have eIhi : ((PCEnd.IhiB B c th : ℚ) : ℝ) =
      ((PCCell.HmHi B c : ℚ) : ℝ) - (th : ℝ) * ((c.Clo : ℚ) : ℝ) - (1 - (th : ℝ)) * (E0 : ℝ) := by
    simp only [PCEnd.IhiB]; push_cast; ring
  have rp1 : (0 : ℝ) ≤ (e.pLo : ℝ) := by exact_mod_cast hp1
  have rp2 : (e.pLo : ℝ) ≤ ((PCEnd.IloB c th : ℚ) : ℝ) := by exact_mod_cast hp2
  have rp3 : ((PCEnd.IhiB B c th : ℚ) : ℝ) ≤ (e.pHi : ℝ) := by exact_mod_cast hp3
  have rp4 : (e.pLo : ℝ) < (e.pHi : ℝ) := by exact_mod_cast hp4
  have rp5 : (e.pHi : ℝ) < 1 := by exact_mod_cast hp5
  have hIlo : (e.pLo : ℝ) ≤
      H ((a + b) / 2) - (th : ℝ) * ((H a + H b) / 2) - (1 - (th : ℝ)) * (E0 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hChi rth0
    rw [eIlo] at rp2; linarith
  have hIhi : H ((a + b) / 2) - (th : ℝ) * ((H a + H b) / 2) - (1 - (th : ℝ)) * (E0 : ℝ) ≤
      (e.pHi : ℝ) := by
    have := mul_le_mul_of_nonneg_left hClo rth0
    rw [eIhi] at rp3; linarith
  -- profile chord on the information range
  obtain ⟨xa0, _, _, _, _, _⟩ := Pt.ok_logs hxa
  obtain ⟨xb0, _, _, _, _, _⟩ := Pt.ok_logs hxb
  obtain ⟨_, HxaH⟩ := Pt.H_bounds hxa
  obtain ⟨_, HxbH⟩ := Pt.H_bounds hxb
  obtain ⟨_, JxaH⟩ := Pt.J_bounds hxa
  obtain ⟨_, JxbH⟩ := Pt.J_bounds hxb
  have rx1 : 2 * (e.xa.q : ℝ) ≤ 1 := by exact_mod_cast hx1
  have rx2 : ((e.xa.Hhi : ℚ) : ℝ) ≤ 1 - (e.pLo : ℝ) := by exact_mod_cast hx2
  have rx3 : 2 * (e.xb.q : ℝ) ≤ 1 := by exact_mod_cast hx3
  have rx4 : ((e.xb.Hhi : ℚ) : ℝ) ≤ 1 - (e.pHi : ℝ) := by exact_mod_cast hx4
  have xa0' : (0 : ℝ) < (e.xa.q : ℝ) := by exact_mod_cast xa0
  have xb0' : (0 : ℝ) < (e.xb.q : ℝ) := by exact_mod_cast xb0
  have hPLo : P (e.pLo : ℝ) ≤ ((PCEnd.PuLo e : ℚ) : ℝ) := by
    have hbr := CKLaneD.P_le_bracket rp1 (by linarith) xa0' (by linarith) (HxaH.trans rx2)
    have ee : ((PCEnd.PuLo e : ℚ) : ℝ) = (1 - 2 * (e.xa.q : ℝ)) * ((e.xa.Jhi : ℚ) : ℝ) := by
      simp only [PCEnd.PuLo]; push_cast; ring
    have := mul_le_mul_of_nonneg_left JxaH (by linarith : (0 : ℝ) ≤ 1 - 2 * (e.xa.q : ℝ))
    rw [ee]; linarith
  have hPHi : P (e.pHi : ℝ) ≤ ((PCEnd.PuHi e : ℚ) : ℝ) := by
    have hbr := CKLaneD.P_le_bracket (by linarith) rp5 xb0' (by linarith) (HxbH.trans rx4)
    have ee : ((PCEnd.PuHi e : ℚ) : ℝ) = (1 - 2 * (e.xb.q : ℝ)) * ((e.xb.Jhi : ℚ) : ℝ) := by
      simp only [PCEnd.PuHi]; push_cast; ring
    have := mul_le_mul_of_nonneg_left JxbH (by linarith : (0 : ℝ) ≤ 1 - 2 * (e.xb.q : ℝ))
    rw [ee]; linarith
  have esig : ((PCEnd.sig e : ℚ) : ℝ) =
      (((PCEnd.PuHi e : ℚ) : ℝ) - ((PCEnd.PuLo e : ℚ) : ℝ)) / ((e.pHi : ℝ) - (e.pLo : ℝ)) := by
    simp only [PCEnd.sig]; push_cast; ring
  have hPI : P (H ((a + b) / 2) - (th : ℝ) * ((H a + H b) / 2) - (1 - (th : ℝ)) * (E0 : ℝ)) ≤
      ((PCEnd.PuLo e : ℚ) : ℝ) + ((PCEnd.sig e : ℚ) : ℝ) *
        (H ((a + b) / 2) - (th : ℝ) * ((H a + H b) / 2) - (1 - (th : ℝ)) * (E0 : ℝ) -
          (e.pLo : ℝ)) := by
    have hch := CKLaneD.P_chord rp1 hIlo hIhi rp5 rp4
    have hm2 := CKLaneD.chord_mono (f0 := P (e.pLo : ℝ)) (f1 := P (e.pHi : ℝ))
      (g0 := ((PCEnd.PuLo e : ℚ) : ℝ)) (g1 := ((PCEnd.PuHi e : ℚ) : ℝ))
      (Δ := (e.pHi : ℝ) - (e.pLo : ℝ))
      (x := H ((a + b) / 2) - (th : ℝ) * ((H a + H b) / 2) - (1 - (th : ℝ)) * (E0 : ℝ) -
        (e.pLo : ℝ))
      (by linarith) (by linarith) (by linarith) hPLo hPHi
    rw [esig]; exact hch.trans hm2
  -- the deficit range
  have hHa1 : H a ≤ 1 := H_le_one a
  have hHb1 : H b ≤ 1 := H_le_one b
  have rsL0 : (0 : ℝ) ≤ (e.sL : ℝ) := by exact_mod_cast hsL0
  have rsL1 : (e.sL : ℝ) ≤ (1 - (th : ℝ)) * (((c.Clo : ℚ) : ℝ) - (E0 : ℝ)) := by
    exact_mod_cast hsL1
  have hE0 : ((E0 : ℚ) : ℝ) = 11 / 200 := by norm_num [E0]
  have hsL : (e.sL : ℝ) ≤ (1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left
      (by linarith : ((c.Clo : ℚ) : ℝ) - (E0 : ℝ) ≤ (H a + H b) / 2 - (E0 : ℝ))
      (by linarith : (0 : ℝ) ≤ 1 - (th : ℝ))
    linarith
  have hs1 : (1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ)) < 1 := by
    have hC1 : (H a + H b) / 2 - (E0 : ℝ) < 1 := by rw [hE0]; linarith
    rcases le_or_gt ((H a + H b) / 2 - (E0 : ℝ)) 0 with hneg | hpos
    · have : (1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
      linarith
    · have hth := mul_nonneg rth0 hpos.le
      linarith only [hth, hC1]
  -- profile tangent on the deficit side
  have hPs : ((PCEnd.PlS e : ℚ) : ℝ) + ((PCEnd.tau e : ℚ) : ℝ) *
      ((1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ)) - (e.sL : ℝ)) ≤
      P ((1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ))) := by
    unfold PCEnd.slopeOk at hslope
    by_cases hpos : 0 < e.sL
    · rw [if_pos hpos] at hslope
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hslope
      obtain ⟨⟨hxc, hw⟩, c1, c2, c3, c4, c5⟩ := hslope
      obtain ⟨xc0, _, _, _, _, _⟩ := Pt.ok_logs hxc
      obtain ⟨w0, _, _, _, _, _⟩ := Pt.ok_logs hw
      have xc0' : (0 : ℝ) < (e.xc.q : ℝ) := by exact_mod_cast xc0
      have w0' : (0 : ℝ) < (e.w.q : ℝ) := by exact_mod_cast w0
      obtain ⟨HxcL, _⟩ := Pt.H_bounds hxc
      obtain ⟨JxcL, _⟩ := Pt.J_bounds hxc
      obtain ⟨HwL, _⟩ := Pt.H_bounds hw
      have rc1 : 2 * (e.xc.q : ℝ) ≤ 1 := by exact_mod_cast c1
      have rc2 : 1 - (e.sL : ℝ) ≤ ((e.xc.Hlo : ℚ) : ℝ) := by exact_mod_cast c2
      have rc3 : 2 * (e.w.q : ℝ) < 1 := by exact_mod_cast c3
      have rc4 : (0 : ℝ) < ((e.w.m1 - e.w.l0 : ℚ) : ℝ) := by exact_mod_cast c4
      have rc5 : 1 - ((e.w.Hlo : ℚ) : ℝ) ≤ (e.sL : ℝ) := by exact_mod_cast c5
      have hsl1 : (e.sL : ℝ) < 1 := lt_of_le_of_lt hsL hs1
      have hbr := CKLaneD.P_ge_bracket rsL0 hsl1 xc0' (by linarith) (rc2.trans HxcL)
      have ePlS : ((PCEnd.PlS e : ℚ) : ℝ) = (1 - 2 * (e.xc.q : ℝ)) * ((e.xc.Jlo : ℚ) : ℝ) := by
        simp only [PCEnd.PlS, if_pos hpos]; push_cast; ring
      have hval : ((PCEnd.PlS e : ℚ) : ℝ) ≤ P (e.sL : ℝ) := by
        have := mul_le_mul_of_nonneg_left JxcL (by linarith : (0 : ℝ) ≤ 1 - 2 * (e.xc.q : ℝ))
        rw [ePlS]; linarith
      have hanch := anchor_le_P1 w0' (by linarith) (by linarith : 1 - H (e.w.q : ℝ) ≤ (e.sL : ℝ))
        hsl1
      have hlam := Pt.lam_le hw
      have hww : (0 : ℝ) < (e.w.q : ℝ) * (1 - (e.w.q : ℝ)) := by
        have : (0 : ℝ) < 1 - (e.w.q : ℝ) := by linarith
        positivity
      have hlogpos : 0 < Real.log ((1 - (e.w.q : ℝ)) / (e.w.q : ℝ)) := by
        apply Real.log_pos
        rw [lt_div_iff₀ w0']; linarith
      have etau : ((PCEnd.tau e : ℚ) : ℝ) = 2 + (1 - 2 * (e.w.q : ℝ)) /
          ((e.w.q : ℝ) * (1 - (e.w.q : ℝ)) * ((e.w.m1 - e.w.l0 : ℚ) : ℝ)) := by
        simp only [PCEnd.tau, if_pos hpos]; push_cast; ring
      have htau : ((PCEnd.tau e : ℚ) : ℝ) ≤ P1 (e.sL : ℝ) := by
        rw [etau]
        have hfr : (1 - 2 * (e.w.q : ℝ)) /
            ((e.w.q : ℝ) * (1 - (e.w.q : ℝ)) * ((e.w.m1 - e.w.l0 : ℚ) : ℝ)) ≤
            (1 - 2 * (e.w.q : ℝ)) /
            ((e.w.q : ℝ) * (1 - (e.w.q : ℝ)) * Real.log ((1 - (e.w.q : ℝ)) / (e.w.q : ℝ))) := by
          apply div_le_div_of_nonneg_left (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_left hlam hww.le
        linarith
      have htan := P_tangent_lower rsL0 hsL hs1
      have := mul_le_mul_of_nonneg_right htau
        (by linarith : (0 : ℝ) ≤ (1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ)) - (e.sL : ℝ))
      linarith
    · have hs0 : e.sL = 0 := le_antisymm (not_lt.mp hpos) hsL0
      have ePlS : ((PCEnd.PlS e : ℚ) : ℝ) = 0 := by
        simp only [PCEnd.PlS, if_neg hpos, Rat.cast_zero]
      have etau : ((PCEnd.tau e : ℚ) : ℝ) = 4 := by
        simp only [PCEnd.tau, if_neg hpos]; norm_num
      have hs0' : (0 : ℝ) ≤ (1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ)) := by
        rw [hs0, Rat.cast_zero] at hsL; exact hsL
      rw [ePlS, etau, hs0, Rat.cast_zero]
      have := four_mul_le_P hs0' hs1
      linarith
  -- the entropy coefficients of a and b
  have rsig : (0 : ℝ) ≤ ((PCEnd.sig e : ℚ) : ℝ) := by exact_mod_cast hsig
  have hA : ((PCEnd.ga c th e : ℚ) : ℝ) * H a ≥
      ((PCEnd.aK B c th e : ℚ) : ℝ) + ((PCEnd.aS B c th e : ℚ) : ℝ) * a := by
    by_cases hg : 0 ≤ PCEnd.ga c th e
    · have eK : ((PCEnd.aK B c th e : ℚ) : ℝ) = ((PCEnd.ga c th e : ℚ) : ℝ) *
          (((c.pa0.Hlo : ℚ) : ℝ) - ((PCCell.mua B c : ℚ) : ℝ) * (B.a0 : ℝ)) := by
        simp only [PCEnd.aK, if_pos hg]; push_cast; ring
      have eS : ((PCEnd.aS B c th e : ℚ) : ℝ) =
          ((PCEnd.ga c th e : ℚ) : ℝ) * ((PCCell.mua B c : ℚ) : ℝ) := by
        simp only [PCEnd.aS, if_pos hg]; push_cast; ring
      have emua : ((PCCell.mua B c : ℚ) : ℝ) =
          (((c.pa1.Hlo : ℚ) : ℝ) - ((c.pa0.Hlo : ℚ) : ℝ)) / ((B.a1 : ℝ) - (B.a0 : ℝ)) := by
        simp only [PCCell.mua]; push_cast; ring
      have hch := CKLaneD.H_chord_lower (lo := (B.a0 : ℝ)) (hi := (B.a1 : ℝ)) (x := a)
        (HL0 := ((c.pa0.Hlo : ℚ) : ℝ)) (HL1 := ((c.pa1.Hlo : ℚ) : ℝ)) ra0.le ha0 ha1
        (by linarith) Ha0l Ha1l
      rw [← emua] at hch
      have rg : (0 : ℝ) ≤ ((PCEnd.ga c th e : ℚ) : ℝ) := by exact_mod_cast hg
      have := mul_le_mul_of_nonneg_left hch rg
      rw [eK, eS]; linarith
    · have eK : ((PCEnd.aK B c th e : ℚ) : ℝ) = ((PCEnd.ga c th e : ℚ) : ℝ) *
          (((c.pac.Hhi : ℚ) : ℝ) - ((c.Jca : ℚ) : ℝ) * ((c.pac.q : ℚ) : ℝ) +
            ((c.eJa : ℚ) : ℝ) * (((B.a1 : ℝ) - (B.a0 : ℝ)) / 2)) := by
        simp only [PCEnd.aK, if_neg hg]; push_cast; ring
      have eS : ((PCEnd.aS B c th e : ℚ) : ℝ) =
          ((PCEnd.ga c th e : ℚ) : ℝ) * ((c.Jca : ℚ) : ℝ) := by
        simp only [PCEnd.aS, if_neg hg]; push_cast; ring
      have eac : ((c.pac.q : ℚ) : ℝ) = ((B.a0 : ℝ) + (B.a1 : ℝ)) / 2 := by
        rw [q8]; push_cast; ring
      have haw : |a - ((c.pac.q : ℚ) : ℝ)| ≤ ((B.a1 : ℝ) - (B.a0 : ℝ)) / 2 := by
        rw [abs_le, eac]; constructor <;> linarith
      have ht := H_tangent_upper hpac (x := a) ha0'.le (by linarith) haw
      have eJca : ((c.Jca : ℚ) : ℝ) = (((c.pac.Jlo : ℚ) : ℝ) + ((c.pac.Jhi : ℚ) : ℝ)) / 2 := by
        simp only [PCCell.Jca]; push_cast; ring
      have eeJa : ((c.eJa : ℚ) : ℝ) = (((c.pac.Jhi : ℚ) : ℝ) - ((c.pac.Jlo : ℚ) : ℝ)) / 2 := by
        simp only [PCCell.eJa]; push_cast; ring
      rw [← eJca, ← eeJa] at ht
      have rg : ((PCEnd.ga c th e : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast (le_of_lt (lt_of_not_ge hg))
      have := mul_le_mul_of_nonpos_left ht rg
      rw [eK, eS]; linarith
  have hB : ((PCEnd.gb c th e : ℚ) : ℝ) * H b ≥
      ((PCEnd.bK B c th e : ℚ) : ℝ) + ((PCEnd.bS B c th e : ℚ) : ℝ) * b := by
    by_cases hg : 0 ≤ PCEnd.gb c th e
    · have eK : ((PCEnd.bK B c th e : ℚ) : ℝ) = ((PCEnd.gb c th e : ℚ) : ℝ) *
          (((c.pb0.Hlo : ℚ) : ℝ) - ((PCCell.mub B c : ℚ) : ℝ) * (B.b0 : ℝ)) := by
        simp only [PCEnd.bK, if_pos hg]; push_cast; ring
      have eS : ((PCEnd.bS B c th e : ℚ) : ℝ) =
          ((PCEnd.gb c th e : ℚ) : ℝ) * ((PCCell.mub B c : ℚ) : ℝ) := by
        simp only [PCEnd.bS, if_pos hg]; push_cast; ring
      have emub : ((PCCell.mub B c : ℚ) : ℝ) =
          (((c.pb1.Hlo : ℚ) : ℝ) - ((c.pb0.Hlo : ℚ) : ℝ)) / ((B.b1 : ℝ) - (B.b0 : ℝ)) := by
        simp only [PCCell.mub]; push_cast; ring
      have hch := CKLaneD.H_chord_lower (lo := (B.b0 : ℝ)) (hi := (B.b1 : ℝ)) (x := b)
        (HL0 := ((c.pb0.Hlo : ℚ) : ℝ)) (HL1 := ((c.pb1.Hlo : ℚ) : ℝ)) (by linarith) hb0 hb1
        rb1.le Hb0l Hb1l
      rw [← emub] at hch
      have rg : (0 : ℝ) ≤ ((PCEnd.gb c th e : ℚ) : ℝ) := by exact_mod_cast hg
      have := mul_le_mul_of_nonneg_left hch rg
      rw [eK, eS]; linarith
    · have eK : ((PCEnd.bK B c th e : ℚ) : ℝ) = ((PCEnd.gb c th e : ℚ) : ℝ) *
          (((c.pbc.Hhi : ℚ) : ℝ) - ((c.Jcb : ℚ) : ℝ) * ((c.pbc.q : ℚ) : ℝ) +
            ((c.eJb : ℚ) : ℝ) * (((B.b1 : ℝ) - (B.b0 : ℝ)) / 2)) := by
        simp only [PCEnd.bK, if_neg hg]; push_cast; ring
      have eS : ((PCEnd.bS B c th e : ℚ) : ℝ) =
          ((PCEnd.gb c th e : ℚ) : ℝ) * ((c.Jcb : ℚ) : ℝ) := by
        simp only [PCEnd.bS, if_neg hg]; push_cast; ring
      have ebc : ((c.pbc.q : ℚ) : ℝ) = ((B.b0 : ℝ) + (B.b1 : ℝ)) / 2 := by
        rw [q9]; push_cast; ring
      have hbw : |b - ((c.pbc.q : ℚ) : ℝ)| ≤ ((B.b1 : ℝ) - (B.b0 : ℝ)) / 2 := by
        rw [abs_le, ebc]; constructor <;> linarith
      have ht := H_tangent_upper hpbc (x := b) (by linarith) hb1'.le hbw
      have eJcb : ((c.Jcb : ℚ) : ℝ) = (((c.pbc.Jlo : ℚ) : ℝ) + ((c.pbc.Jhi : ℚ) : ℝ)) / 2 := by
        simp only [PCCell.Jcb]; push_cast; ring
      have eeJb : ((c.eJb : ℚ) : ℝ) = (((c.pbc.Jhi : ℚ) : ℝ) - ((c.pbc.Jlo : ℚ) : ℝ)) / 2 := by
        simp only [PCCell.eJb]; push_cast; ring
      rw [← eJcb, ← eeJb] at ht
      have rg : ((PCEnd.gb c th e : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast (le_of_lt (lt_of_not_ge hg))
      have := mul_le_mul_of_nonpos_left ht rg
      rw [eK, eS]; linarith
  -- the final affine bound
  have rmu : (0 : ℝ) ≤ (e.mu : ℝ) := by exact_mod_cast hmu
  have rfin : (0 : ℝ) ≤ ((PCEnd.fin B c th e : ℚ) : ℝ) := by exact_mod_cast hfin
  have hcorner : (0 : ℝ) ≤ ((PCEnd.c0 B c th e : ℚ) : ℝ) + ((PCEnd.ca B c th e : ℚ) : ℝ) * a +
      ((PCEnd.cb B c th e : ℚ) : ℝ) * b := by
    have e1 := CKLaneD.min_mul_le (q := PCEnd.ca B c th e + e.mu) ha0 ha1
    have e2 := CKLaneD.min_mul_le (q := PCEnd.cb B c th e - e.mu) hb0 hb1
    have ef : ((PCEnd.fin B c th e : ℚ) : ℝ) = ((PCEnd.c0 B c th e : ℚ) : ℝ) +
        (e.mu : ℝ) * (DMIN : ℝ) +
        ((min ((PCEnd.ca B c th e + e.mu) * B.a0) ((PCEnd.ca B c th e + e.mu) * B.a1) : ℚ) : ℝ) +
        ((min ((PCEnd.cb B c th e - e.mu) * B.b0) ((PCEnd.cb B c th e - e.mu) * B.b1) : ℚ) : ℝ) := by
      simp only [PCEnd.fin]; push_cast; ring
    rw [Rat.cast_add] at e1
    rw [Rat.cast_sub] at e2
    have hmud := mul_le_mul_of_nonneg_left hd rmu
    rw [ef] at rfin
    linarith only [rfin, e1, e2, hmud]
  -- assemble
  have hgapI : H ((a + b) / 2) - (H a + H b) / 2 + (1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ)) =
      H ((a + b) / 2) - (th : ℝ) * ((H a + H b) / 2) - (1 - (th : ℝ)) * (E0 : ℝ) := by ring
  refine ⟨?_, ?_⟩
  · unfold gap
    rw [hgapI]
    have eal : ((PCCell.al c : ℚ) : ℝ) = 2 * min ((c.pl.Ahi : ℚ) : ℝ) ((c.pl.Bhi : ℚ) : ℝ) := by
      simp only [PCCell.al]; push_cast; ring
    have ec0 : ((PCEnd.c0 B c th e : ℚ) : ℝ) = ((PCEnd.K0 c th e : ℚ) : ℝ) -
        ((PCEnd.sig e : ℚ) : ℝ) * (((c.pmc.Hhi : ℚ) : ℝ) - ((c.Jc : ℚ) : ℝ) * ((c.pmc.q : ℚ) : ℝ) +
          ((c.eJ : ℚ) : ℝ) * ((PCCell.wm B : ℚ) : ℝ)) +
        ((PCEnd.aK B c th e : ℚ) : ℝ) + ((PCEnd.bK B c th e : ℚ) : ℝ) := by
      simp only [PCEnd.c0]; push_cast; ring
    have eca : ((PCEnd.ca B c th e : ℚ) : ℝ) = -((c.pl.lam : ℚ) : ℝ) -
        ((PCEnd.sig e : ℚ) : ℝ) * ((c.Jc : ℚ) : ℝ) / 2 + ((PCEnd.aS B c th e : ℚ) : ℝ) := by
      simp only [PCEnd.ca]; push_cast; ring
    have ecb : ((PCEnd.cb B c th e : ℚ) : ℝ) = ((c.pl.lam : ℚ) : ℝ) -
        ((PCEnd.sig e : ℚ) : ℝ) * ((c.Jc : ℚ) : ℝ) / 2 + ((PCEnd.bS B c th e : ℚ) : ℝ) := by
      simp only [PCEnd.cb]; push_cast; ring
    have eK0 : ((PCEnd.K0 c th e : ℚ) : ℝ) =
        -(((PCCell.al c : ℚ) : ℝ) * (1 - (th : ℝ)) * (E0 : ℝ)) -
        ((PCEnd.PuLo e : ℚ) : ℝ) + ((PCEnd.sig e : ℚ) : ℝ) * (1 - (th : ℝ)) * (E0 : ℝ) +
        ((PCEnd.sig e : ℚ) : ℝ) * (e.pLo : ℝ) + ((PCEnd.PlS e : ℚ) : ℝ) -
        ((PCEnd.tau e : ℚ) : ℝ) * (1 - (th : ℝ)) * (E0 : ℝ) -
        ((PCEnd.tau e : ℚ) : ℝ) * (e.sL : ℝ) := by
      simp only [PCEnd.K0]; push_cast; ring
    have ega : ((PCEnd.ga c th e : ℚ) : ℝ) = (((PCCell.al c : ℚ) : ℝ) * (1 - (th : ℝ)) +
        ((PCEnd.sig e : ℚ) : ℝ) * (th : ℝ) + ((PCEnd.tau e : ℚ) : ℝ) * (1 - (th : ℝ))) / 2 -
        ((c.pl.Ahi : ℚ) : ℝ) := by
      simp only [PCEnd.ga, PCEnd.gam, PCCell.AH]; push_cast; ring
    have egb : ((PCEnd.gb c th e : ℚ) : ℝ) = (((PCCell.al c : ℚ) : ℝ) * (1 - (th : ℝ)) +
        ((PCEnd.sig e : ℚ) : ℝ) * (th : ℝ) + ((PCEnd.tau e : ℚ) : ℝ) * (1 - (th : ℝ))) / 2 -
        ((c.pl.Bhi : ℚ) : ℝ) := by
      simp only [PCEnd.gb, PCEnd.gam, PCCell.BH]; push_cast; ring
    rw [← eal]
    rw [ec0, eK0, eca, ecb] at hcorner
    rw [ega] at hA
    rw [egb] at hB
    have hsigHm := mul_le_mul_of_nonneg_left hHmTan rsig
    generalize P (H ((a + b) / 2) - (th : ℝ) * ((H a + H b) / 2) - (1 - (th : ℝ)) * (E0 : ℝ)) = PI
      at hPI ⊢
    generalize P ((1 - (th : ℝ)) * ((H a + H b) / 2 - (E0 : ℝ))) = PS at hPs ⊢
    linarith only [hPI, hPs, hA, hB, hsigHm, hcorner]
  · rw [hgapI]
    linarith

/-- Unconditional soundness of the plane-cell checker. -/
theorem PCCell.ok_sound {B : Box} {c : PCCell} (h : PCCell.ok B c = true) : Sem B := by
  unfold PCCell.ok at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hbase, h0⟩, h1⟩ := h
  have hbase' := hbase
  unfold PCCell.baseOk at hbase'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbase'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, hq⟩, hpa0⟩, _⟩, _⟩, hpb1⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hpl⟩, hC⟩ := hbase'
  obtain ⟨s1, _, s3, s4, _, s6, st0, st01, st1⟩ := hbox
  obtain ⟨q1, _, _, q4, _, _, _, _, _⟩ := hq
  intro k μ hin hd
  obtain ⟨ha0, ha1, hb0, hb1, hE0, hE1⟩ := hin
  have ha1' : μ.a ≤ (1 / 2 : ℝ) := ha1.trans (cast_le_half s3)
  have hb0' : (1 / 2 : ℝ) ≤ μ.b := le_trans (half_le_cast s4) hb0
  have hab : μ.a ≤ μ.b := by linarith
  obtain ⟨hplane, _, _⟩ := Plane.ok_sound hpl μ hab
  obtain ⟨g0, cap0⟩ := PCEnd.ok_sound hbase h0 ha0 ha1 hb0 hb1 hd
  obtain ⟨g1, _⟩ := PCEnd.ok_sound hbase h1 ha0 ha1 hb0 hb1 hd
  apply plane_gap_bound μ hplane
  -- concavity between the two entropy endpoints
  have rt0 : (0 : ℝ) ≤ (B.t0 : ℝ) := by exact_mod_cast st0
  have rt01 : (B.t0 : ℝ) ≤ (B.t1 : ℝ) := by exact_mod_cast st01
  have rt1 : (B.t1 : ℝ) ≤ 1 := by exact_mod_cast st1
  -- C ≥ E0 on the box
  obtain ⟨Ha0l, _⟩ := Pt.H_bounds hpa0
  obtain ⟨Hb1l, _⟩ := Pt.H_bounds hpb1
  rw [q1] at Ha0l
  rw [q4] at Hb1l
  have ra0 : (0 : ℝ) < (B.a0 : ℝ) := by exact_mod_cast s1
  have rb1 : (B.b1 : ℝ) < 1 := by exact_mod_cast s6
  have hHa := CKLaneD.H_mono_left ra0.le ha0 ha1'
  have hHb := CKLaneD.H_anti_right hb0' hb1 rb1.le
  have rC : ((E0 : ℚ) : ℝ) ≤ ((c.Clo : ℚ) : ℝ) := by exact_mod_cast hC
  have eClo : ((c.Clo : ℚ) : ℝ) = (((c.pa0.Hlo : ℚ) : ℝ) + ((c.pb1.Hlo : ℚ) : ℝ)) / 2 := by
    simp only [PCCell.Clo]; push_cast; ring
  have hCE : (0 : ℝ) ≤ (H μ.a + H μ.b) / 2 - (E0 : ℝ) := by rw [eClo] at rC; linarith
  have hΔ := jensenGap_nonneg (μ.a_interior.1.le) (μ.a_interior.2.le) (μ.b_interior.1.le)
    (μ.b_interior.2.le)
  have hs0 : 0 ≤ (1 - (B.t1 : ℝ)) * ((H μ.a + H μ.b) / 2 - (E0 : ℝ)) :=
    mul_nonneg (by linarith) hCE
  have hs01 : (1 - (B.t1 : ℝ)) * ((H μ.a + H μ.b) / 2 - (E0 : ℝ)) ≤
      (1 - (B.t0 : ℝ)) * ((H μ.a + H μ.b) / 2 - (E0 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hCE
  have hsA : (1 - (B.t1 : ℝ)) * ((H μ.a + H μ.b) / 2 - (E0 : ℝ)) ≤
      (H μ.a + H μ.b) / 2 - μ.meanEntropy := by linarith
  have hsB : (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤
      (1 - (B.t0 : ℝ)) * ((H μ.a + H μ.b) / 2 - (E0 : ℝ)) := by linarith
  exact gap_nonneg_of_ends hΔ hs0 hs01 cap0 hsA hsB g1 g0

end CKLaneN1b

end


