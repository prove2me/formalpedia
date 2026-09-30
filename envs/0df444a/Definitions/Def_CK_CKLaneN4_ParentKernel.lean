-- Prove2me | Definitions.Def_CK_CKLaneN4_ParentKernel
-- name    : CK_CKLaneN4_ParentKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:42:21.562571+00:00
-- url     : https://prove2.me/theorems/7df307db-22bb-4ce8-afe3-eaf50c320214
-- title:
--   Courtade–Kumar proof module `CKLaneN4.ParentKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.ParentKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.ParentKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.ParentKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/ParentKernel.lean)

import Definitions.Def_CK_CKLaneD_Analytic
import Definitions.Def_CK_GeneralCK_RadialConvexity
import Definitions.Def_CK_GeneralCK_EntropyParabola

-- ===== source module CKLaneN4.ParentKernel =====
section

/-!
# Lane N4: reflective parent-dominance checker on scalar boxes

Archive: `PARENT8.py` / `PARENT16.py` (boxes in `(q, x)`, `x = q / E`) and `HIGH_Q_PARENT.py`
(boxes in `(q, E)`).  The acceptance inequality of every archived leaf is

  `eta(E*) - eta(E* + C(q_-)) - F_upper > 0`,

with `E*` an upper bound of `E` on the box, because `eta` is convex and decreasing (so
`eta E - eta (E + C)` decreases in `E` and increases in `C`), `C(q) = 1 - H((1-q)/2)` increases in `q`,
and `F(q, E) = q J(v(q/E))` increases in `q` and in `q / E`.

`checkQX B c = true → SemQX B` and `checkQE B c = true → SemQE B` with no other hypotheses: the
checkers recompute every derived quantity from the box and verify every primitive enclosure (log
certificates of all `H`/`J` evaluations, both `eta` brackets and the radial-contact bracket).  No margin is
stored.  `CTree` aggregates boxes by exact halving (the archived binary partitions).

The first four lemmas are copied (verbatim statements) from Lane M12 `CKLaneM12.Analytic`.
-/

namespace CKLaneN4

open GeneralCK CKLaneD Set

/-! ## Analytic lemmas (unconditional) -/

/-- Increments of the convex `eta` shrink when the base point moves right (on `(0, 1]`). -/
theorem eta_increment_mono {x x' c : ℝ} (hx : 0 < x) (hxx : x ≤ x') (hc : 0 ≤ c)
    (h1 : x' + c ≤ 1) :
    eta x' - eta (x' + c) ≤ eta x - eta (x + c) := by
  rcases hc.eq_or_lt with h0 | hc'
  · subst h0
    simp
  have hD : 0 < x' + c - x := by linarith
  set l := c / (x' + c - x) with hl
  have hl0 : 0 ≤ l := div_nonneg hc hD.le
  have hl1 : l ≤ 1 := by rw [hl, div_le_one hD]; linarith
  have hmx : x ∈ Ioc (0 : ℝ) 1 := ⟨hx, by linarith⟩
  have hmy : x' + c ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, h1⟩
  have e1 : (1 - l) * x + l * (x' + c) = x + c := by
    rw [hl]; field_simp; ring
  have e2 : l * x + (1 - l) * (x' + c) = x' := by
    rw [hl]; field_simp; ring
  have c1 := Scalar.eta_convexOn_Ioc.2 hmx hmy (by linarith : (0 : ℝ) ≤ 1 - l) hl0 (by ring)
  have c2 := Scalar.eta_convexOn_Ioc.2 hmx hmy hl0 (by linarith : (0 : ℝ) ≤ 1 - l) (by ring)
  simp only [smul_eq_mul] at c1 c2
  rw [e1] at c1
  rw [e2] at c2
  linarith

/-- Lower bound for the parent gain `eta E - eta (E + C)` from the box corner `(E_hi, C_lo)`. -/
theorem parent_gain_lower {E Eu C Clo : ℝ} (hE : 0 < E) (hEu : E ≤ Eu) (hClo : 0 ≤ Clo)
    (hC : Clo ≤ C) (hphys : E + C ≤ 1) (hu : Eu + Clo ≤ 1) :
    eta Eu - eta (Eu + Clo) ≤ eta E - eta (E + C) := by
  have h1 := eta_increment_mono hE hEu hClo hu
  have h2 : eta (E + C) ≤ eta (E + Clo) :=
    eta_antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, hphys⟩ (by linarith)
  linarith

/-- Lower bracket for `eta` at `h`: if `h ≤ H xc` with `xc ≤ 1/2`, then `(1 - 2 xc) J xc ≤ eta h`. -/
theorem eta_ge_bracket {h xc : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (hxc : 0 < xc) (hxc' : xc ≤ 1 / 2)
    (hH : h ≤ H xc) : (1 - 2 * xc) * J xc ≤ eta h := by
  have hb := P_ge_bracket (p := 1 - h) (by linarith) (by linarith) hxc hxc' (by linarith)
  have e : Scalar.P (1 - h) = eta h := by
    unfold Scalar.P
    congr 1
    ring
  rw [e] at hb
  exact hb

/-- Upper bracket for `eta` at `h`: if `H xa ≤ h` with `0 < xa ≤ 1/2`, then `eta h ≤ (1 - 2 xa) J xa`. -/
theorem eta_le_bracket {h xa : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (hxa : 0 < xa) (hxa' : xa ≤ 1 / 2)
    (hH : H xa ≤ h) : eta h ≤ (1 - 2 * xa) * J xa := by
  have hb := P_le_bracket (p := 1 - h) (by linarith) (by linarith) hxa hxa' (by linarith)
  have e : Scalar.P (1 - h) = eta h := by
    unfold Scalar.P
    congr 1
    ring
  rw [e] at hb
  exact hb

/-- Radial profile bound from a lower contact bracket: `q H v ≤ E (1 - 2 v)` gives `F q E ≤ q J v`. -/
theorem F_le_of_contact {q E v : ℝ} (hq : 0 < q) (hE : 0 < E) (hv : 0 < v) (hv' : v ≤ 1 / 2)
    (hc : q * H v ≤ E * (1 - 2 * v)) : F q E ≤ q * J v := by
  have hvc : v ≤ radialContact q E := (le_radialContact_iff hq hE hv.le hv').2 hc
  have hJ := J_antitone hv (radialContact_lt_half hq hE).le hvc
  simp only [F, hq.ne', if_false]
  exact mul_le_mul_of_nonneg_left hJ hq.le

/-- The parent capacity is below `q^2`. -/
theorem capacity_le_sq {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : 1 - H ((1 - q) / 2) ≤ q ^ 2 := by
  have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
  nlinarith

/-- The parent capacity increases with the bias. -/
theorem capacity_mono {q q' : ℝ} (hq : q ≤ q') (hq' : q' ≤ 1) (hq0 : 0 ≤ q) :
    1 - H ((1 - q) / 2) ≤ 1 - H ((1 - q') / 2) := by
  have := H_mono_left (x := (1 - q') / 2) (y := (1 - q) / 2) (by linarith) (by linarith)
    (by linarith)
  linarith

/-- Pointwise comparison at the parent `m = (1 - q)/2`. -/
theorem psi_lt_phi_of_gain {q E G : ℝ} (hq : 0 < q)
    (hG : G ≤ eta E - eta (E + (1 - H ((1 - q) / 2)))) (hF : F q E < G) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  unfold phi psi
  rw [show |1 - 2 * ((1 - q) / 2)| = q by
      rw [show 1 - 2 * ((1 - q) / 2) = q by ring, abs_of_pos hq],
    show E + 1 - H ((1 - q) / 2) = E + (1 - H ((1 - q) / 2)) by ring]
  linarith

/-! ## Certificates and the core comparison -/

/-- Untrusted per-box certificate: log certificates at `(1 - q_-)/2`, the two `eta` brackets
`xc`, `xa` and the contact bracket `v`. -/
structure ParentCert where
  pM : PtCert
  xc : ℚ
  pxc : PtCert
  xa : ℚ
  pxa : PtCert
  v : ℚ
  pv : PtCert
  deriving Repr, DecidableEq

/-- Certified lower bound of the parent capacity `C(q_-)`. -/
def capLo (q0 : ℚ) (c : ParentCert) : ℚ := 1 - Hhi ((1 - q0) / 2) c.pM

/-- The certified margin (computed, never stored). -/
def pmargin (q1 : ℚ) (c : ParentCert) : ℚ :=
  (1 - 2 * c.xc) * Jlo c.xc c.pxc - (1 - 2 * c.xa) * Jhi c.xa c.pxa - q1 * Jhi c.v c.pv

/-- Core comparison shared by both coordinate systems; `Est` is an upper bound of `E`. -/
def checkCore (q0 q1 Est : ℚ) (c : ParentCert) : Bool :=
  checkPt ((1 - q0) / 2) c.pM && checkPt c.xc c.pxc && checkPt c.xa c.pxa &&
  checkPt c.v c.pv &&
  decide (0 ≤ capLo q0 c) && decide (Est + capLo q0 c ≤ 1) &&
  decide (2 * c.xc ≤ 1 ∧ Est ≤ Hlo c.xc c.pxc) &&
  decide (2 * c.xa ≤ 1 ∧ Hhi c.xa c.pxa ≤ Est + capLo q0 c) &&
  decide (2 * c.v ≤ 1) &&
  decide (0 < pmargin q1 c)

theorem checkCore_v {q0 q1 Est : ℚ} {c : ParentCert} (h : checkCore q0 q1 Est c = true) :
    checkPt c.v c.pv = true ∧ 2 * c.v ≤ 1 := by
  unfold checkCore at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.2, h.1.2⟩

/-- Soundness of the core: for any point of the box (described by its consequences) the parent
dominates strictly. -/
theorem checkCore_sound {q0 q1 Est : ℚ} {c : ParentCert} (h : checkCore q0 q1 Est c = true)
    {q E : ℝ} (hq0 : 0 < (q0 : ℝ)) (hqq0 : (q0 : ℝ) ≤ q) (hqq1 : q ≤ q1) (hq1 : (q1 : ℝ) < 1)
    (hE : 0 < E) (hEst : E ≤ Est) (hphys : E + (1 - H ((1 - q) / 2)) ≤ 1)
    (hcontact : q * H (c.v : ℝ) ≤ E * (1 - 2 * (c.v : ℝ))) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  unfold checkCore at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpM, hpxc⟩, hpxa⟩, hpv⟩, hcap0⟩, hEC⟩, ⟨hxc1, hxc2⟩⟩, ⟨hxa1, hxa2⟩⟩, hv1⟩,
    hmar⟩ := h
  obtain ⟨hM0, hM1, _, hMu, _, _⟩ := checkPt_bounds hpM
  obtain ⟨hxc0, _, hxcHl, _, hxcJl, _⟩ := checkPt_bounds hpxc
  obtain ⟨hxa0, _, _, hxaHu, _, hxaJu⟩ := checkPt_bounds hpxa
  obtain ⟨hv0, _, _, _, _, hvJu⟩ := checkPt_bounds hpv
  have hq : 0 < q := hq0.trans_le hqq0
  -- capacity
  have ecap : ((capLo q0 c : ℚ) : ℝ) = 1 - (Hhi ((1 - q0) / 2) c.pM : ℝ) := by
    unfold capLo; push_cast; ring
  have rcap0 : (0 : ℝ) ≤ (capLo q0 c : ℝ) := by exact_mod_cast hcap0
  have hM : (((1 - q0) / 2 : ℚ) : ℝ) = (1 - (q0 : ℝ)) / 2 := by push_cast; ring
  have hHq : H ((1 - q) / 2) ≤ H ((1 - (q0 : ℝ)) / 2) :=
    H_mono_left (by linarith) (by linarith) (by linarith)
  rw [hM] at hMu
  have hcapLe : (capLo q0 c : ℝ) ≤ 1 - H ((1 - q) / 2) := by rw [ecap]; linarith
  have rEC : (Est : ℝ) + (capLo q0 c : ℝ) ≤ 1 := by exact_mod_cast hEC
  have hgain := parent_gain_lower hE hEst rcap0 hcapLe hphys rEC
  -- eta brackets
  have rEst0 : (0 : ℝ) < (Est : ℝ) := hE.trans_le hEst
  have rxc0 : (0 : ℝ) < (c.xc : ℝ) := by exact_mod_cast hxc0
  have rxc1 : 2 * (c.xc : ℝ) ≤ 1 := by exact_mod_cast hxc1
  have rxc2 : (Est : ℝ) ≤ (Hlo c.xc c.pxc : ℝ) := by exact_mod_cast hxc2
  have hetaLo : (1 - 2 * (c.xc : ℝ)) * J (c.xc : ℝ) ≤ eta (Est : ℝ) :=
    eta_ge_bracket rEst0 (by linarith) rxc0 (by linarith) (rxc2.trans hxcHl)
  have rxa0 : (0 : ℝ) < (c.xa : ℝ) := by exact_mod_cast hxa0
  have rxa1 : 2 * (c.xa : ℝ) ≤ 1 := by exact_mod_cast hxa1
  have rxa2 : (Hhi c.xa c.pxa : ℝ) ≤ (Est : ℝ) + (capLo q0 c : ℝ) := by exact_mod_cast hxa2
  have hetaHi : eta ((Est : ℝ) + (capLo q0 c : ℝ)) ≤ (1 - 2 * (c.xa : ℝ)) * J (c.xa : ℝ) :=
    eta_le_bracket (by linarith) rEC rxa0 (by linarith) (hxaHu.trans rxa2)
  have hJxc : (1 - 2 * (c.xc : ℝ)) * (Jlo c.xc c.pxc : ℝ) ≤ (1 - 2 * (c.xc : ℝ)) * J (c.xc : ℝ) :=
    mul_le_mul_of_nonneg_left hxcJl (by linarith)
  have hJxa : (1 - 2 * (c.xa : ℝ)) * J (c.xa : ℝ) ≤ (1 - 2 * (c.xa : ℝ)) * (Jhi c.xa c.pxa : ℝ) :=
    mul_le_mul_of_nonneg_left hxaJu (by linarith)
  -- radial profile
  have rv0 : (0 : ℝ) < (c.v : ℝ) := by exact_mod_cast hv0
  have rv1 : 2 * (c.v : ℝ) ≤ 1 := by exact_mod_cast hv1
  have hF := F_le_of_contact hq hE rv0 (by linarith) hcontact
  have hJv0 : 0 ≤ J (c.v : ℝ) := J_nonneg rv0 (by linarith)
  have hF2 : q * J (c.v : ℝ) ≤ (q1 : ℝ) * (Jhi c.v c.pv : ℝ) :=
    (mul_le_mul_of_nonneg_right hqq1 hJv0).trans
      (mul_le_mul_of_nonneg_left hvJu (by linarith))
  -- margin
  have rmar : (0 : ℝ) < (pmargin q1 c : ℝ) := by exact_mod_cast hmar
  have emar : (pmargin q1 c : ℝ) = (1 - 2 * (c.xc : ℝ)) * (Jlo c.xc c.pxc : ℝ) -
      (1 - 2 * (c.xa : ℝ)) * (Jhi c.xa c.pxa : ℝ) - (q1 : ℝ) * (Jhi c.v c.pv : ℝ) := by
    unfold pmargin; push_cast; ring
  rw [emar] at rmar
  apply psi_lt_phi_of_gain hq hgain
  linarith

/-! ## `(q, x)` boxes (PARENT8, PARENT16) -/

/-- A rational box in `(q, x)`, `x = q / E`. -/
structure QXBox where
  q0 : ℚ
  q1 : ℚ
  x0 : ℚ
  x1 : ℚ
  deriving Repr, DecidableEq

/-- Strict parent dominance on every `(q, E)` whose `(q, q/E)` lies in the box. -/
def SemQX (B : QXBox) : Prop :=
  ∀ q E : ℝ, 0 < E → (B.q0 : ℝ) ≤ q → q ≤ B.q1 → (B.x0 : ℝ) * E ≤ q → q ≤ (B.x1 : ℝ) * E →
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E

def checkQX (B : QXBox) (c : ParentCert) : Bool :=
  decide (0 < B.q0 ∧ B.q0 ≤ B.q1 ∧ B.q1 < 1 ∧ 0 < B.x0 ∧ B.x0 ≤ B.x1 ∧
    B.q1 / B.x0 + B.q1 ^ 2 ≤ 1) &&
  checkCore B.q0 B.q1 (B.q1 / B.x0) c &&
  decide (B.x1 * Hhi c.v c.pv ≤ 1 - 2 * c.v)

theorem checkQX_sound {B : QXBox} {c : ParentCert} (h : checkQX B c = true) : SemQX B := by
  intro q E hE hq0 hq1 hx0 hx1
  unfold checkQX at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hB1, hB2, hB3, hB4, hB5, hB6⟩, hcore⟩, hv⟩ := h
  have rB1 : (0 : ℝ) < B.q0 := by exact_mod_cast hB1
  have rB3 : (B.q1 : ℝ) < 1 := by exact_mod_cast hB3
  have rB4 : (0 : ℝ) < B.x0 := by exact_mod_cast hB4
  have rB6 : (B.q1 : ℝ) / B.x0 + (B.q1 : ℝ) ^ 2 ≤ 1 := by exact_mod_cast hB6
  have hq : 0 < q := rB1.trans_le hq0
  have hEst : E ≤ ((B.q1 / B.x0 : ℚ) : ℝ) := by
    push_cast
    rw [le_div_iff₀ rB4]
    nlinarith
  have hcap := capacity_le_sq hq (by linarith)
  have hsq : q ^ 2 ≤ (B.q1 : ℝ) ^ 2 := by nlinarith
  have hphys : E + (1 - H ((1 - q) / 2)) ≤ 1 := by
    have : E ≤ (B.q1 : ℝ) / B.x0 := by simpa using hEst
    linarith
  obtain ⟨hv0, hv1', _, hvHu, _, _⟩ := checkPt_bounds (checkCore_v hcore).1
  have rv : (B.x1 : ℝ) * (Hhi c.v c.pv : ℝ) ≤ 1 - 2 * (c.v : ℝ) := by exact_mod_cast hv
  have rv0 : (0 : ℝ) < (c.v : ℝ) := by exact_mod_cast hv0
  have rv1 : (c.v : ℝ) < 1 := by exact_mod_cast hv1'
  have hHv : 0 ≤ H (c.v : ℝ) := H_nonneg rv0.le rv1.le
  have hcontact : q * H (c.v : ℝ) ≤ E * (1 - 2 * (c.v : ℝ)) := by
    have h1 : q * H (c.v : ℝ) ≤ ((B.x1 : ℝ) * E) * H (c.v : ℝ) :=
      mul_le_mul_of_nonneg_right hx1 hHv
    have h2 : ((B.x1 : ℝ) * E) * H (c.v : ℝ) ≤ ((B.x1 : ℝ) * E) * (Hhi c.v c.pv : ℝ) :=
      mul_le_mul_of_nonneg_left hvHu (by nlinarith)
    have h3 : ((B.x1 : ℝ) * E) * (Hhi c.v c.pv : ℝ) ≤ E * (1 - 2 * (c.v : ℝ)) := by
      have := mul_le_mul_of_nonneg_left rv hE.le
      linarith
    linarith
  exact checkCore_sound hcore rB1 hq0 hq1 rB3 hE hEst hphys hcontact

/-! ## `(q, E)` boxes (HIGH_Q_PARENT) -/

/-- A rational box in `(q, E)`. -/
structure QEBox where
  q0 : ℚ
  q1 : ℚ
  e0 : ℚ
  e1 : ℚ
  deriving Repr, DecidableEq

def SemQE (B : QEBox) : Prop :=
  ∀ q E : ℝ, (B.q0 : ℝ) ≤ q → q ≤ B.q1 → (B.e0 : ℝ) ≤ E → E ≤ B.e1 →
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E

def checkQE (B : QEBox) (c : ParentCert) : Bool :=
  decide (0 < B.q0 ∧ B.q0 ≤ B.q1 ∧ B.q1 < 1 ∧ 0 < B.e0 ∧ B.e0 ≤ B.e1 ∧
    B.e1 + B.q1 ^ 2 ≤ 1) &&
  checkCore B.q0 B.q1 B.e1 c &&
  decide (B.q1 * Hhi c.v c.pv ≤ B.e0 * (1 - 2 * c.v))

theorem checkQE_sound {B : QEBox} {c : ParentCert} (h : checkQE B c = true) : SemQE B := by
  intro q E hq0 hq1 he0 he1
  unfold checkQE at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hB1, hB2, hB3, hB4, hB5, hB6⟩, hcore⟩, hv⟩ := h
  have rB1 : (0 : ℝ) < B.q0 := by exact_mod_cast hB1
  have rB3 : (B.q1 : ℝ) < 1 := by exact_mod_cast hB3
  have rB4 : (0 : ℝ) < B.e0 := by exact_mod_cast hB4
  have rB6 : (B.e1 : ℝ) + (B.q1 : ℝ) ^ 2 ≤ 1 := by exact_mod_cast hB6
  have hq : 0 < q := rB1.trans_le hq0
  have hE : 0 < E := rB4.trans_le he0
  have hcap := capacity_le_sq hq (by linarith)
  have hsq : q ^ 2 ≤ (B.q1 : ℝ) ^ 2 := by nlinarith
  have hphys : E + (1 - H ((1 - q) / 2)) ≤ 1 := by linarith
  obtain ⟨hv0, hv1', _, hvHu, _, _⟩ := checkPt_bounds (checkCore_v hcore).1
  have rv : (B.q1 : ℝ) * (Hhi c.v c.pv : ℝ) ≤ (B.e0 : ℝ) * (1 - 2 * (c.v : ℝ)) := by
    exact_mod_cast hv
  have rv0 : (0 : ℝ) < (c.v : ℝ) := by exact_mod_cast hv0
  have rv1 : (c.v : ℝ) < 1 := by exact_mod_cast hv1'
  have hv12 : 2 * (c.v : ℝ) ≤ 1 := by exact_mod_cast (checkCore_v hcore).2
  have hHv : 0 ≤ H (c.v : ℝ) := H_nonneg rv0.le rv1.le
  have hcontact : q * H (c.v : ℝ) ≤ E * (1 - 2 * (c.v : ℝ)) := by
    have h1 : q * H (c.v : ℝ) ≤ (B.q1 : ℝ) * (Hhi c.v c.pv : ℝ) :=
      mul_le_mul hq1 hvHu hHv (by linarith)
    have h2 : (B.e0 : ℝ) * (1 - 2 * (c.v : ℝ)) ≤ E * (1 - 2 * (c.v : ℝ)) :=
      mul_le_mul_of_nonneg_right he0 (by linarith)
    linarith
  exact checkCore_sound hcore rB1 hq0 hq1 rB3 hE he1 hphys hcontact

/-! ## Binary partition trees of certified boxes -/

/-- A binary partition tree: `node ax l r` halves axis `ax` (`l` lower half, `r` upper half). -/
inductive CTree (α : Type) where
  | leaf (c : α)
  | node (axis : ℕ) (l r : CTree α)
  deriving Repr

/-- Leaf paths (digit `2 ax` for the lower half, `2 ax + 1` for the upper half), left-first. -/
def CTree.paths {α : Type} : CTree α → List (List ℕ)
  | .leaf _ => [[]]
  | .node ax l r => (l.paths.map fun p => 2 * ax :: p) ++ (r.paths.map fun p => (2 * ax + 1) :: p)

def QXBox.lower (B : QXBox) : ℕ → QXBox
  | 0 => { B with q1 := (B.q0 + B.q1) / 2 }
  | _ => { B with x1 := (B.x0 + B.x1) / 2 }

def QXBox.upper (B : QXBox) : ℕ → QXBox
  | 0 => { B with q0 := (B.q0 + B.q1) / 2 }
  | _ => { B with x0 := (B.x0 + B.x1) / 2 }

def checkTreeQX : QXBox → CTree ParentCert → Bool
  | B, .leaf c => checkQX B c
  | B, .node ax l r => decide (ax ≤ 1) && checkTreeQX (B.lower ax) l && checkTreeQX (B.upper ax) r

theorem semQX_of_halves {B : QXBox} {ax : ℕ} (hax : ax ≤ 1) (hl : SemQX (B.lower ax))
    (hr : SemQX (B.upper ax)) : SemQX B := by
  intro q E hE hq0 hq1 hx0 hx1
  obtain rfl | rfl : ax = 0 ∨ ax = 1 := by omega
  · by_cases hm : q ≤ (((B.q0 + B.q1) / 2 : ℚ) : ℝ)
    · exact hl q E hE hq0 hm hx0 hx1
    · exact hr q E hE (le_of_not_ge hm) hq1 hx0 hx1
  · by_cases hm : q ≤ (((B.x0 + B.x1) / 2 : ℚ) : ℝ) * E
    · exact hl q E hE hq0 hq1 hx0 hm
    · exact hr q E hE hq0 hq1 (le_of_not_ge hm) hx1

theorem checkTreeQX_sound : ∀ (T : CTree ParentCert) (B : QXBox), checkTreeQX B T = true → SemQX B
  | .leaf c, B, h => checkQX_sound h
  | .node ax l r, B, h => by
    unfold checkTreeQX at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact semQX_of_halves h.1.1 (checkTreeQX_sound l _ h.1.2) (checkTreeQX_sound r _ h.2)

def QEBox.lower (B : QEBox) : ℕ → QEBox
  | 0 => { B with q1 := (B.q0 + B.q1) / 2 }
  | _ => { B with e1 := (B.e0 + B.e1) / 2 }

def QEBox.upper (B : QEBox) : ℕ → QEBox
  | 0 => { B with q0 := (B.q0 + B.q1) / 2 }
  | _ => { B with e0 := (B.e0 + B.e1) / 2 }

def checkTreeQE : QEBox → CTree ParentCert → Bool
  | B, .leaf c => checkQE B c
  | B, .node ax l r => decide (ax ≤ 1) && checkTreeQE (B.lower ax) l && checkTreeQE (B.upper ax) r

theorem semQE_of_halves {B : QEBox} {ax : ℕ} (hax : ax ≤ 1) (hl : SemQE (B.lower ax))
    (hr : SemQE (B.upper ax)) : SemQE B := by
  intro q E hq0 hq1 he0 he1
  obtain rfl | rfl : ax = 0 ∨ ax = 1 := by omega
  · by_cases hm : q ≤ (((B.q0 + B.q1) / 2 : ℚ) : ℝ)
    · exact hl q E hq0 hm he0 he1
    · exact hr q E (le_of_not_ge hm) hq1 he0 he1
  · by_cases hm : E ≤ (((B.e0 + B.e1) / 2 : ℚ) : ℝ)
    · exact hl q E hq0 hq1 he0 hm
    · exact hr q E hq0 hq1 (le_of_not_ge hm) he1

theorem checkTreeQE_sound : ∀ (T : CTree ParentCert) (B : QEBox), checkTreeQE B T = true → SemQE B
  | .leaf c, B, h => checkQE_sound h
  | .node ax l r, B, h => by
    unfold checkTreeQE at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact semQE_of_halves h.1.1 (checkTreeQE_sound l _ h.1.2) (checkTreeQE_sound r _ h.2)

end CKLaneN4

end


