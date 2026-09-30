-- Prove2me | Definitions.Def_CK_CKLaneN1b_Points
-- name    : CK_CKLaneN1b_Points
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:51:57.412504+00:00
-- url     : https://prove2.me/theorems/da41bfe3-d008-44e1-b51b-7873aaadd216
-- title:
--   Courtade–Kumar proof module `CKLaneN1b.Points` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1b.Points` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1b.Points` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1b.Points (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1b/Points.lean)

import Definitions.Def_CK_CKLaneN1b_Analytic

-- ===== source module CKLaneN1b.Points =====
section

/-!
# Lane N1b: rational log points, boxes, the semantic statement, and contact planes

* `Pt`: a rational point `q ∈ (0,1)` with stored bounds on `log q` and `log (1-q)`, verified
  against `CKLaneE.FP` (fixed-point atanh series) by `Pt.ok`; derived `H`/`J` enclosures.
* `Box`, `InBox`, `Sem`: the archived `(a, b, t)` box with `E = 11/200 + t (C0 - 11/200)`,
  `C0 = (H a + H b)/2`, and the law-level psi-candidate Bellman statement on its exact image,
  restricted to `b - a ≥ 1/50` (the archived relevance condition).
* `Plane`: a rational contact `(x, y)`; `Plane.ok_sound` gives the averaged global supporting
  plane `lam (b - a) - Ahi e - Bhi f ≤ cost` with checked rational coefficients.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN1b

open GeneralCK CKLaneE

/-! ## Division by `log 2` -/

def dLo (N : ℚ) : ℚ := if 0 ≤ N then N / FP.LqHi else N / FP.LqLo
def dHi (N : ℚ) : ℚ := if 0 ≤ N then N / FP.LqLo else N / FP.LqHi

theorem LqHi_pos : (0 : ℝ) < ((FP.LqHi : ℚ) : ℝ) :=
  FP.LqLo_pos.trans_le (FP.log_two_mem.1.trans FP.log_two_mem.2)

theorem dLo_le {N0 : ℚ} {N : ℝ} (h : (N0 : ℝ) ≤ N) : ((dLo N0 : ℚ) : ℝ) ≤ N / Real.log 2 := by
  have hL := FP.log_two_mem
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 := FP.LqLo_pos
  have hL1 := LqHi_pos
  unfold dLo
  split_ifs with h0
  · push_cast
    have h0' : (0 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast h0
    rw [div_le_div_iff₀ hL1 hl2]
    nlinarith
  · push_cast
    have h0' : (N0 : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h0)
    rw [div_le_div_iff₀ hL0 hl2]
    nlinarith

theorem le_dHi {N1 : ℚ} {N : ℝ} (h : N ≤ (N1 : ℝ)) : N / Real.log 2 ≤ ((dHi N1 : ℚ) : ℝ) := by
  have hL := FP.log_two_mem
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 := FP.LqLo_pos
  have hL1 := LqHi_pos
  unfold dHi
  split_ifs with h0
  · push_cast
    have h0' : (0 : ℝ) ≤ (N1 : ℝ) := by exact_mod_cast h0
    rw [div_le_div_iff₀ hl2 hL0]
    nlinarith
  · push_cast
    have h0' : (N1 : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h0)
    rw [div_le_div_iff₀ hl2 hL1]
    nlinarith

/-! ## Rational log points -/

/-- A rational point with stored bounds on `log q` (`l0 ≤ · ≤ l1`) and `log (1-q)`
(`m0 ≤ · ≤ m1`). -/
structure Pt where
  q : ℚ
  l0 : ℚ
  l1 : ℚ
  m0 : ℚ
  m1 : ℚ
  deriving Repr, DecidableEq

namespace Pt

/-- The stored bounds are implied by the kernel-checkable `CKLaneE.FP` enclosures. -/
def ok (p : Pt) : Bool :=
  FP.ptOk p.q && decide (p.l0 ≤ FP.lLo p.q ∧ FP.lHi p.q ≤ p.l1 ∧
    p.m0 ≤ FP.l1Lo p.q ∧ FP.l1Hi p.q ≤ p.m1)

def Hlo (p : Pt) : ℚ := dLo (-(p.q * p.l1) - (1 - p.q) * p.m1)
def Hhi (p : Pt) : ℚ := dHi (-(p.q * p.l0) - (1 - p.q) * p.m0)
def Jlo (p : Pt) : ℚ := dLo (p.m0 - p.l1)
def Jhi (p : Pt) : ℚ := dHi (p.m1 - p.l0)

theorem ok_logs {p : Pt} (h : p.ok = true) :
    0 < p.q ∧ p.q < 1 ∧ (p.l0 : ℝ) ≤ Real.log (p.q : ℝ) ∧ Real.log (p.q : ℝ) ≤ (p.l1 : ℝ) ∧
      (p.m0 : ℝ) ≤ Real.log (1 - (p.q : ℝ)) ∧ Real.log (1 - (p.q : ℝ)) ≤ (p.m1 : ℝ) := by
  unfold ok at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hp, c1, c2, c3, c4⟩ := h
  have hq := FP.ptOk_pos hp
  obtain ⟨f1, f2, f3, f4⟩ := FP.ptOk_sound hp
  have r1 : (p.l0 : ℝ) ≤ ((FP.lLo p.q : ℚ) : ℝ) := by exact_mod_cast c1
  have r2 : ((FP.lHi p.q : ℚ) : ℝ) ≤ (p.l1 : ℝ) := by exact_mod_cast c2
  have r3 : (p.m0 : ℝ) ≤ ((FP.l1Lo p.q : ℚ) : ℝ) := by exact_mod_cast c3
  have r4 : ((FP.l1Hi p.q : ℚ) : ℝ) ≤ (p.m1 : ℝ) := by exact_mod_cast c4
  exact ⟨hq.1, hq.2, r1.trans f1, f2.trans r2, r3.trans f3, f4.trans r4⟩

theorem H_bounds {p : Pt} (h : p.ok = true) :
    ((p.Hlo : ℚ) : ℝ) ≤ H (p.q : ℝ) ∧ H (p.q : ℝ) ≤ ((p.Hhi : ℚ) : ℝ) := by
  obtain ⟨hq0, hq1, a1, a2, a3, a4⟩ := ok_logs h
  have hq0' : (0 : ℝ) < (p.q : ℝ) := by exact_mod_cast hq0
  have hq1' : (p.q : ℝ) < 1 := by exact_mod_cast hq1
  rw [CKLaneE.H_eq_logs]
  constructor
  · unfold Hlo
    apply dLo_le
    push_cast
    have m1 := mul_le_mul_of_nonneg_left a2 hq0'.le
    have m2 := mul_le_mul_of_nonneg_left a4 (by linarith : (0 : ℝ) ≤ 1 - (p.q : ℝ))
    linarith
  · unfold Hhi
    apply le_dHi
    push_cast
    have m1 := mul_le_mul_of_nonneg_left a1 hq0'.le
    have m2 := mul_le_mul_of_nonneg_left a3 (by linarith : (0 : ℝ) ≤ 1 - (p.q : ℝ))
    linarith

theorem J_bounds {p : Pt} (h : p.ok = true) :
    ((p.Jlo : ℚ) : ℝ) ≤ J (p.q : ℝ) ∧ J (p.q : ℝ) ≤ ((p.Jhi : ℚ) : ℝ) := by
  obtain ⟨hq0, hq1, a1, a2, a3, a4⟩ := ok_logs h
  have hq0' : (0 : ℝ) < (p.q : ℝ) := by exact_mod_cast hq0
  have hq1' : (p.q : ℝ) < 1 := by exact_mod_cast hq1
  have hJ : J (p.q : ℝ) = (Real.log (1 - (p.q : ℝ)) - Real.log (p.q : ℝ)) / Real.log 2 := by
    unfold J
    rw [Real.log_div (by linarith) hq0'.ne']
  rw [hJ]
  constructor
  · unfold Jlo; apply dLo_le; push_cast; linarith
  · unfold Jhi; apply le_dHi; push_cast; linarith

/-- Upper bound of `log ((1-q)/q)` (for slope anchors). -/
theorem lam_le {p : Pt} (h : p.ok = true) :
    Real.log ((1 - (p.q : ℝ)) / (p.q : ℝ)) ≤ ((p.m1 - p.l0 : ℚ) : ℝ) := by
  obtain ⟨hq0, hq1, a1, a2, a3, a4⟩ := ok_logs h
  have hq0' : (0 : ℝ) < (p.q : ℝ) := by exact_mod_cast hq0
  have hq1' : (p.q : ℝ) < 1 := by exact_mod_cast hq1
  rw [Real.log_div (by linarith) hq0'.ne']
  push_cast
  linarith

end Pt

/-! ## Boxes and the semantic statement -/

/-- The archived entropy floor `11/200`. -/
def E0 : ℚ := 11 / 200

/-- The archived minimum mean difference `1/50`. -/
def DMIN : ℚ := 1 / 50

/-- A box in archived `(a, b, t)` coordinates. -/
structure Box where
  a0 : ℚ
  a1 : ℚ
  b0 : ℚ
  b1 : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving Repr, DecidableEq

/-- `(a, b, E)` lies in the exact image of the box: `E = 11/200 + t (C0 - 11/200)`,
`t ∈ [t0, t1]`, `C0 = (H a + H b)/2`. -/
def InBox (B : Box) (a b E : ℝ) : Prop :=
  (B.a0 : ℝ) ≤ a ∧ a ≤ (B.a1 : ℝ) ∧ (B.b0 : ℝ) ≤ b ∧ b ≤ (B.b1 : ℝ) ∧
    (E0 : ℝ) + (B.t0 : ℝ) * ((H a + H b) / 2 - (E0 : ℝ)) ≤ E ∧
    E ≤ (E0 : ℝ) + (B.t1 : ℝ) * ((H a + H b) / 2 - (E0 : ℝ))

/-- The law-level psi-candidate Bellman statement on the exact image of the box, for mean
difference at least `1/50`. -/
def Sem (B : Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InBox B μ.a μ.b μ.meanEntropy →
    (DMIN : ℝ) ≤ μ.b - μ.a → candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

/-- Boxes whose largest mean difference is below `1/50` are irrelevant: `Sem` holds vacuously. -/
theorem sem_of_outside {B : Box} (h : B.b1 - B.a0 < DMIN) : Sem B := by
  intro k μ hin hd
  obtain ⟨h1, _, _, h4, _, _⟩ := hin
  have h' : ((B.b1 - B.a0 : ℚ) : ℝ) < (DMIN : ℝ) := by exact_mod_cast h
  push_cast at h'
  exfalso
  linarith

theorem sem_splitA {B : Box} {m : ℚ} (hl : Sem { B with a1 := m })
    (hr : Sem { B with a0 := m }) : Sem B := by
  intro k μ hbox hd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbox
  rcases le_total μ.a (m : ℝ) with h | h
  · exact hl k μ ⟨h1, h, h3, h4, h5, h6⟩ hd
  · exact hr k μ ⟨h, h2, h3, h4, h5, h6⟩ hd

theorem sem_splitB {B : Box} {m : ℚ} (hl : Sem { B with b1 := m })
    (hr : Sem { B with b0 := m }) : Sem B := by
  intro k μ hbox hd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbox
  rcases le_total μ.b (m : ℝ) with h | h
  · exact hl k μ ⟨h1, h2, h3, h, h5, h6⟩ hd
  · exact hr k μ ⟨h1, h2, h, h4, h5, h6⟩ hd

theorem sem_splitT {B : Box} {m : ℚ} (hl : Sem { B with t1 := m })
    (hr : Sem { B with t0 := m }) : Sem B := by
  intro k μ hbox hd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbox
  rcases le_total μ.meanEntropy
      ((E0 : ℝ) + (m : ℝ) * ((H μ.a + H μ.b) / 2 - (E0 : ℝ))) with h | h
  · exact hl k μ ⟨h1, h2, h3, h4, h5, h⟩ hd
  · exact hr k μ ⟨h1, h2, h3, h4, h, h6⟩ hd

/-! ## Contact planes with checked rational coefficients -/

/-- A rational contact `(x, y)` of the manuscript's global supporting plane. -/
structure Plane where
  x : Pt
  y : Pt
  deriving Repr, DecidableEq

namespace Plane

def dd (P : Plane) : ℚ := P.y.q - P.x.q
def r1 (P : Plane) : ℚ := P.dd ^ 2 / (2 * P.x.q * P.y.q)
def r2 (P : Plane) : ℚ := P.dd ^ 2 / (2 * (1 - P.x.q) * (1 - P.y.q))
/-- Interval of `capDet x y = log x · log (1-y) - log y · log (1-x)` (all four logs negative). -/
def detlo (P : Plane) : ℚ := P.x.l1 * P.y.m1 - P.y.l0 * P.x.m0
def dethi (P : Plane) : ℚ := P.x.l0 * P.y.m0 - P.y.l1 * P.x.m1
/-- Interval of the numerator of `capA x y = (r2 log y - r1 log (1-y)) / det`. -/
def nAlo (P : Plane) : ℚ := P.r2 * P.y.l0 - P.r1 * P.y.m1
def nAhi (P : Plane) : ℚ := P.r2 * P.y.l1 - P.r1 * P.y.m0
/-- Interval of the numerator of `capB x y = (r1 log (1-x) - r2 log x) / det`. -/
def nBlo (P : Plane) : ℚ := P.r1 * P.x.m0 - P.r2 * P.x.l1
def nBhi (P : Plane) : ℚ := P.r1 * P.x.m1 - P.r2 * P.x.l0
def Alo (P : Plane) : ℚ := P.nAlo / P.dethi
def Ahi (P : Plane) : ℚ := P.nAhi / P.detlo
def Blo (P : Plane) : ℚ := P.nBlo / P.dethi
def Bhi (P : Plane) : ℚ := P.nBhi / P.detlo
/-- Lower bound of the plane slope `(interiorCost x y + A H x + B H y)/(y - x)`. -/
def lam (P : Plane) : ℚ := (P.x.Jlo - P.y.Jhi) / 2 + (P.Alo * P.x.Hlo + P.Blo * P.y.Hlo) / P.dd

def ok (P : Plane) : Bool :=
  P.x.ok && P.y.ok &&
    decide (0 < P.x.q ∧ P.x.q < P.y.q ∧ P.y.q < 1 ∧ P.x.l1 < 0 ∧ P.x.m1 < 0 ∧ P.y.l1 < 0 ∧
      P.y.m1 < 0 ∧ 0 < P.detlo ∧ 0 < P.nAlo ∧ 0 < P.nBlo ∧ 0 ≤ P.x.Hlo ∧ 0 ≤ P.y.Hlo)

theorem neg_mul_bounds {u v u0 u1 v0 v1 : ℝ} (hu0 : u0 ≤ u) (hu1 : u ≤ u1) (hv0 : v0 ≤ v)
    (hv1 : v ≤ v1) (hu1n : u1 < 0) (hv1n : v1 < 0) : u1 * v1 ≤ u * v ∧ u * v ≤ u0 * v0 := by
  constructor <;> nlinarith

theorem ok_sound {P : Plane} (h : P.ok = true) {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a ≤ μ.b) :
    (P.lam : ℝ) * (μ.b - μ.a) - (P.Ahi : ℝ) * μ.e - (P.Bhi : ℝ) * μ.f ≤ μ.cost ∧
      (0 : ℝ) ≤ (P.Ahi : ℝ) ∧ (0 : ℝ) ≤ (P.Bhi : ℝ) := by
  unfold ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hx, hy⟩, s1, s2, s3, n1, n2, n3, n4, d1, d2, d3, h1, h2⟩ := h
  obtain ⟨_, _, lx0, lx1, mx0, mx1⟩ := Pt.ok_logs hx
  obtain ⟨_, _, ly0, ly1, my0, my1⟩ := Pt.ok_logs hy
  obtain ⟨hHx0, _⟩ := Pt.H_bounds hx
  obtain ⟨hHy0, _⟩ := Pt.H_bounds hy
  obtain ⟨hJx0, _⟩ := Pt.J_bounds hx
  obtain ⟨_, hJy1⟩ := Pt.J_bounds hy
  have rx0 : (0 : ℝ) < (P.x.q : ℝ) := by exact_mod_cast s1
  have rxy : (P.x.q : ℝ) < (P.y.q : ℝ) := by exact_mod_cast s2
  have ry1 : (P.y.q : ℝ) < 1 := by exact_mod_cast s3
  have rn1 : (P.x.l1 : ℝ) < 0 := by exact_mod_cast n1
  have rn2 : (P.x.m1 : ℝ) < 0 := by exact_mod_cast n2
  have rn3 : (P.y.l1 : ℝ) < 0 := by exact_mod_cast n3
  have rn4 : (P.y.m1 : ℝ) < 0 := by exact_mod_cast n4
  set x : ℝ := (P.x.q : ℝ) with hxdef
  set y : ℝ := (P.y.q : ℝ) with hydef
  -- determinant
  obtain ⟨p1, p2⟩ := neg_mul_bounds lx0 lx1 my0 my1 rn1 rn4
  obtain ⟨p3, p4⟩ := neg_mul_bounds ly0 ly1 mx0 mx1 rn3 rn2
  have hdet_eq : CKLaneM09.capDet x y = Real.log x * Real.log (1 - y) -
      Real.log y * Real.log (1 - x) := rfl
  have edetlo : ((P.detlo : ℚ) : ℝ) = (P.x.l1 : ℝ) * (P.y.m1 : ℝ) - (P.y.l0 : ℝ) * (P.x.m0 : ℝ) := by
    simp only [detlo]; push_cast; ring
  have edethi : ((P.dethi : ℚ) : ℝ) = (P.x.l0 : ℝ) * (P.y.m0 : ℝ) - (P.y.l1 : ℝ) * (P.x.m1 : ℝ) := by
    simp only [dethi]; push_cast; ring
  have rd1 : (0 : ℝ) < ((P.detlo : ℚ) : ℝ) := by exact_mod_cast d1
  have hdetL : ((P.detlo : ℚ) : ℝ) ≤ CKLaneM09.capDet x y := by
    rw [edetlo, hdet_eq]; linarith
  have hdetU : CKLaneM09.capDet x y ≤ ((P.dethi : ℚ) : ℝ) := by
    rw [edethi, hdet_eq]; linarith
  have hdet : 0 < CKLaneM09.capDet x y := rd1.trans_le hdetL
  -- numerators
  have hdd : ((P.dd : ℚ) : ℝ) = y - x := by simp only [dd]; push_cast; ring
  have er1 : ((P.r1 : ℚ) : ℝ) = (y - x) ^ 2 / (2 * x * y) := by
    simp only [r1, dd]; push_cast; ring
  have er2 : ((P.r2 : ℚ) : ℝ) = (y - x) ^ 2 / (2 * (1 - x) * (1 - y)) := by
    simp only [r2, dd]; push_cast; ring
  have hr1 : (0 : ℝ) ≤ ((P.r1 : ℚ) : ℝ) := by
    rw [er1]
    have : 0 < y := by linarith
    positivity
  have hr2 : (0 : ℝ) ≤ ((P.r2 : ℚ) : ℝ) := by
    rw [er2]
    have : (0 : ℝ) < 1 - x := by linarith
    have : (0 : ℝ) < 1 - y := by linarith
    positivity
  have hA_eq : CKLaneM09.capA x y = (((P.r2 : ℚ) : ℝ) * Real.log y -
      ((P.r1 : ℚ) : ℝ) * Real.log (1 - y)) / CKLaneM09.capDet x y := by
    rw [er1, er2]; unfold CKLaneM09.capA; ring
  have hB_eq : CKLaneM09.capB x y = (((P.r1 : ℚ) : ℝ) * Real.log (1 - x) -
      ((P.r2 : ℚ) : ℝ) * Real.log x) / CKLaneM09.capDet x y := by
    rw [er1, er2]; unfold CKLaneM09.capB; ring
  have enAlo : ((P.nAlo : ℚ) : ℝ) = ((P.r2 : ℚ) : ℝ) * (P.y.l0 : ℝ) - ((P.r1 : ℚ) : ℝ) * (P.y.m1 : ℝ) := by
    simp only [nAlo]; push_cast; ring
  have enAhi : ((P.nAhi : ℚ) : ℝ) = ((P.r2 : ℚ) : ℝ) * (P.y.l1 : ℝ) - ((P.r1 : ℚ) : ℝ) * (P.y.m0 : ℝ) := by
    simp only [nAhi]; push_cast; ring
  have enBlo : ((P.nBlo : ℚ) : ℝ) = ((P.r1 : ℚ) : ℝ) * (P.x.m0 : ℝ) - ((P.r2 : ℚ) : ℝ) * (P.x.l1 : ℝ) := by
    simp only [nBlo]; push_cast; ring
  have enBhi : ((P.nBhi : ℚ) : ℝ) = ((P.r1 : ℚ) : ℝ) * (P.x.m1 : ℝ) - ((P.r2 : ℚ) : ℝ) * (P.x.l0 : ℝ) := by
    simp only [nBhi]; push_cast; ring
  set nA : ℝ := ((P.r2 : ℚ) : ℝ) * Real.log y - ((P.r1 : ℚ) : ℝ) * Real.log (1 - y) with hnA
  set nB : ℝ := ((P.r1 : ℚ) : ℝ) * Real.log (1 - x) - ((P.r2 : ℚ) : ℝ) * Real.log x with hnB
  have hnAlo : ((P.nAlo : ℚ) : ℝ) ≤ nA := by
    rw [enAlo, hnA]
    have := mul_le_mul_of_nonneg_left ly0 hr2
    have := mul_le_mul_of_nonneg_left my1 hr1
    linarith
  have hnAhi : nA ≤ ((P.nAhi : ℚ) : ℝ) := by
    rw [enAhi, hnA]
    have := mul_le_mul_of_nonneg_left ly1 hr2
    have := mul_le_mul_of_nonneg_left my0 hr1
    linarith
  have hnBlo : ((P.nBlo : ℚ) : ℝ) ≤ nB := by
    rw [enBlo, hnB]
    have := mul_le_mul_of_nonneg_left mx0 hr1
    have := mul_le_mul_of_nonneg_left lx1 hr2
    linarith
  have hnBhi : nB ≤ ((P.nBhi : ℚ) : ℝ) := by
    rw [enBhi, hnB]
    have := mul_le_mul_of_nonneg_left mx1 hr1
    have := mul_le_mul_of_nonneg_left lx0 hr2
    linarith
  have rnA : (0 : ℝ) < ((P.nAlo : ℚ) : ℝ) := by exact_mod_cast d2
  have rnB : (0 : ℝ) < ((P.nBlo : ℚ) : ℝ) := by exact_mod_cast d3
  have hdethi : (0 : ℝ) < ((P.dethi : ℚ) : ℝ) := hdet.trans_le hdetU
  -- coefficient enclosures
  have eAlo : ((P.Alo : ℚ) : ℝ) = ((P.nAlo : ℚ) : ℝ) / ((P.dethi : ℚ) : ℝ) := by
    simp only [Alo]; push_cast; ring
  have eAhi : ((P.Ahi : ℚ) : ℝ) = ((P.nAhi : ℚ) : ℝ) / ((P.detlo : ℚ) : ℝ) := by
    simp only [Ahi]; push_cast; ring
  have eBlo : ((P.Blo : ℚ) : ℝ) = ((P.nBlo : ℚ) : ℝ) / ((P.dethi : ℚ) : ℝ) := by
    simp only [Blo]; push_cast; ring
  have eBhi : ((P.Bhi : ℚ) : ℝ) = ((P.nBhi : ℚ) : ℝ) / ((P.detlo : ℚ) : ℝ) := by
    simp only [Bhi]; push_cast; ring
  have hnA0 : 0 < nA := rnA.trans_le hnAlo
  have hnB0 : 0 < nB := rnB.trans_le hnBlo
  have hA_lo : ((P.Alo : ℚ) : ℝ) ≤ CKLaneM09.capA x y := by
    rw [eAlo, hA_eq]
    calc ((P.nAlo : ℚ) : ℝ) / ((P.dethi : ℚ) : ℝ) ≤ nA / ((P.dethi : ℚ) : ℝ) :=
          div_le_div_of_nonneg_right hnAlo hdethi.le
      _ ≤ nA / CKLaneM09.capDet x y := div_le_div_of_nonneg_left hnA0.le hdet hdetU
  have hA_hi : CKLaneM09.capA x y ≤ ((P.Ahi : ℚ) : ℝ) := by
    rw [eAhi, hA_eq]
    calc nA / CKLaneM09.capDet x y ≤ nA / ((P.detlo : ℚ) : ℝ) :=
          div_le_div_of_nonneg_left hnA0.le rd1 hdetL
      _ ≤ ((P.nAhi : ℚ) : ℝ) / ((P.detlo : ℚ) : ℝ) := div_le_div_of_nonneg_right hnAhi rd1.le
  have hB_lo : ((P.Blo : ℚ) : ℝ) ≤ CKLaneM09.capB x y := by
    rw [eBlo, hB_eq]
    calc ((P.nBlo : ℚ) : ℝ) / ((P.dethi : ℚ) : ℝ) ≤ nB / ((P.dethi : ℚ) : ℝ) :=
          div_le_div_of_nonneg_right hnBlo hdethi.le
      _ ≤ nB / CKLaneM09.capDet x y := div_le_div_of_nonneg_left hnB0.le hdet hdetU
  have hB_hi : CKLaneM09.capB x y ≤ ((P.Bhi : ℚ) : ℝ) := by
    rw [eBhi, hB_eq]
    calc nB / CKLaneM09.capDet x y ≤ nB / ((P.detlo : ℚ) : ℝ) :=
          div_le_div_of_nonneg_left hnB0.le rd1 hdetL
      _ ≤ ((P.nBhi : ℚ) : ℝ) / ((P.detlo : ℚ) : ℝ) := div_le_div_of_nonneg_right hnBhi rd1.le
  have hAlo0 : (0 : ℝ) < ((P.Alo : ℚ) : ℝ) := by rw [eAlo]; exact div_pos rnA hdethi
  have hBlo0 : (0 : ℝ) < ((P.Blo : ℚ) : ℝ) := by rw [eBlo]; exact div_pos rnB hdethi
  have hA0 : 0 < CKLaneM09.capA x y := hAlo0.trans_le hA_lo
  have hB0 : 0 < CKLaneM09.capB x y := hBlo0.trans_le hB_lo
  -- the plane
  have hpl := contact_plane_cost μ rx0 rxy ry1 hdet.ne' hA0 hB0
  set A := CKLaneM09.capA x y
  set B := CKLaneM09.capB x y
  have hIC : interiorCost x y = (y - x) * (J x - J y) / 2 := rfl
  have hyx : 0 < y - x := by linarith
  have hlam_eq : (interiorCost x y + A * H x + B * H y) / (y - x) =
      (J x - J y) / 2 + (A * H x + B * H y) / (y - x) := by
    rw [hIC]; field_simp; ring
  have rH1 : (0 : ℝ) ≤ ((P.x.Hlo : ℚ) : ℝ) := by exact_mod_cast h1
  have rH2 : (0 : ℝ) ≤ ((P.y.Hlo : ℚ) : ℝ) := by exact_mod_cast h2
  have elam : ((P.lam : ℚ) : ℝ) = (((P.x.Jlo : ℚ) : ℝ) - ((P.y.Jhi : ℚ) : ℝ)) / 2 +
      (((P.Alo : ℚ) : ℝ) * ((P.x.Hlo : ℚ) : ℝ) + ((P.Blo : ℚ) : ℝ) * ((P.y.Hlo : ℚ) : ℝ)) /
        ((P.dd : ℚ) : ℝ) := by
    simp only [lam]; push_cast; ring
  have hlam : ((P.lam : ℚ) : ℝ) ≤ (interiorCost x y + A * H x + B * H y) / (y - x) := by
    rw [hlam_eq, elam, hdd]
    have t1 : ((P.Alo : ℚ) : ℝ) * ((P.x.Hlo : ℚ) : ℝ) ≤ A * H x :=
      mul_le_mul hA_lo hHx0 rH1 hA0.le
    have t2 : ((P.Blo : ℚ) : ℝ) * ((P.y.Hlo : ℚ) : ℝ) ≤ B * H y :=
      mul_le_mul hB_lo hHy0 rH2 hB0.le
    have t3 : (((P.Alo : ℚ) : ℝ) * ((P.x.Hlo : ℚ) : ℝ) + ((P.Blo : ℚ) : ℝ) * ((P.y.Hlo : ℚ) : ℝ)) /
        (y - x) ≤ (A * H x + B * H y) / (y - x) :=
      div_le_div_of_nonneg_right (by linarith) hyx.le
    linarith
  have hd0 : 0 ≤ μ.b - μ.a := by linarith
  have he0 : 0 ≤ μ.e := μ.e_pos.le
  have hf0 : 0 ≤ μ.f := μ.f_pos.le
  have k1 := mul_le_mul_of_nonneg_right hlam hd0
  have k2 := mul_le_mul_of_nonneg_right hA_hi he0
  have k3 := mul_le_mul_of_nonneg_right hB_hi hf0
  refine ⟨by linarith, hA0.le.trans hA_hi, hB0.le.trans hB_hi⟩

end Plane

end CKLaneN1b

end


