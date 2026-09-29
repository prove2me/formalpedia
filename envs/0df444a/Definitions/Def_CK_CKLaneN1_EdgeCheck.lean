-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeCheck
-- name    : CK_CKLaneN1_EdgeCheck
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:05:41.58631+00:00
-- url     : https://prove2.me/theorems/5a6b303f-bb5a-4b0f-96d6-f47d7e3d3b1a
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeCheck` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeCheck` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeCheck` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeCheck (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeCheck.lean)

import Definitions.Def_CK_CKLaneN1_Tree
import Definitions.Def_CK_CKLaneN1_CapSlope

-- ===== source module CKLaneN1.EdgeCheck =====
section

set_option autoImplicit false

/-!
# Lane N1: leftEdge box checker (exact rationals, kernel-evaluated)

Chart on the cutoff edge `a + c = S`, `S = 1/10000`, `m = S/2`:
`t ∈ [0,1]`, `z ∈ [0,1]`, `y = S t`, `a = m (1 - t)`, `b = m (1 + t (2z - 1))`, `c = m (1 + t)`,
`M = (a+b)/2 = m (1 - t (1 - z))`.  A box is a `B3` with `t ∈ [a0,a1]`, `z ∈ [b0,b1]`.

`edgeOK B w` certifies `cPG a c (H a) (H b) ≥ y² · P(z) > 0` on the box, where
`P = T1 + T2 - T3 - T4` is a quadratic in `z` with rational coefficients (`ePoly`):
* `T1 = A (1 - z²)`, `A = slopeLo v1 / X̄ / (4 h1)`, `X̄ = y1/(2 h0)` (ratio bound for `Θ`);
* `T2` interior cost: normalized `z²/(2 M1 log 2)` or direct `z Δ/(2 y1)`;
* `T3` entropy-Jensen penalty: normalized `z² Θ̄ ξ` (via `C(ρ)/ρ²` monotone) or direct constant;
* `T4` outer tangent penalty `(1-z) K [c4 + L]`, `K = 81/50` (tail `Θ` increment on `[128,∞)`).
-/

namespace CKLaneN1.Edge

open CKLaneE.FP CKLaneN1.Capital

/-- Witness of one edge box. -/
structure EWit where
  corner : Bool
  v1 : ℚ
  v2 : ℚ
  k2 : Bool
  k3 : Bool
  k4 : Bool
  deriving Repr

def Sq : ℚ := 1 / 10000
def mq : ℚ := 1 / 20000
def Kq : ℚ := 81 / 50
def CHq : ℚ := 1047 / 1000
def TCq : ℚ := 1023 / 1024
def ZCq : ℚ := 1 / 2048

def bAt (t z : ℚ) : ℚ := mq * (1 + t * (2 * z - 1))
def MAt (t z : ℚ) : ℚ := mq * (1 - t * (1 - z))

def ey0 (B : B3) : ℚ := Sq * B.a0
def ey1 (B : B3) : ℚ := Sq * B.a1
def ea0 (B : B3) : ℚ := mq * (1 - B.a1)
def ea1 (B : B3) : ℚ := mq * (1 - B.a0)
def ec1 (B : B3) : ℚ := mq * (1 + B.a1)
def eb0 (B : B3) : ℚ :=
  min (min (bAt B.a0 B.b0) (bAt B.a0 B.b1)) (min (bAt B.a1 B.b0) (bAt B.a1 B.b1))
def eb1 (B : B3) : ℚ :=
  max (max (bAt B.a0 B.b0) (bAt B.a0 B.b1)) (max (bAt B.a1 B.b0) (bAt B.a1 B.b1))
def eM0 (B : B3) : ℚ :=
  min (min (MAt B.a0 B.b0) (MAt B.a0 B.b1)) (min (MAt B.a1 B.b0) (MAt B.a1 B.b1))
def eM1 (B : B3) : ℚ :=
  max (max (MAt B.a0 B.b0) (MAt B.a0 B.b1)) (max (MAt B.a1 B.b0) (MAt B.a1 B.b1))
def ee0 (B : B3) : ℚ := if ea0 B = 0 then 0 else Hlo (ea0 B)
def ee1 (B : B3) : ℚ := Hhi (ea1 B)
def ef0 (B : B3) : ℚ := Hlo (eb0 B)
def ef1 (B : B3) : ℚ := Hhi (eb1 B)
def eh0 (B : B3) : ℚ := (ee0 B + ef0 B) / 2
def eh1 (B : B3) : ℚ := (ee1 B + ef1 B) / 2
def eXbar (B : B3) : ℚ := ey1 B / (2 * eh0 B)
def eXhat (B : B3) : ℚ := 1 / (2 * eh0 B)
def eA (B : B3) (w : EWit) : ℚ := slopeLo w.v1 / eXbar B / (4 * eh1 B)
def eJM1 (B : B3) : ℚ := lamLo (eM1 B) / LqHi
def erho1 (B : B3) : ℚ := B.b1 * B.a1 / (1 - B.a1 + B.b1 * B.a1)
def erhop1 (B : B3) : ℚ := mq * B.b1 * B.a1 / (1 - eM1 B)
def eChi1 (B : B3) : ℚ :=
  ((1 + erho1 B) * (-l1Lo (erho1 B / (1 + erho1 B))) + (1 - erho1 B) * l1Hi (erho1 B)) /
    erho1 B ^ 2
def exi (B : B3) : ℚ := (eChi1 B / eM0 B + CHq / (1 - eM1 B)) / (4 * LqLo * eJM1 B)
def eDelta (B : B3) : ℚ := lamLo (ea1 B) / LqHi - lamHi (eb0 B) / LqLo
def ec4 (B : B3) : ℚ := 2 / (1 - 2 * ec1 B)
def eg (B : B3) : ℚ := lamHi (ea0 B) / LqLo / (2 * eh0 B)
def eq4 (B : B3) : ℚ := (ef1 B - ee0 B) / (2 * ef1 B)
def eLhi (B : B3) : ℚ := -l1Lo (eq4 B)

/-- `T2` coefficients `(z, z²)`. -/
def eT2 (B : B3) (w : EWit) : ℚ × ℚ :=
  if w.k2 then (eDelta B / (2 * ey1 B), 0) else (0, 1 / (2 * eM1 B * LqHi))

/-- `T3` coefficients `(1, z²)` (subtracted). -/
def eT3 (B : B3) (w : EWit) : ℚ × ℚ :=
  if w.k3 then
    (slopeHi w.v2 * (eM1 B * (2 * LqHi) + (1 - eM0 B) * erhop1 B ^ 2 * CHq) /
      (LqLo * eJM1 B * ey0 B ^ 2), 0)
  else (0, slopeHi w.v2 * exi B)

/-- `T4` coefficients `(1, z, z²)` (subtracted). -/
def eT4 (B : B3) (w : EWit) : ℚ × ℚ × ℚ :=
  if w.k4 then
    (Kq * (ec4 B + eLhi B / ey0 B), -(Kq * (ec4 B + eLhi B / ey0 B)), 0)
  else (Kq * ec4 B, Kq * (eg B - ec4 B), -(Kq * eg B))

def eP0 (B : B3) (w : EWit) : ℚ := eA B w - (eT3 B w).1 - (eT4 B w).1
def eP1 (B : B3) (w : EWit) : ℚ := (eT2 B w).1 - (eT4 B w).2.1
def eP2 (B : B3) (w : EWit) : ℚ := -eA B w + (eT2 B w).2 - (eT3 B w).2 - (eT4 B w).2.2

/-- Positivity of `c0 + c1 z + c2 z²` on `[z0, z1]`. -/
def qposOK (c0 c1 c2 z0 z1 : ℚ) : Bool :=
  decide (0 < c0 + c1 * z0 + c2 * z0 ^ 2) && decide (0 < c0 + c1 * z1 + c2 * z1 ^ 2) &&
    (decide (c2 ≤ 0) || decide (0 < 4 * c0 * c2 - c1 ^ 2) || decide (-c1 ≤ 2 * c2 * z0) ||
      decide (2 * c2 * z1 ≤ -c1))

/-- Variant-specific side conditions. -/
def eVarOK (B : B3) (w : EWit) : Bool :=
  (if w.k2 then ptOk (ea1 B) && decide (0 ≤ lamLo (ea1 B)) && decide (0 ≤ eDelta B) &&
      decide (0 < ey1 B) else true) &&
  (if w.k3 then decide (0 < ey0 B)
    else decide (0 < erho1 B) && decide (erho1 B < 1) && ptOk (erho1 B) &&
      ptOk (erho1 B / (1 + erho1 B)) && decide (0 ≤ eChi1 B)) &&
  (if w.k4 then decide (0 < ey0 B) && ptOk (eq4 B)
    else decide (0 < ea0 B) && ptOk (ea0 B))

/-- Box shape. -/
def eShapeOK (B : B3) : Bool :=
  decide (0 ≤ B.a0) && decide (B.a0 < B.a1) && decide (B.a1 ≤ 1) &&
  decide (0 ≤ B.b0) && decide (B.b0 < B.b1) && decide (B.b1 ≤ 1) &&
  decide (0 < eb0 B) && decide (0 < eM0 B)

/-- Certified logarithm points and scalar side conditions. -/
def eLogsOK (B : B3) : Bool :=
  (decide (ea0 B = 0) || ptOk (ea0 B)) && ptOk (ea1 B) && ptOk (eb0 B) && ptOk (eb1 B) &&
  ptOk (eM1 B) && decide (0 < eh0 B) && decide (256 * ef1 B ≤ 1 - 2 * ec1 B) &&
  decide (0 < lamLo (eM1 B)) && decide (erhop1 B ≤ 1 / 2)

/-- Contact brackets for `Θ(X̄)` (lower) and `Θ(X̂)` (upper). -/
def eThetaOK (B : B3) (w : EWit) : Bool :=
  slopeLoOk w.v1 && decide (0 ≤ slopeLo w.v1) &&
  decide (1 - 2 * w.v1 ≤ 2 * eXbar B * Hlo w.v1) &&
  slopeHiOk w.v2 && decide (2 * eXhat B * Hhi w.v2 ≤ 1 - 2 * w.v2)

/-- Kernel check of one (non-corner) edge box. -/
def edgeOK (B : B3) (w : EWit) : Bool :=
  eShapeOK B && eLogsOK B && eThetaOK B w && eVarOK B w &&
  qposOK (eP0 B w) (eP1 B w) (eP2 B w) B.b0 B.b1

/-- Leaf check: a certified box, or the corner box `t ≥ 1023/1024`, `z ≤ 1/2048`. -/
def edgeLeafOK (B : B3) (w : EWit) : Bool :=
  if w.corner then
    decide (TCq ≤ B.a0) && decide (B.a1 ≤ 1) && decide (0 ≤ B.b0) && decide (B.b1 ≤ ZCq)
  else edgeOK B w

/-- Root box `[0,1]²` in `(t, z)`. -/
def edgeRoot : B3 := ⟨0, 1, 0, 1, 0, 0⟩

/-! ## Quadratic positivity -/

theorem qposOK_sound {c0 c1 c2 z0 z1 : ℚ} (h : qposOK c0 c1 c2 z0 z1 = true) {z : ℝ}
    (hz0 : (z0 : ℝ) ≤ z) (hz1 : z ≤ (z1 : ℝ)) :
    0 < (c0 : ℝ) + c1 * z + c2 * z ^ 2 := by
  simp only [qposOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp0, hp1⟩, hc⟩ := h
  have hp0R : (0 : ℝ) < c0 + c1 * z0 + c2 * z0 ^ 2 := by exact_mod_cast hp0
  have hp1R : (0 : ℝ) < c0 + c1 * z1 + c2 * z1 ^ 2 := by exact_mod_cast hp1
  have hz01 : (z0 : ℝ) ≤ z1 := hz0.trans hz1
  -- concave case
  by_cases hc2 : (c2 : ℝ) ≤ 0
  · rcases eq_or_lt_of_le hz01 with heq | hlt
    · have : z = z0 := le_antisymm (heq ▸ hz1) hz0
      subst this; exact hp0R
    · have key : ((c0 : ℝ) + c1 * z + c2 * z ^ 2) * (z1 - z0) =
          (z1 - z) * (c0 + c1 * z0 + c2 * z0 ^ 2) + (z - z0) * (c0 + c1 * z1 + c2 * z1 ^ 2) -
            c2 * (z - z0) * (z1 - z) * (z1 - z0) := by ring
      have h1 : 0 ≤ (z1 - z) * ((c0 : ℝ) + c1 * z0 + c2 * z0 ^ 2) :=
        mul_nonneg (by linarith) hp0R.le
      have h2 : 0 ≤ (z - z0) * ((c0 : ℝ) + c1 * z1 + c2 * z1 ^ 2) :=
        mul_nonneg (by linarith) hp1R.le
      have h3 : 0 ≤ -(c2 : ℝ) * ((z - z0) * (z1 - z) * (z1 - z0)) :=
        mul_nonneg (by linarith) (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
      have hpos : 0 < ((c0 : ℝ) + c1 * z + c2 * z ^ 2) * (z1 - z0) := by
        rw [key]
        rcases lt_or_eq_of_le hz0 with hlt0 | heq0
        · have : 0 < (z - z0) * ((c0 : ℝ) + c1 * z1 + c2 * z1 ^ 2) :=
            mul_pos (by linarith) hp1R
          nlinarith
        · subst heq0
          have : 0 < (z1 - (z0 : ℝ)) * ((c0 : ℝ) + c1 * z0 + c2 * z0 ^ 2) :=
            mul_pos (by linarith) hp0R
          nlinarith
      exact pos_of_mul_pos_left hpos (by linarith) |>.trans_le' le_rfl |> fun h => by
        nlinarith [hpos]
  · have hc2 : (0 : ℝ) < c2 := lt_of_not_ge hc2
    rcases hc with ((hc | hc) | hc) | hc
    · exact absurd (by exact_mod_cast hc) (not_le.mpr hc2)
    · have hd : (0 : ℝ) < 4 * c0 * c2 - c1 ^ 2 := by exact_mod_cast hc
      nlinarith [sq_nonneg (2 * (c2 : ℝ) * z + c1)]
    · have hv : -(c1 : ℝ) ≤ 2 * c2 * z0 := by exact_mod_cast hc
      have : ((c0 : ℝ) + c1 * z + c2 * z ^ 2) - (c0 + c1 * z0 + c2 * z0 ^ 2) =
          (z - z0) * (c1 + c2 * (z + z0)) := by ring
      have h2 : 0 ≤ (z - (z0 : ℝ)) * (c1 + c2 * (z + z0)) :=
        mul_nonneg (by linarith) (by nlinarith)
      linarith
    · have hv : 2 * (c2 : ℝ) * z1 ≤ -c1 := by exact_mod_cast hc
      have : ((c0 : ℝ) + c1 * z + c2 * z ^ 2) - (c0 + c1 * z1 + c2 * z1 ^ 2) =
          (z1 - z) * (-(c1 + c2 * (z + z1))) := by ring
      have h2 : 0 ≤ (z1 - z) * (-((c1 : ℝ) + c2 * (z + z1))) :=
        mul_nonneg (by linarith) (by nlinarith)
      linarith

end CKLaneN1.Edge

end


