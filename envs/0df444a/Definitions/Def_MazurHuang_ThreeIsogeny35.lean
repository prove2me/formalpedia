-- Prove2me | Definitions.Def_MazurHuang_ThreeIsogeny35
-- name    : MazurHuang_ThreeIsogeny35
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:04:58.304983+00:00
-- url     : https://prove2.me/theorems/ddb1d4da-2831-49c4-a028-3a0d1d0147db
-- title:
--   The 3-isogenous pair of curves of conductor 35 and the explicit isogeny formulas
-- statement:
--   Notation for an explicit pair of $3$-isogenous elliptic curves over $\mathbb{Q}$ of conductor $35$ (namespace `MazurHuang.ThreeIsogeny35`).
--
--   * `E35ShortCurve` is the Weierstrass curve $E : y^2 = x^3 + 16x^2 + 224x + 784$, that is $y^2 = x^3 + (4x+28)^2$; `OnE35Short x y` is this equation. It is a model of the curve with Cremona label 35a1 (see the theorem `MazurHuang.eq_one_of_curve_35a1_equation` for the change of coordinates), and $(0,\pm 28)$ are rational points of order $3$.
--   * `E35DualCurve` is $E' : t^2 = s^3 - 432 s^2 - 108000 s - 6750000$, that is $t^2 = s^3 - 3(12s+1500)^2$; `OnE35Dual s t` is this equation.
--   * Both curves are elliptic (discriminants $-175616000$ and $-29760696000000000$); the instances and the two `equation_iff` lemmas are part of the definition file. `E35ShortPoint` and `E35DualPoint` are the Mathlib groups of rational points `WeierstrassCurve.Affine.Point`.
--   * The isogeny $\varphi : E \to E'$ with kernel $\{O,(0,\pm28)\}$ is given away from the kernel by
--     $$\varphi(x,y) = \Bigl(\frac{9x^3+192x^2+4032x+28224}{x^2},\ \frac{27x^3y-12096xy-169344y}{x^3}\Bigr)$$
--     (`threeIsogenyX`, `threeIsogenyY`), and the isogeny $\hat\varphi : E' \to E$ in the other direction is given for $s \neq 0$ by
--     $$\hat\varphi(s,t) = \Bigl(\frac{s^3-576s^2-216000s-27000000}{81s^2},\ \frac{s^3t+216000st+54000000t}{729s^3}\Bigr)$$
--     (`dualThreeIsogenyX`, `dualThreeIsogenyY`). The lemmas `threeIsogeny_on_curve` and `dualThreeIsogeny_on_curve` state that these formulas map points of one curve to points of the other.
--   * `threeIsogenyPoint : E35ShortPoint → E35DualPoint` and `dualThreeIsogenyPoint : E35DualPoint → E35ShortPoint` are the corresponding maps of point sets: the point at infinity and the points with first coordinate $0$ go to the point at infinity, and every other point is mapped by the formulas above. They are defined as plain functions; no additivity is asserted.
--   * `shortTangent`, `shortDoubleX`, `shortDoubleY`, `shortTripleSlope`, `shortTripleX`, `shortTripleY` are the chord-and-tangent expressions for the coordinates of $2P$ and $3P$ on $E$ in terms of the coordinates $(x,y)$ of $P$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; FLT/Assumptions/MazurProof/RationalPointsX135.lean (declarations E35ShortCurve to dualThreeIsogeny_on_curve, threeIsogenyPoint to dualThreeIsogenyPoint_some_of_x_ne_zero, shortTangent to shortTripleY).

/-
The curve y^2 = x^3 + (4 x + 28)^2 (Cremona 35a1), its 3-isogenous curve and the two
3-isogenies: definitions and their immediate API.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580,
  FLT/Assumptions/MazurProof/RationalPointsX135.lean (declarations E35ShortCurve ... dualThreeIsogeny_on_curve,
  threeIsogenyPoint ... dualThreeIsogenyPoint_some_of_x_ne_zero, shortTangent ... shortTripleY);
  the namespace is MazurHuang.ThreeIsogeny35 instead of MazurProof.RationalPointsX135 and the
  six tripling formulas are public instead of private; nothing else is changed,
  ported to Lean v4.33.1 / Mathlib 0df444a360ea.
-/
import Mathlib

open scoped WeierstrassCurve.Affine

namespace MazurHuang.ThreeIsogeny35

noncomputable section

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 715-790
def E35ShortCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 16
  a₃ := 0
  a₄ := 224
  a₆ := 784

def E35DualCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -432
  a₃ := 0
  a₄ := -108000
  a₆ := -6750000

def OnE35Short (x y : ℚ) : Prop := y ^ 2 = x ^ 3 + (4 * x + 28) ^ 2

def OnE35Dual (s t : ℚ) : Prop := t ^ 2 = s ^ 3 - 3 * (12 * s + 1500) ^ 2

theorem E35ShortCurve_delta : E35ShortCurve.Δ = (-175616000 : ℚ) := by
  norm_num [E35ShortCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem E35DualCurve_delta : E35DualCurve.Δ = (-29760696000000000 : ℚ) := by
  norm_num [E35DualCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E35ShortCurve_isElliptic : E35ShortCurve.IsElliptic where
  isUnit := by rw [E35ShortCurve_delta]; norm_num

instance E35DualCurve_isElliptic : E35DualCurve.IsElliptic where
  isUnit := by rw [E35DualCurve_delta]; norm_num

@[simp] theorem E35ShortCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation E35ShortCurve x y ↔ OnE35Short x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [E35ShortCurve, OnE35Short]
  ring_nf

@[simp] theorem E35DualCurve_equation_iff (s t : ℚ) :
    WeierstrassCurve.Affine.Equation E35DualCurve s t ↔ OnE35Dual s t := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [E35DualCurve, OnE35Dual]
  ring_nf

abbrev E35ShortPoint := WeierstrassCurve.Affine.Point E35ShortCurve
abbrev E35DualPoint := WeierstrassCurve.Affine.Point E35DualCurve

def threeIsogenyX (x : ℚ) : ℚ :=
  (9 * x ^ 3 + 192 * x ^ 2 + 4032 * x + 28224) / x ^ 2

def threeIsogenyY (x y : ℚ) : ℚ :=
  (27 * x ^ 3 * y - 12096 * x * y - 169344 * y) / x ^ 3

def dualThreeIsogenyX (s : ℚ) : ℚ :=
  (s ^ 3 - 576 * s ^ 2 - 216000 * s - 27000000) / (81 * s ^ 2)

def dualThreeIsogenyY (s t : ℚ) : ℚ :=
  (s ^ 3 * t + 216000 * s * t + 54000000 * t) / (729 * s ^ 3)

theorem threeIsogeny_on_curve {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    OnE35Dual (threeIsogenyX x) (threeIsogenyY x y) := by
  unfold OnE35Short at h
  unfold OnE35Dual threeIsogenyX threeIsogenyY
  field_simp [hx]
  simp_rw [h]
  ring

theorem dualThreeIsogeny_on_curve {s t : ℚ} (hs : s ≠ 0)
    (h : OnE35Dual s t) :
    OnE35Short (dualThreeIsogenyX s) (dualThreeIsogenyY s t) := by
  unfold OnE35Dual at h
  unfold OnE35Short dualThreeIsogenyX dualThreeIsogenyY
  field_simp [hs]
  simp_rw [h]
  ring

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 872-908
noncomputable def threeIsogenyPoint : E35ShortPoint → E35DualPoint
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (E35DualCurve_equation_iff _ _ |>.2 <|
          threeIsogeny_on_curve hx (E35ShortCurve_equation_iff _ _ |>.1 h.1))

noncomputable def dualThreeIsogenyPoint : E35DualPoint → E35ShortPoint
  | .zero => .zero
  | .some s _t h =>
      if hs : s = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (E35ShortCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs (E35DualCurve_equation_iff _ _ |>.1 h.1))

@[simp] theorem threeIsogenyPoint_zero : threeIsogenyPoint 0 = 0 := rfl

@[simp] theorem dualThreeIsogenyPoint_zero : dualThreeIsogenyPoint 0 = 0 := rfl

theorem threeIsogenyPoint_some_of_x_ne_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E35ShortCurve x y)
    (hx : x ≠ 0) :
    threeIsogenyPoint (.some x y h) =
      WeierstrassCurve.Affine.Point.mk
        (E35DualCurve_equation_iff _ _ |>.2 <|
          threeIsogeny_on_curve hx (E35ShortCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [threeIsogenyPoint, hx]

theorem dualThreeIsogenyPoint_some_of_x_ne_zero {s t : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E35DualCurve s t)
    (hs : s ≠ 0) :
    dualThreeIsogenyPoint (.some s t h) =
      WeierstrassCurve.Affine.Point.mk
        (E35ShortCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs (E35DualCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [dualThreeIsogenyPoint, hs]

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 916-933 (with `private def` replaced by `def`, 6 times)
def shortTangent (x y : ℚ) : ℚ :=
  (3 * x ^ 2 + 32 * x + 224) / (2 * y)

def shortDoubleX (x y : ℚ) : ℚ :=
  shortTangent x y ^ 2 - 16 - 2 * x

def shortDoubleY (x y : ℚ) : ℚ :=
  -(shortTangent x y * (shortDoubleX x y - x) + y)

def shortTripleSlope (x y : ℚ) : ℚ :=
  (shortDoubleY x y - y) / (shortDoubleX x y - x)

def shortTripleX (x y : ℚ) : ℚ :=
  shortTripleSlope x y ^ 2 - 16 - shortDoubleX x y - x

def shortTripleY (x y : ℚ) : ℚ :=
  -(shortTripleSlope x y * (shortTripleX x y - shortDoubleX x y) +
      shortDoubleY x y)

end

end MazurHuang.ThreeIsogeny35


