-- Prove2me | Definitions.Def_PolygonPack_clearance
-- name    : PolygonPack_clearance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:48.892046+00:00
-- url     : https://prove2.me/theorems/d7607882-12db-4ffd-85fb-ddda573732ed
-- title:
--   Clearance, the repaired angle and the prefix coefficients
-- statement:
--   At an orientation with direction $(a,b)$, $a=\cos\phi$, $b=\sin\phi$, the **clearance** of a diameter $D$ is $C(D)=a+b-2abD$. For a largest diameter $M$, the **repaired angle** is given by
--   $$
--   \cos\phi=\frac{1-2c}M+\frac{2c}{\sqrt2},\qquad\sin\phi\ge0.
--   $$
--   The constants are $R=2+2\sqrt2$, $D_0=2/\sqrt3$,
--   $$
--   \alpha_{\mathrm{ad}}=\frac{R+4\sqrt2c}{1-12c},\qquad
--   \alpha_{\mathrm{an}}=\max\Bigl\{2+\frac{2\sqrt2+4\sqrt2c}{D_B},\ \frac2{D_B(\sqrt2-D_B)}\Bigr\}.
--   $$
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), App. C.1, p.32; Lemma C.2, p.32; Lemma C.5, p.35; Lemma C.6, p.36

import Mathlib

namespace PolygonPack

/-- **Clearance and the repaired angle.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), App. C.1, p.32: "C(D) = a + b − 2abD", Lemma C.2, p.32: "cos φ =
(1 − 2c)/M + 2c/√2". App. C, p.31: "R = 2 + 2√2", p.32: "D0 = 2/√3".

`clr a b D` is the clearance, `repairCos c M` and `repairSin c M` are `a = cos φ`, `b = sin φ` at the repaired
angle, with `0 ≤ b`. `alphaAd` and `alphaAn` are the prefix coefficients of Lemmas C.5 and C.6.

**Formalization Note.** `repairCos c M` is a convex combination of `1/M` and `1/√2` for `0 < c ≤ 1/24`, so it lies in
`(0, 1]` when `M ≥ 1`, and `repairSin` is then the sine. -/
noncomputable def clr (a b D : ℝ) : ℝ := a + b - 2 * a * b * D

/-- `cos φ = (1 − 2c)/M + 2c/√2`. -/
noncomputable def repairCos (c M : ℝ) : ℝ := (1 - 2 * c) / M + 2 * c / Real.sqrt 2

/-- `sin φ ≥ 0` for that angle. -/
noncomputable def repairSin (c M : ℝ) : ℝ := Real.sqrt (1 - repairCos c M ^ 2)

/-- `R = 2 + 2√2`. -/
noncomputable def constR : ℝ := 2 + 2 * Real.sqrt 2

/-- `D0 = 2/√3`. -/
noncomputable def constD0 : ℝ := 2 / Real.sqrt 3

/-- `α_ad = (R + 4√2c)/(1 − 12c)`. -/
noncomputable def alphaAd (c : ℝ) : ℝ := (constR + 4 * Real.sqrt 2 * c) / (1 - 12 * c)

/-- `α_an = max{2 + (2√2 + 4√2c)/D_B, 2/(D_B(√2 − D_B))}`. -/
noncomputable def alphaAn (c DB : ℝ) : ℝ :=
  max (2 + (2 * Real.sqrt 2 + 4 * Real.sqrt 2 * c) / DB) (2 / (DB * (Real.sqrt 2 - DB)))

end PolygonPack


