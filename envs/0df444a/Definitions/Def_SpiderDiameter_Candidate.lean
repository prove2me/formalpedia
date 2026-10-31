-- Prove2me | Definitions.Def_SpiderDiameter_Candidate
-- name    : SpiderDiameter_Candidate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:11.41257+00:00
-- url     : https://prove2.me/theorems/e7491936-be6e-4ba8-be10-875820b68584
-- title:
--   Explicit candidate $U$: $\varphi$, its inverse $f$, (3.8), Corollary 3.5 (corrected), (3.12)–(3.13)
-- statement:
--   Fix $n\ge 3$. Let
--   $$\varphi(s)=(n-1)s-\frac{(n-1)^2}{2}+\frac{n(n-2)}{2}\exp\Big(-\frac{2s}{n-1}\Big),$$
--   so that $\varphi(0)=-\tfrac12$ and $\varphi$ is strictly increasing on $[0,\infty)$. Let $f(z)=z+\tfrac12$ for $z\le-\tfrac12$, and for $z>-\tfrac12$ let $f(z)$ be the unique $s\ge0$ with $\varphi(s)=z$; this $f$ is written $\varphi^{-1}$ in the paper.
--
--   The candidate value function $U(x,y,z)$ is defined in three regions.
--
--   1. If $y\ge\tfrac12$ and $z\le\varphi(y-\tfrac12)$, $U$ is given by the five lines of (3.8):
--   $y-z-2(z+\tfrac12)x+(z+\tfrac12)^2$ if $x\le f(z)\le0$; $y-z-\tfrac{2f(z)}{n-1}x+f(z)^2$ if $x\le0\le f(z)$; $y-z-2f(z)x+f(z)^2$ if $0\le x\le f(z)$; $y-z-x^2$ if $f(z)\le x\le y-\tfrac12$; $y-z-2(y-\tfrac12)x+(y-\tfrac12)^2$ if $x\ge y-\tfrac12$.
--   2. If $y\ge\tfrac12$ and $z>\varphi(y-\tfrac12)$,
--   $$U(x,y,z)=U\big(x,f(z)+\tfrac12,z\big)-\int_y^{f(z)+1/2}\frac{(n-1)(s-x)}{(n-1)s-\varphi(s-\frac12)}\,ds\quad(x\ge0),$$
--   with numerator $(n-1)s-x$ for $x<0$; the first term is (3.8) at the point $(x,f(z)+\tfrac12,z)$.
--   3. If $y<\tfrac12$, $U$ is given by (3.12) for $x<0$ and (3.13) for $x\ge0$, in terms of $U(\tfrac12,\tfrac12,s)$, $s\in[-\tfrac12,z]$, taken from the two previous regions.
--
--   The constant of Theorem 1.1 is $C_n=2\sqrt{U(0,0,0)}$, where by (3.13)
--   $$U(0,0,0)=\int_{-1/2}^{0}U(\tfrac12,\tfrac12,s)\,\frac{2n(n-1)}{(n-1-2s)^2}\,ds .$$
--   Numerically $U(0,0,0)\approx0.789944$ for $n=3$ ($C_3\approx1.777576$), $0.807389$ for $n=4$ and $0.817206$ for $n=5$; at $n=2$ the same formulas give exactly $3/4$, the known value.
--
--   **Formalization Note** The integrand of region 2 uses $\varphi(s-\tfrac12)$, a correction of the printed $\varphi(y-\tfrac12)$ in Corollary 3.5: the corollary integrates (3.9) of Lemma 3.4 in $y$, and the printed version contradicts (3.9) and the continuity of $U$ across $y=\tfrac12$. The functions are total on $\mathbb R^3$; only their values on the state space are used.
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, §3: Step 6 (φ, f), p.14; Step 5 (f(z) = z + 1/2), pp.13–14; eq. (3.8), p.15; Corollary 3.5, p.17 (corrected); eqs. (3.12), p.17 and (3.13), p.18

import Mathlib

namespace SpiderDiameter

/-! A family of tightly coupled definitions: the explicit candidate `U` of §3, built region by
region from `φ`, its extended inverse `f`, the five-line formula (3.8), Corollary 3.5 (corrected)
and (3.12)–(3.13). All functions are real-valued and total on `ℝ³`; only their values on the
state space `𝒟` (and on `{y = 1/2}` for `U(1/2, 1/2, ·)`) are meaningful. -/

/-- **The function `φ`** of Step 6.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, §3 Step 6, p.14:
`φ(s) = (n − 1)s − (n − 1)²/2 + (n(n − 2)/2) exp(−2s/(n − 1))`.
It satisfies `φ(0) = −1/2` and is strictly increasing on `[0, ∞)` (for `n ≥ 2`). -/
noncomputable def phi (n : ℕ) (s : ℝ) : ℝ :=
  ((n : ℝ) - 1) * s - ((n : ℝ) - 1) ^ 2 / 2
    + (n : ℝ) * ((n : ℝ) - 2) / 2 * Real.exp (-(2 * s) / ((n : ℝ) - 1))

/-- **The lower boundary `f`**, written `φ⁻¹` in (3.8) and Corollary 3.5.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, §3 Steps 5–6, pp.13–14: "f(z) = z + 1/2" for
`z ≤ −1/2` (Step 5), and "for z > −1/2, f is the inverse to the above function" (Step 6), i.e.
`f(z)` is the unique `s ≥ 0` with `φ(s) = z`.

**Formalization Note.** `φ` is not injective on `ℝ`, so `φ⁻¹` is read as this two-branch
function. For `z > −1/2` the inverse is written as `inf {s ≥ 0 : z ≤ φ(s)}`, which is the unique
root of `φ(s) = z` in `[0, ∞)` because `φ` is continuous and strictly increasing there with
`φ(0) = −1/2` and `φ(s) → ∞`. Both branches give `f(−1/2) = 0`. -/
noncomputable def finv (n : ℕ) (z : ℝ) : ℝ :=
  if z ≤ -1 / 2 then z + 1 / 2 else sInf {s : ℝ | 0 ≤ s ∧ z ≤ phi n s}

/-- **Formula (3.8)** (Corollary 3.3), the candidate on `{y ≥ 1/2, z ≤ φ(y − 1/2)}`.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, eq. (3.8), p.15, with `φ⁻¹(z) = finv n z`:
* `y − z − 2(z + 1/2)x + (z + 1/2)²` if `x ≤ φ⁻¹(z) ≤ 0`,
* `y − z − (2φ⁻¹(z)/(n−1))x + (φ⁻¹(z))²` if `x ≤ 0 ≤ φ⁻¹(z)`,
* `y − z − 2φ⁻¹(z)x + (φ⁻¹(z))²` if `0 ≤ x ≤ φ⁻¹(z)`,
* `y − z − x²` if `φ⁻¹(z) ≤ x ≤ y − 1/2`,
* `y − z − 2(y − 1/2)x + (y − 1/2)²` if `x ≥ y − 1/2`.

**Formalization Note.** The cases are tested in the printed order; adjacent cases agree where
they overlap, so the order does not matter. -/
noncomputable def U38 (n : ℕ) (x y z : ℝ) : ℝ :=
  let F := finv n z
  if x ≤ F ∧ F ≤ 0 then y - z - 2 * (z + 1 / 2) * x + (z + 1 / 2) ^ 2
  else if x ≤ 0 ∧ 0 ≤ F then y - z - 2 * F / ((n : ℝ) - 1) * x + F ^ 2
  else if 0 ≤ x ∧ x ≤ F then y - z - 2 * F * x + F ^ 2
  else if F ≤ x ∧ x ≤ y - 1 / 2 then y - z - x ^ 2
  else y - z - 2 * (y - 1 / 2) * x + (y - 1 / 2) ^ 2

/-- **The integrand of Corollary 3.5, corrected**: `(n − 1)(s − x)/((n − 1)s − φ(s − 1/2))` for
`x ≥ 0` and `((n − 1)s − x)/((n − 1)s − φ(s − 1/2))` for `x < 0` (the two agree at `x = 0`).
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, Corollary 3.5, p.17, and (3.9), p.15.

**Formalization Note (correction).** The page prints the denominator `(n − 1)s − φ(y − 1/2)`,
with the lower limit `y` in place of the integration variable. Corollary 3.5 integrates (3.9)
of Lemma 3.4 in `y` from `y` to `f(z) + 1/2`, and (3.9) at the point `s` has denominator
`(n − 1)s − φ(s − 1/2)`; the printed version contradicts (3.9) and the continuity of `U` across
`y = 1/2` (see the mission's moderation notes). -/
noncomputable def integrand35 (n : ℕ) (x s : ℝ) : ℝ :=
  if 0 ≤ x then ((n : ℝ) - 1) * (s - x) / (((n : ℝ) - 1) * s - phi n (s - 1 / 2))
  else (((n : ℝ) - 1) * s - x) / (((n : ℝ) - 1) * s - phi n (s - 1 / 2))

/-- **Corollary 3.5 (corrected)**, the candidate on `{y ≥ 1/2, z > φ(y − 1/2)}`:
`U(x, f(z) + 1/2, z) − ∫_y^{f(z)+1/2} integrand35 n x s ds`, where the first term is (3.8) at the
point `(x, f(z) + 1/2, z)` (which lies in the region of (3.8), since `z = φ(f(z))`).
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, Corollary 3.5, p.17. -/
noncomputable def U35 (n : ℕ) (x y z : ℝ) : ℝ :=
  U38 n x (finv n z + 1 / 2) z - ∫ s in y..(finv n z + 1 / 2), integrand35 n x s

/-- **`U(1/2, 1/2, s)`**, the candidate on the segment used in (3.12)–(3.13): (3.8) when
`s ≤ φ(0) = −1/2`, Corollary 3.5 (corrected) when `s > −1/2`.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, p.18: "The values of U(1/2, 1/2, s) can be extracted
from Corollary 3.5." -/
noncomputable def Uhalf (n : ℕ) (s : ℝ) : ℝ :=
  if s ≤ phi n 0 then U38 n (1 / 2) (1 / 2) s else U35 n (1 / 2) (1 / 2) s

/-- **Formulas (3.12) and (3.13)** (Corollary 3.6), the candidate on `{y < 1/2}`.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, eqs. (3.12), p.17 (for `x < 0`) and (3.13), p.18
(for `x ≥ 0`), with `U(1/2, 1/2, s) = Uhalf n s`:
for `x < 0`,
`U(1/2,1/2,−y)·2((n−1)y − x)/(n−1+2y) + U(1/2,1/2,z)·2(x − z)/(n−1−2z)
 + ∫_{−1/2}^{−y} U(1/2,1/2,s)·2n(n−1)/(n−1−2s)² ds + ∫_{−y}^{z} U(1/2,1/2,s)·2(n−1−2x)/(n−1−2s)² ds`;
for `x ≥ 0`,
`U(1/2,1/2,−y)·2(n−1)(y − x)/(n−1+2y) + U(1/2,1/2,z)·2((n−1)x − z)/(n−1−2z)
 + ∫_{−1/2}^{−y} U(1/2,1/2,s)·2n(n−1)/(n−1−2s)² ds + ∫_{−y}^{z} U(1/2,1/2,s)·2(n−1)(1−2x)/(n−1−2s)² ds`. -/
noncomputable def U36 (n : ℕ) (x y z : ℝ) : ℝ :=
  let m : ℝ := (n : ℝ) - 1
  if x < 0 then
    Uhalf n (-y) * (2 * (m * y - x) / (m + 2 * y)) + Uhalf n z * (2 * (x - z) / (m - 2 * z))
      + (∫ s in (-1 / 2 : ℝ)..(-y), Uhalf n s * (2 * (n : ℝ) * m / (m - 2 * s) ^ 2))
      + ∫ s in (-y)..z, Uhalf n s * (2 * (m - 2 * x) / (m - 2 * s) ^ 2)
  else
    Uhalf n (-y) * (2 * m * (y - x) / (m + 2 * y)) + Uhalf n z * (2 * (m * x - z) / (m - 2 * z))
      + (∫ s in (-1 / 2 : ℝ)..(-y), Uhalf n s * (2 * (n : ℝ) * m / (m - 2 * s) ^ 2))
      + ∫ s in (-y)..z, Uhalf n s * (2 * m * (1 - 2 * x) / (m - 2 * s) ^ 2)

/-- **The candidate value function `U`** of §3, glued from its three regions:
(3.12)–(3.13) for `y < 1/2`; (3.8) for `y ≥ 1/2, z ≤ φ(y − 1/2)`; Corollary 3.5 (corrected) for
`y ≥ 1/2, z > φ(y − 1/2)`.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, §3, pp.15–18 (Corollaries 3.3, 3.5, 3.6). The
constant of Theorem 1.1 is `2 √(candidate n 0 0 0)`, with `candidate n 0 0 0` given by (3.13) at
the origin.

**Formalization Note.** `candidate n 0 0 0 ≈ 0.789944` for `n = 3` (so `C_3 ≈ 1.777576`), with the
corrected Corollary 3.5; with the printed one the value would differ. At `n = 2` the same formulas
give exactly `3/4`, the known value. -/
noncomputable def candidate (n : ℕ) (x y z : ℝ) : ℝ :=
  if y < 1 / 2 then U36 n x y z
  else if z ≤ phi n (y - 1 / 2) then U38 n x y z
  else U35 n x y z

end SpiderDiameter


