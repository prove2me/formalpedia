-- Prove2me | Definitions.Def_GoldieRenewal_Implicit_DRi
-- name    : GoldieRenewal_Implicit_DRi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:00.429976+00:00
-- url     : https://prove2.me/theorems/941b2333-f5a5-44db-b524-06957783dc65
-- title:
--   The smoothing f̌(t) = ∫_{−∞}^t e^{−(t−u)} f(u) du (p. 128) and direct Riemann integrability (Feller XI.1)
-- statement:
--   **Smoothing** (p. 128). For $f:\mathbb R\to\mathbb R$,
--   $$
--   \check f(t) := \int_{-\infty}^t e^{-(t-u)} f(u)\,du,\qquad t\in\mathbb R .
--   $$
--   It is the convolution of $f$ with the kernel $K(t) = e^{-t}\mathbf 1_{t>0}$ (p. 145).
--
--   **Direct Riemann integrability** (dRi). The paper uses this notion (Lemmas 9.1, 9.2 and the key renewal theorem) without defining it; the definition is that of Feller (1971), Vol. II, §XI.1. For a mesh $h>0$ and $n\in\mathbb Z$ let $I_{n,h} = [nh,(n+1)h]$. A function $f$ is *directly Riemann-integrable* if
--
--   1. for every $h>0$, $\sum_{n\in\mathbb Z}\sup_{I_{n,h}}|f| < \infty$, and
--   2. $h\sum_{n\in\mathbb Z}\bigl(\sup_{I_{n,h}} f - \inf_{I_{n,h}} f\bigr)\to 0$ as $h\downarrow 0$.
--
--   Condition 1 makes the upper and lower Riemann sums over the whole line absolutely convergent; condition 2 says that they have a common limit. dRi functions are the ones to which the key renewal theorem applies.
--
--   **Formalization Note** The cell suprema and oscillations are computed in $[0,\infty]$, so a function unbounded on a cell gives $\infty$ and fails condition 1, instead of producing a junk real supremum. Finiteness of the series in 1 for one mesh implies it for every mesh. $\check f$ is a Bochner integral over $(-\infty,t]$; every statement applies it to a function for which the integral converges absolutely (an $L^1$ function, or the tail function $r$, which is bounded by $e^{\kappa u}$).
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 128 (§1, definition of f̌), p. 143 (Lemmas 9.1–9.2, dRi); dRi as in Feller, An Introduction to Probability Theory and Its Applications, Vol. II, 2nd ed. (1971), §XI.1

import Mathlib

namespace GoldieRenewal.Implicit

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **The smoothing `f̌`** (Goldie 1991, §1, p. 128):
`f̌(t) := ∫_{−∞}^t e^{−(t−u)} f(u) du`, `t ∈ ℝ`.

**Formalization Note** The integral is a Bochner integral over `(−∞, t]` with respect to Lebesgue
measure. It is the paper's value whenever `u ↦ e^{−(t−u)} f(u)` is integrable on `(−∞, t]`, which
holds for every `t` when `f ∈ L¹(ℝ)` (the kernel is at most `1` there) and for the tail functions
`r` of the mission (they are bounded by `e^{κu}` and the kernel decays). Every statement of the
mission applies it only to such functions. -/
noncomputable def smooth (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in Set.Iic t, Real.exp (-(t - u)) * f u

/-- The closed cell `[n h, (n+1) h]` of the grid of mesh `h`. -/
def cell (h : ℝ) (n : ℤ) : Set ℝ :=
  Set.Icc ((n : ℝ) * h) (((n : ℝ) + 1) * h)

/-- `sup_{[nh,(n+1)h]} |f|`, computed in `[0, ∞]` (it is `∞` if `f` is unbounded on the cell). -/
noncomputable def cellSupAbs (f : ℝ → ℝ) (h : ℝ) (n : ℤ) : ℝ≥0∞ :=
  ⨆ x ∈ cell h n, ENNReal.ofReal |f x|

/-- The oscillation `sup_{[nh,(n+1)h]} f − inf_{[nh,(n+1)h]} f`, computed in `[0, ∞]` as
`sup_{x, y ∈ cell} (f x − f y)⁺` (it is `∞` if `f` is unbounded on the cell). -/
noncomputable def cellOsc (f : ℝ → ℝ) (h : ℝ) (n : ℤ) : ℝ≥0∞ :=
  ⨆ x ∈ cell h n, ⨆ y ∈ cell h n, ENNReal.ofReal (f x - f y)

/-- **Direct Riemann integrability** (dRi), the notion used in Lemmas 9.1–9.2 of Goldie (1991,
p. 143) and in the key renewal theorem. The paper does not define it; this is the definition of
Feller (1971), *An Introduction to Probability Theory and Its Applications*, Vol. II, §XI.1:
`f : ℝ → ℝ` is directly Riemann-integrable when

1. for every mesh `h > 0` the series `Σ_{n∈ℤ} sup_{[nh,(n+1)h]} |f|` converges (so the upper and
   lower Riemann sums `h Σ_n sup_{[nh,(n+1)h]} f` and `h Σ_n inf_{[nh,(n+1)h]} f` over the whole
   line converge absolutely), and
2. the difference of the upper and lower sums, `h Σ_{n∈ℤ} (sup_{[nh,(n+1)h]} f − inf_{[nh,(n+1)h]} f)`,
   tends to `0` as `h ↓ 0`.

**Formalization Note** Suprema and oscillations are computed in `[0, ∞]`, so an unbounded cell gives
`∞` rather than a junk real value, and condition 1 then fails. Finiteness of the series for one mesh
implies it for every mesh, so "for every `h > 0`" is not a strengthening of Feller's definition. -/
def IsDRi (f : ℝ → ℝ) : Prop :=
  (∀ h : ℝ, 0 < h → ∑' n : ℤ, cellSupAbs f h n < ∞) ∧
    Tendsto (fun h : ℝ => ENNReal.ofReal h * ∑' n : ℤ, cellOsc f h n) (𝓝[>] 0) (𝓝 0)

end GoldieRenewal.Implicit


