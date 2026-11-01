-- Prove2me | Definitions.Def_MeanFieldContest_EnvelopeObjects
-- name    : MeanFieldContest_EnvelopeObjects
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:48.6165+00:00
-- url     : https://prove2.me/theorems/c5388d73-802e-4ab3-916d-a35da693cc94
-- title:
--   Auxiliary objects of §3: $F^{-1}$, $F^{-1}(y+)$, $J(g)$, $h(\infty)$, $h^{-1}$, $\Phi(F)$, $\bar w_F$, $\bar y$, $\mathcal F^\prime$, $A_y$, $A$, $w_y$
-- statement:
--   The objects of the uniqueness proof of Nutz and Zhang. The goal theorem does not use them.
--
--   1. **Quantiles.** $F^{-1}(y)=\inf\{x:F(x)\ge y\}$ and $F^{-1}(y+)=\inf\{x:F(x)>y\}$.
--   2. **Jumps.** $J(g):=\{y\in(0,1):g(y-)<g(y+)\}$.
--   3. **Scale at infinity.** $h(\infty):=\sup_{x\ge0}h(x)\in(1,\infty]$, $D:=[0,h(\infty)]\cap\mathbb R$, and $h^{-1}:[0,h(\infty))\to[0,\infty)$.
--   4. **Transformed functions.** $F\circ h^{-1}$ and $\xi^F\circ h^{-1}$ on $D$, with $F\circ h^{-1}(h(\infty)):=1$ and $\xi^F\circ h^{-1}(h(\infty)):=g(1)$ when $h(\infty)<\infty$, and $\Phi(F):=g\circ F\circ h^{-1}$.
--   5. **The set $\mathcal F'$.** With
--   $$\bar w_F:=\inf\{w\in[0,h(\infty)]:\Phi(F)(w)=g(1)\},\qquad\bar y:=\inf\{y\in[0,1]:g(y)=g(1)\},$$
--   $\mathcal F':=\{F\in\mathcal F:\bar w_F>1$, and $\bar w_F<h(\infty)$ in case $\bar y<1\}$.
--   6. **Level sets.** $A_y=\{w\in D:F\circ h^{-1}(w)=y\}$, $A=\bigcup_{y\notin J(g)}A_y$, $w_y=\inf A_y$.
--
--   Passing to the scale $w=h(x)$ turns the player's problem into a concave envelope, and these objects describe the minimizer of that envelope.
--
--   **Formalization Note** $\bar w_F$ and $h(\infty)$ live in the extended reals, where $\inf\emptyset=+\infty$, which is $h(\infty)$ in the only case in which no real $w$ qualifies. Only order comparisons are made with them.
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, §3.1, F⁻¹ p.8, J(g) p.10; §3.2, Φ(F), w̄_F, ȳ, 𝓕′ p.12; Lemma 3.9, A, A_y, w_y p.15

import Mathlib
import Definitions.Def_MeanFieldContest_Model

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MeanFieldContest

/-- The left-continuous inverse (quantile function) `F⁻¹(y) = inf{x : F(x) ≥ y}`,
arXiv:2103.04219v1, §3.1, p.8.

**Formalization Note.** The real `sInf` is `0` on an empty or unbounded-below set: at `y = 0` the
paper's value is `−∞`, and at `y = 1` the set may be empty. Every statement using `quantile` either
asserts nonemptiness of the set or takes the maximum with `0`, as Remark 3.3 does. -/
noncomputable def quantile (F : Measure ℝ) (y : ℝ) : ℝ := sInf {x | y ≤ cdf F x}

/-- `F⁻¹(y+) = inf{x : F(x) > y}`, the right limit of the quantile function,
arXiv:2103.04219v1, §3.1, p.8 (it is the right-continuous inverse `F⁻¹₊` of §4, p.17).
For a distribution on `[0,∞)` and `0 ≤ y < 1` the set is nonempty and bounded below by `0`. -/
noncomputable def quantileRight (F : Measure ℝ) (y : ℝ) : ℝ := sInf {x | y < cdf F x}

/-- `J(g) := {y ∈ (0,1) : g(y−) < g(y+)}`, the interior jump points of `g`,
arXiv:2103.04219v1, §3.1, p.10.

**Formalization Note.** At an interior point the monotone `g` has both one-sided limits, which
`Function.leftLim` and `Function.rightLim` return. -/
def jumpSet (R : ℝ → ℝ) : Set ℝ :=
  {y | y ∈ Ioo (0 : ℝ) 1 ∧ Function.leftLim (g R) y < Function.rightLim (g R) y}

/-- `h(∞) := sup_{x ≥ 0} h(x)`, arXiv:2103.04219v1, §3 (first used p.6): `+∞` if `µ ≤ 0`, and
`1/(1 − exp(−2µx₀/σ²))` if `µ > 0`.

**Formalization Note.** A supremum in `EReal`, a complete lattice, so it has no junk value. Only
order comparisons with it are used, never arithmetic. -/
noncomputable def hInfty (x₀ μ σ : ℝ) : EReal :=
  ⨆ x : Ici (0 : ℝ), ((scale x₀ μ σ x : ℝ) : EReal)

/-- The domain `D := [0, h(∞)] ∩ ℝ` of `Φ(F)` and of the concave envelopes,
arXiv:2103.04219v1, §3.2, pp.12, 15. It contains `h(∞)` exactly when `µ > 0`. -/
def hDomain (x₀ μ σ : ℝ) : Set ℝ := {w | 0 ≤ w ∧ (w : EReal) ≤ hInfty x₀ μ σ}

/-- `h⁻¹ : [0, h(∞)) → [0, ∞)`, the inverse of the strictly increasing scale function.

**Formalization Note.** Outside the range of `h` on `[0,∞)` the value is not meaningful; the only
such point of `hDomain` is `h(∞)` for `µ > 0`, which `cdfScale` and `xiScale` treat separately. -/
noncomputable def scaleInv (x₀ μ σ w : ℝ) : ℝ := Function.invFunOn (scale x₀ μ σ) (Ici 0) w

open Classical in
/-- `F ∘ h⁻¹` on `D`, with `F ∘ h⁻¹(h(∞)) := 1` when `h(∞) < ∞`, arXiv:2103.04219v1, §3.2. -/
noncomputable def cdfScale (x₀ μ σ : ℝ) (F : Measure ℝ) (w : ℝ) : ℝ :=
  if (w : EReal) = hInfty x₀ μ σ then 1 else cdf F (scaleInv x₀ μ σ w)

open Classical in
/-- `ξ^F ∘ h⁻¹` on `D`, with value `g(1)` at `h(∞)` when `h(∞) < ∞` (its limit under the reward
assumptions), arXiv:2103.04219v1, §3.2, p.12. -/
noncomputable def xiScale (x₀ μ σ : ℝ) (R : ℝ → ℝ) (F : Measure ℝ) (w : ℝ) : ℝ :=
  if (w : EReal) = hInfty x₀ μ σ then g R 1 else xi R F (scaleInv x₀ μ σ w)

/-- `Φ(F) := g ∘ F ∘ h⁻¹`, arXiv:2103.04219v1, §3.2, p.12. -/
noncomputable def Phi (x₀ μ σ : ℝ) (R : ℝ → ℝ) (F : Measure ℝ) (w : ℝ) : ℝ :=
  g R (cdfScale x₀ μ σ F w)

/-- `w̄_F := inf{w ∈ [0, h(∞)] : Φ(F)(w) = g(1)} ≤ h(∞)`, arXiv:2103.04219v1, §3.2, p.12.

**Formalization Note.** In `EReal`, with `inf ∅ = ⊤`, which is `h(∞)` in the only case where the
set of real `w` can be empty (`h(∞) = ∞`). -/
noncomputable def wBar (x₀ μ σ : ℝ) (R : ℝ → ℝ) (F : Measure ℝ) : EReal :=
  sInf ((fun w : ℝ => (w : EReal)) '' {w | w ∈ hDomain x₀ μ σ ∧ Phi x₀ μ σ R F w = g R 1})

/-- `ȳ := inf{y ∈ [0,1] : g(y) = g(1)}`, arXiv:2103.04219v1, §3.2, p.12. The set contains `1`. -/
noncomputable def yBar (R : ℝ → ℝ) : ℝ := sInf {y | y ∈ Icc (0 : ℝ) 1 ∧ g R y = g R 1}

/-- `𝓕′ := {F ∈ 𝓕 : w̄_F > 1, and w̄_F < h(∞) in case ȳ < 1}`, arXiv:2103.04219v1, §3.2, p.12. -/
def feasibleLawsPrime (x₀ μ σ : ℝ) (R : ℝ → ℝ) : Set (Measure ℝ) :=
  {F | F ∈ feasibleLaws x₀ μ σ ∧ 1 < wBar x₀ μ σ R F ∧
    (yBar R < 1 → wBar x₀ μ σ R F < hInfty x₀ μ σ)}

/-- `A_y = {w ∈ [0, h(∞)] ∩ ℝ : F ∘ h⁻¹(w) = y}`, arXiv:2103.04219v1, Lemma 3.9, p.15. -/
def levelA (x₀ μ σ : ℝ) (F : Measure ℝ) (y : ℝ) : Set ℝ :=
  {w | w ∈ hDomain x₀ μ σ ∧ cdfScale x₀ μ σ F w = y}

/-- `A = ⋃_{y ∉ J(g)} A_y`, arXiv:2103.04219v1, Lemma 3.9, p.15. -/
def unionA (x₀ μ σ : ℝ) (R : ℝ → ℝ) (F : Measure ℝ) : Set ℝ :=
  ⋃ y ∈ (jumpSet R)ᶜ, levelA x₀ μ σ F y

/-- `w_y = inf A_y`, arXiv:2103.04219v1, Lemma 3.9, p.15. It is used for `y ∈ J(g)`, where `A_y`
is nonempty (it has positive length by Lemma 3.6) and bounded below by `0`. -/
noncomputable def wLevel (x₀ μ σ : ℝ) (F : Measure ℝ) (y : ℝ) : ℝ := sInf (levelA x₀ μ σ F y)

end MeanFieldContest


