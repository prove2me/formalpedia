-- Prove2me | Definitions.Def_TalagrandConc_Penalties_Basic
-- name    : TalagrandConc_Penalties_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:38:25.086907+00:00
-- url     : https://prove2.me/theorems/144a7d95-a460-4fc3-8449-8bf1198f31d8
-- title:
--   The penalized distance $f_h(A,x)$, $v = \max(h, h^{\top})$, $h(\omega,B)$, the transforms $\hat g$ of (2.4.5) and (2.5.7), and the upper integral
-- statement:
--   Let $\Omega$ be a set, $N \ge 0$ an integer, and $h : \Omega \times \Omega \to \mathbb R$ a function (a **penalty**; in the paper $h \ge 0$). This module defines the objects of Sections 2.4–2.5 of Talagrand's 1995 memoir.
--
--   1. **The penalized distance** (2.4.1). For $A \subseteq \Omega^N$ and $x \in \Omega^N$,
--   $$f_h(A,x) = \inf\Big\{ \sum_{i \le N} h(x_i,y_i)\, \mathbf 1_{\{x_i \ne y_i\}} \;;\; y \in A \Big\} \in [0,\infty],$$
--   with the convention $f_h(\emptyset, x) = +\infty$. When $h(\omega,\omega) = 0$ for all $\omega$ (assumption (2.4.2)), the indicator can be dropped and this is (2.4.3). For $h \equiv 1$ off the diagonal, $f_h(A,x)$ is the Hamming distance from $x$ to $A$.
--   2. **The symmetrized penalty** $v(\omega,\omega') = \max(h(\omega,\omega'), h(\omega',\omega))$ of Theorem 2.4.1.
--   3. **The transform** (2.4.5): for $t \in \mathbb R$ and $g : \Omega \to \mathbb R$,
--   $$\hat g(x) = \inf_{y \in \Omega} \big(g(y) + t\,h(x,y)\big).$$
--   4. **The set functional** (2.5.1): for $\omega \in \Omega$ and $B \subseteq \Omega$, $h(\omega,B) = \inf\{h(\omega,\omega') ; \omega' \in B\} \in [0,\infty]$, with $h(\omega,\emptyset) = +\infty$.
--   5. **The level-set transform** (2.5.7): with $B_s = \{g \le s\}$,
--   $$\hat g(x) = \inf_{s > 0} \big(s + t\,h(x,B_s)\big) \in [0,\infty].$$
--   6. **The upper integral** of a function $F : \Omega \to [0,\infty]$ with respect to a measure $\mu$: $\int^* F\,d\mu = \inf\{\int G\,d\mu \,;\, G \text{ measurable},\ F \le G\}$. It coincides with $\int F\, d\mu$ when $F$ is measurable; the paper (pp. 81–82) uses it in place of the integral when measurability fails.
--
--   These objects measure how far a point of a product space is from a set when missing a coordinate costs a coordinate-dependent penalty rather than $1$, and they are the data of every result in Sections 2.4 and 2.5.
--
--   **Formalization Note** $f_h$, $h(\omega,B)$ and the transform (2.5.7) take values in $[0,\infty]$ (`ℝ≥0∞`), computed as infima over the index set, so that an empty index set gives $+\infty$ rather than a junk value. The transform (2.4.5) is a real infimum; in every statement that uses it, $g \ge 0$, $h \ge 0$, $t > 0$ and $\Omega$ is nonempty, so the family is bounded below by $0$ and the real infimum is the true infimum. Points of $\Omega^N$ are functions `Fin N → Ω` (coordinates indexed from $0$).
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 91, Eq. (2.4.1)–(2.4.3); p. 92, Theorem 2.4.1 and Eq. (2.4.5); p. 94, Eq. (2.5.1); p. 95, Eq. (2.5.7); pp. 81–82 (upper integrals)

import Mathlib

open MeasureTheory

namespace TalagrandConc.Penalties

open Classical in
/-- The penalized distance (2.4.1) from `x ∈ Ω^N` to `A ⊆ Ω^N` for a penalty `h : Ω → Ω → ℝ`:
`f_h(A,x) = inf { ∑_{i} h(x_i, y_i) 1_{x_i ≠ y_i} ; y ∈ A }`, computed in `ℝ≥0∞`
(so `f_h(∅, x) = ⊤`). Under (2.4.2) `h(x,x) = 0` this is (2.4.3). -/
noncomputable def fh {Ω : Type*} {N : ℕ} (h : Ω → Ω → ℝ) (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : ENNReal :=
  ⨅ y ∈ A, ∑ i, ENNReal.ofReal (if x i = y i then 0 else h (x i) (y i))

/-- The symmetrized penalty `v(ω, ω') = max(h(ω, ω'), h(ω', ω))` of Theorem 2.4.1. -/
def vmax {Ω : Type*} (h : Ω → Ω → ℝ) (ω ω' : Ω) : ℝ :=
  max (h ω ω') (h ω' ω)

/-- The transform (2.4.5) of Proposition 2.4.2: `ĝ(x) = inf_{y ∈ Ω} (g(y) + t h(x, y))`.
(For `g ≥ 0`, `h ≥ 0`, `t > 0` the family is bounded below by `0`, so the real infimum is the
true infimum whenever `Ω` is nonempty.) -/
noncomputable def ghat {Ω : Type*} (t : ℝ) (h : Ω → Ω → ℝ) (g : Ω → ℝ) (x : Ω) : ℝ :=
  ⨅ y : Ω, (g y + t * h x y)

/-- The functional (2.5.1): `h(ω, B) = inf { h(ω, ω') ; ω' ∈ B }` for `B ⊆ Ω`, computed in
`ℝ≥0∞` (so `h(ω, ∅) = ⊤`). -/
noncomputable def hSet {Ω : Type*} (h : Ω → Ω → ℝ) (ω : Ω) (B : Set Ω) : ENNReal :=
  ⨅ ω' ∈ B, ENNReal.ofReal (h ω ω')

/-- The transform (2.5.7) of Proposition 2.5.2: with `B_s = {g ≤ s}`,
`ĝ(x) = inf_{s > 0} (s + t h(x, B_s))`, computed in `ℝ≥0∞`. -/
noncomputable def ghatLevel {Ω : Type*} (t : ℝ) (h : Ω → Ω → ℝ) (g : Ω → ℝ) (x : Ω) : ENNReal :=
  ⨅ s : ℝ, ⨅ (_ : 0 < s), ENNReal.ofReal s + ENNReal.ofReal t * hSet h x {y | g y ≤ s}

/-- The upper integral `∫* F dμ = inf { ∫ G dμ ; G measurable, F ≤ G }` of a possibly
non-measurable `F : Ω → ℝ≥0∞` (pp. 81–82). It equals `∫⁻ F dμ` when `F` is measurable. -/
noncomputable def upperLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → ENNReal) : ENNReal :=
  ⨅ (G : Ω → ENNReal) (_ : Measurable G) (_ : F ≤ G), ∫⁻ x, G x ∂μ

end TalagrandConc.Penalties


