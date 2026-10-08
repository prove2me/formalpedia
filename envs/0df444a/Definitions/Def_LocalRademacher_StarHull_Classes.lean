-- Prove2me | Definitions.Def_LocalRademacher_StarHull_Classes
-- name    : LocalRademacher_StarHull_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:09:10.064987+00:00
-- url     : https://prove2.me/theorems/31780891-8288-4a6b-80a4-e96e9d346c3e
-- title:
--   §2 p. 7 and §3.2 p. 14 — the star-hull star(F, f₀), the local class {f ∈ star(F,0) : T(f) ≤ r} and the rescaled class G̃ᵣ = {rf/(T(f) ∨ r) : f ∈ F}
-- statement:
--   Let $\mathcal X$ be a set and $\mathcal F$ a class of real-valued functions on $\mathcal X$.
--
--   1. The **star-hull** of $\mathcal F$ around a function $f_0$ is
--   $$
--   \operatorname{star}(\mathcal F, f_0) = \{ f_0 + \alpha (f - f_0) : f \in \mathcal F,\ \alpha \in [0,1] \}.
--   $$
--   2. For a functional $T$ (a real number $T(g)$ for every real function $g$ on $\mathcal X$) and a level $r$, the **local class** of the star-hull around $0$ is
--   $$
--   \{ g \in \operatorname{star}(\mathcal F, 0) : T(g) \le r \}.
--   $$
--   3. For the same $T$ and $r > 0$, the **rescaled class** is
--   $$
--   \tilde{\mathcal G}_r = \left\{ \frac{r f}{T(f) \vee r} : f \in \mathcal F \right\},
--   $$
--   where $u \vee v = \max\{u, v\}$. When $T(f) \ge 0$, the factor $r/(T(f) \vee r)$ lies in $(0,1]$: it equals $1$ when $T(f) \le r$ and scales $f$ down to "size" $r$ otherwise.
--
--   These are the classes over which the local Rademacher averages are taken in the second part of Theorem 3.3 of Bartlett, Bousquet and Mendelson: the hypothesis bounds the Rademacher average of the local class, and the proof concentrates the empirical process indexed by $\tilde{\mathcal G}_r$.
--
--   **Formalization Note** $T$ is a function on all real functions on $\mathcal X$ (the paper's $T : \mathcal F \to \mathbb R^+$ is evaluated on the star-hull as well), and no condition on $T$ is built into the definitions; the theorems state which values of $T$ are constrained. The star-hull keeps the general centre $f_0$ of p. 7; the theorems use the zero function. The definition of $\tilde{\mathcal G}_r$ is used only with $r > 0$.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, §2 p. 7 (star-hull); Theorem 3.3 part 2, p. 10 (the class {f ∈ star(F,0) : T(f) ≤ r}); §3.2 p. 14 (G̃ᵣ)

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk

namespace LocalRademacher.StarHull

/-- The **star-hull** of a class `F` of real functions on `X` around `f₀` (Bartlett, Bousquet and
Mendelson, §2, p. 7): `star(F, f₀) = {f₀ + α (f − f₀) : f ∈ F, α ∈ [0, 1]}`. -/
def starHull {X : Type*} (F : Set (X → ℝ)) (f₀ : X → ℝ) : Set (X → ℝ) :=
  {g | ∃ f ∈ F, ∃ α ∈ Set.Icc (0 : ℝ) 1, g = fun x => f₀ x + α * (f x - f₀ x)}

/-- The **local subclass** `{f ∈ star(F, 0) : T(f) ≤ r}` of the star-hull of `F` around the zero
function (Theorem 3.3, part 2, p. 10), for a functional `T` defined on all real functions. -/
def localClass {X : Type*} (F : Set (X → ℝ)) (T : (X → ℝ) → ℝ) (r : ℝ) : Set (X → ℝ) :=
  {g | g ∈ starHull F 0 ∧ T g ≤ r}

/-- The **rescaled class** `G̃ᵣ = {r f / (T(f) ∨ r) : f ∈ F}` (§3.2, p. 14), with `∨` the maximum.
Wherever it is used, `r > 0` is assumed, so the factor `r / (T(f) ∨ r)` lies in `(0, 1]` when
`T(f) ≥ 0`. -/
def tildeG {X : Type*} (F : Set (X → ℝ)) (T : (X → ℝ) → ℝ) (r : ℝ) : Set (X → ℝ) :=
  {g | ∃ f ∈ F, g = fun x => (r / max (T f) r) * f x}

end LocalRademacher.StarHull


