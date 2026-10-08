-- Prove2me | Definitions.Def_ConjugateConvex_Involution_IsClosedConvexPair
-- name    : ConjugateConvex_Involution_IsClosedConvexPair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:24:42.016526+00:00
-- url     : https://prove2.me/theorems/90b1dbda-5a96-46d1-9bfd-46397cac104a
-- title:
--   §2 — G convex and nonempty, f convex and semi-continuous from below on G, G closed relative to f
-- statement:
--   Let $\mathbb R^n$ carry its Euclidean topology. A pair $(G, f)$ consisting of a set $G \subseteq \mathbb R^n$ and a real function $f$ defined in $G$ belongs to the **standing class** of Fenchel's theorem when all of the following hold:
--
--   1. $G$ is nonempty;
--   2. $G$ is convex and $f$ is convex on $G$: for $x', x'' \in G$ and $0 < \theta < 1$,
--   $$
--   f\bigl((1-\theta)x' + \theta x''\bigr) \le (1-\theta) f(x') + \theta f(x'');
--   $$
--   3. $f$ is semi-continuous from below on $G$: for every $x^* \in G$, $\liminf_{x \to x^*,\, x \in G} f(x) \ge f(x^*)$;
--   4. $G$ is closed relative to $f$: at every boundary point $x^*$ of $G$ which does not belong to $G$ (every point of $\overline G \setminus G$), $f(x) \to +\infty$ as $x \to x^*$ within $G$.
--
--   Fenchel's theorem says that conjugation maps this class to itself and is an involution on it. Condition 4 is what makes the conjugate of the conjugate recover the domain $G$ and not only the values of $f$.
--
--   **Formalization Note** Points of $\mathbb R^n$ are `Fin n → ℝ`, whose product topology is the Euclidean one. $f$ is a total function `(Fin n → ℝ) → ℝ`, and no clause looks at its values off $G$: convexity is `ConvexOn ℝ G f` (which contains the convexity of $G$), semi-continuity is `LowerSemicontinuousOn f G` (neighbourhoods within $G$), and the blow-up is `Tendsto f (𝓝[G] x) atTop` for `x ∈ closure G \ G`. Nonemptiness of $G$ is not written in the paper's §2; it is tacit there (the paper proves that the conjugate set is nonempty, and the theorem asks the conjugate pair to have "exactly the same properties"), and it is stated explicitly here.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), pp. 74–75, §2 (definition (2), the remark after (4)) and the hypothesis of the Theorem, §3, p. 75

import Mathlib

open Filter Topology

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §2, pp. 74–75: the standing class of the theorem. `G ⊆ ℝⁿ` is a nonempty
convex set, `f` (only its values on `G` matter) is convex on `G` and semi-continuous from below
on `G`, and `G` is closed relative to `f`: at every boundary point of `G` not belonging to `G`
(i.e. every point of `closure G \ G`), `f(x) → ∞` as `x → x*` inside `G`. -/
def IsClosedConvexPair {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  G.Nonempty ∧ ConvexOn ℝ G f ∧ LowerSemicontinuousOn f G ∧
    ∀ x ∈ closure G \ G, Tendsto f (𝓝[G] x) atTop

end ConjugateConvex.Involution


