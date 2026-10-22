-- Prove2me | Definitions.Def_ReferencePricing_PriceMonotone_LemmaThreeCondition
-- name    : ReferencePricing_PriceMonotone_LemmaThreeCondition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T14:56:34.078076+00:00
-- url     : https://prove2.me/theorems/97ebf15e-1aeb-4135-80cb-1de7c5432ffb
-- title:
--   Strong concavity and the three alternative conditions (a) α = 0, (b) D convex in r, (c) Π strongly concave with Π_rr ≥ −K, Π_pr ≥ K/2 of Lemma 3
-- statement:
--   **Strong concavity (Popescu and Wu 2007, p. 419).** A real-valued $\mathcal C^2$ function $f(x, y)$ is **strongly concave** if there exist positive constants $a, b$ such that $f(x, y) + a x^2 + b y^2$ is concave. `IsStronglyConcaveOn f U` states this on a set $U \subseteq \mathbb R^2$: $f$ is $\mathcal C^2$ on $U$, and for some $a, b > 0$ the function $f + a x^2 + b y^2$ is concave on $U$.
--
--   **The conditions of Lemma 3 (p. 420).** For the pricing problem with price set $P = [0, \bar p]$, memory $\alpha$, base demand $d$ and reference effect $R$, `LemmaThreeCondition` holds when *at least one* of the following alternative conditions holds:
--
--   - **(a)** consumers have short memory, $\alpha = 0$ (so $r_{t+1} = p_t$);
--   - **(b)** demand $D(p, r)$, or equivalently the reference effect $R(r-p, r)$, is convex in $r$ on $P$, for every $p \in P$;
--   - **(c)** the short-term profit $\Pi(p, r)$ is strongly concave on the interior $(0, \bar p) \times (0, \bar p)$ of its domain, and there is one global constant $K > 0$ such that, at every interior point,
--   $$\Pi_{rr}(p, r) \ge -K \qquad\text{and}\qquad \Pi_{pr}(p, r) \ge K/2 .$$
--
--   **Formalization Note.** $\Pi_{rr}$ is `partialRR`, the iterated one-variable derivative in $r$. $\Pi_{pr}$ is `partialPR`, the derivative in $p$ followed by the derivative in $r$. On the open square, $\Pi$ is $\mathcal C^2$, so these are the genuine second partials and the order of the mixed partial does not matter. The constant $K$ is quantified before the points, as "global constant" requires. The hypothesis is the disjunction, because the paper calls the three conditions "alternative".
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 419, definition of strong concavity; p. 420, Lemma 3 (a)–(c)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
open RobustBooking.Shared

namespace ReferencePricing.PriceMonotone

/-- Second partial derivative `f_rr(p, r)`, as an iterated one-variable derivative in `r`. -/
noncomputable def partialRR (f : ℝ → ℝ → ℝ) (p r : ℝ) : ℝ :=
  deriv (fun r' => deriv (fun r'' => f p r'') r') r

/-- Mixed partial derivative `f_pr(p, r)`: first in `p`, then in `r`. -/
noncomputable def partialPR (f : ℝ → ℝ → ℝ) (p r : ℝ) : ℝ :=
  deriv (fun r' => deriv (fun p' => f p' r') p) r

/-- Strong concavity, p. 419: "a real-valued `C²` function `f(x, y)` is strongly concave if
there exist positive constants `a` and `b` such that `f(x, y) + a x² + b y²` is concave",
relativized to a set `U ⊆ ℝ²` (the `C²` requirement is part of the page's definition). -/
def IsStronglyConcaveOn (f : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  ContDiffOn ℝ 2 (Function.uncurry f) U ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ConcaveOn ℝ U (fun z : ℝ × ℝ => f z.1 z.2 + a * z.1 ^ 2 + b * z.2 ^ 2)

/-- The three alternative conditions of Lemma 3 (Monotone Price Policy), p. 420, for the
problem with price set `P = [0, p̄]`, memory `α`, base demand `d` and reference effect `R`
(the hypothesis is their disjunction: "each of the following alternative conditions"):
(a) short memory, `α = 0`;
(b) demand `D(p, r)` is convex in `r` on `P`, for every `p ∈ P`;
(c) short-term profit `Π(p, r)` is strongly concave on the interior `(0, p̄) × (0, p̄)` of its
domain, and there is one global constant `K > 0` with `Π_rr(p, r) ≥ −K` and
`Π_pr(p, r) ≥ K/2` on that interior. -/
def LemmaThreeCondition (pbar α : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) : Prop :=
  α = 0 ∨
  (∀ p ∈ Set.Icc (0 : ℝ) pbar,
      ConvexOn ℝ (Set.Icc (0 : ℝ) pbar) (fun r => demand d R p r)) ∨
  (IsStronglyConcaveOn (profit d R) (Set.Ioo (0 : ℝ) pbar ×ˢ Set.Ioo (0 : ℝ) pbar) ∧
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ Set.Ioo (0 : ℝ) pbar ×ˢ Set.Ioo (0 : ℝ) pbar,
      -K ≤ partialRR (profit d R) z.1 z.2 ∧ K / 2 ≤ partialPR (profit d R) z.1 z.2)

end ReferencePricing.PriceMonotone


