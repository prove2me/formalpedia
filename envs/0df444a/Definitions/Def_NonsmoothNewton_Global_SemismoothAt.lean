-- Prove2me | Definitions.Def_NonsmoothNewton_Global_SemismoothAt
-- name    : NonsmoothNewton_Global_SemismoothAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:07:01.68357+00:00
-- url     : https://prove2.me/theorems/8d5ee387-3a86-4264-add4-d71574d2dfb1
-- title:
--   Semismooth function at a point (Qi–Sun, p. 355)
-- statement:
--   Let $E$ and $G$ be finite-dimensional real normed spaces and $F : E \to G$. Following Qi and Sun, $F$ is **semismooth at $x$** if
--
--   1. $F$ is Lipschitz on some neighbourhood of $x$, and
--   2. for every direction $h \in E$ the limit
--
--   $$
--   \lim_{\substack{V \in \partial F(x+th') \\ h' \to h,\ t \downarrow 0}} \{ V h' \}
--   $$
--
--   exists, where $\partial F$ is Clarke's generalized Jacobian. Explicitly: there is a vector $L \in G$ such that for every $\varepsilon > 0$ there is $\delta > 0$ with $\|V h' - L\| < \varepsilon$ whenever $0 < t < \delta$, $\|h' - h\| < \delta$ and $V \in \partial F(x + t h')$.
--
--   Semismoothness extends Mifflin's notion from functionals to vector-valued maps. It implies that the directional derivative $F'(x;h)$ exists and equals the limit above (Eq. (2.7)); it is the regularity condition under which the nonsmooth Newton method converges.
--
--   **Formalization Note** The limit over the set-valued index is written in $\varepsilon$–$\delta$ form, uniformly over $V \in \partial F(x+th')$. Local Lipschitzness is an explicit Lipschitz constant on a neighbourhood of $x$.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 355, definition of semismoothness (before Eq. (2.7))

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_clarkeJac

namespace NonsmoothNewton.Global

open Filter Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- `F` is semismooth at `x` (Qi–Sun 1993, p. 355): `F` is locally Lipschitzian at `x` and, for
every direction `h`, the limit of `V h'` over `V ∈ ∂F(x + t h')`, `h' → h`, `t ↓ 0` exists. -/
def SemismoothAt (F : E → G) (x : E) : Prop :=
  (∃ K, ∃ U ∈ 𝓝 x, LipschitzOnWith K F U) ∧
    ∀ h : E, ∃ L : G, ∀ ε > 0, ∃ δ > 0, ∀ (t : ℝ) (h' : E), 0 < t → t < δ → ‖h' - h‖ < δ →
      ∀ V ∈ clarkeJac F (x + t • h'), ‖V h' - L‖ < ε

end NonsmoothNewton.Global


