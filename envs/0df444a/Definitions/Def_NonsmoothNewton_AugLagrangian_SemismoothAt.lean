-- Prove2me | Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
-- name    : NonsmoothNewton_AugLagrangian_SemismoothAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:48:55.377846+00:00
-- url     : https://prove2.me/theorems/ff3fed1e-977a-425b-b7f1-5a634d8c93fd
-- title:
--   Semismoothness of $F$ at $x$ (Qi–Sun, p. 355)
-- statement:
--   Let $E$, $G$ be real normed spaces, $F : E \to G$ and $x \in E$. We say $F$ is **semismooth at $x$** if $F$ is locally Lipschitz at $x$ (Lipschitz on some neighbourhood of $x$) and, for every direction $h \in E$, the limit
--   $$
--   \lim_{\substack{V \in \partial F(x + t h') \\ h' \to h,\ t \downarrow 0}} \{ V h' \}
--   $$
--   exists, where $\partial F$ is Clarke's generalized Jacobian. Explicitly: there is $L \in G$ such that for every $\varepsilon > 0$ there is $\delta > 0$ with
--   $$
--   \| V h' - L \| < \varepsilon \quad \text{whenever } 0 < t < \delta,\ \|h' - h\| < \delta,\ V \in \partial F(x + t h').
--   $$
--
--   Semismoothness, introduced by Mifflin for functionals and extended by Qi and Sun to vector-valued maps, is the regularity condition under which the generalized-Jacobian Newton method converges superlinearly.
--
--   **Formalization Note** The limit over $V$, $h'$, $t$ is encoded by the explicit $\varepsilon$–$\delta$ condition above, uniform over all $V \in \partial F(x + t h')$. Local Lipschitz continuity is an existential Lipschitz constant on a neighbourhood of $x$.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 355, definition of semismooth (unnumbered)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology

namespace NonsmoothNewton.AugLagrangian

/-- Semismoothness, Qi–Sun (1993), p. 355: `F` is locally Lipschitz at `x` and, for every
direction `h`, the limit `lim_{V ∈ ∂F(x + t h'), h' → h, t ↓ 0} V h'` exists (called `L`). -/
def SemismoothAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  (∃ K : NNReal, ∃ U ∈ 𝓝 x, LipschitzOnWith K F U) ∧
  ∀ h : E, ∃ L : G, ∀ ε > 0, ∃ δ > 0, ∀ (t : ℝ) (h' : E), 0 < t → t < δ → ‖h' - h‖ < δ →
    ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (x + t • h'), ‖V h' - L‖ < ε

end NonsmoothNewton.AugLagrangian


