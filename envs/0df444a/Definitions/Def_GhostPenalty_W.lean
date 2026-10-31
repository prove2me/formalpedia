-- Prove2me | Definitions.Def_GhostPenalty_W
-- name    : GhostPenalty_W
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:43.698632+00:00
-- url     : https://prove2.me/theorems/c7ab7ca1-9b44-45f1-946c-9b2fe74c29c8
-- title:
--   The ghost penalty function $W(x;\varepsilon)$, (24)
-- statement:
--   For a penalty parameter $\varepsilon>0$,
--   $$W(x;\varepsilon)\triangleq f(x)+\frac1\varepsilon\max_i\{g_i(x)_+\}. \tag{24}$$
--   $W$ is the classical nondifferentiable exact penalty function. It is a "ghost": it never appears in Algorithm 1 and is used only in the convergence analysis.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, §1, p.2; (24), p.14

import Mathlib
import Definitions.Def_GhostPenalty_posMax

namespace GhostPenalty

/-- **The ghost penalty function `W(x;ε)`**, (24).
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §1, p.2, and §4, (24), p.14:
"`W(x;ε) ≜ f(x) + (1/ε) max_i {g_i(x)+}`, (24) with a positive penalty parameter `ε`. This
function plays a key role in the subsequent convergence analysis although it does not appear
anywhere in the algorithm itself."

**Formalization Note.** Positivity of `ε` is a hypothesis of every statement using `W`. -/
noncomputable def W {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + (1 / ε) * posMax g x

end GhostPenalty


