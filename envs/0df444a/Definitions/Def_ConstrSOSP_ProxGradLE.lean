-- Prove2me | Definitions.Def_ConstrSOSP_ProxGradLE
-- name    : ConstrSOSP_ProxGradLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:38.177977+00:00
-- url     : https://prove2.me/theorems/a3af8c25-5d82-470e-a732-85b16be9989c
-- title:
--   Proximal-gradient bound $\|g_\pi(x)\|\le\varepsilon$
-- statement:
--   The **proximal gradient** of $f$ at $x$ with smoothness constant $L_1$ is
--   $$
--   g_\pi(x)=L_1\Big(\pi_{\mathcal X}\big(x-\tfrac1{L_1}\nabla f(x)\big)-x\Big).
--   $$
--   The predicate says $\|g_\pi(x)\|\le\varepsilon$, with the gradient value $g=\nabla f(x)$ given as data.
--
--   **Formalization Note** The projection is existential; for nonempty closed convex $\mathcal X$ it is unique, so this is the paper's condition.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), (Prox-Gradient), p.19

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ConstrSOSP_IsProj

namespace ConstrSOSP

/-- **The proximal-gradient bound `‖g_π(x)‖ ≤ ε`** (arXiv:2604.02285, 2 Nov 2026,
(Prox-Gradient), p.19: "g_π(x) := L₁ · (π_X(x − (1/L₁)∇f(x)) − x), with
π_X(v) := arg min_{w∈X} ‖w − v‖²").

`ProxGradLE X L1 g x ε` holds iff the Euclidean projection `w` of `x − (1/L₁) g` onto `X`
satisfies `L₁ ‖w − x‖ ≤ ε`; here `g` is the gradient value `∇f(x)`.

**Formalization Note** Written with an existential projection (`IsProj`); for a nonempty closed
convex `X` the projection is unique, so this is the paper's `‖g_π(x)‖ ≤ ε`. The objective enters
only through the gradient value `g`. -/
def ProxGradLE {d : ℕ} (X : Set (Fin d → ℝ)) (L1 : ℝ) (g x : Fin d → ℝ) (ε : ℝ) : Prop :=
  ∃ w, IsProj X (x - L1⁻¹ • g) w ∧ L1 * ApproxVI.euclNorm (w - x) ≤ ε

end ConstrSOSP


