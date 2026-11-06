-- Prove2me | Definitions.Def_ConstrSOSP_IsApproxKKT
-- name    : ConstrSOSP_IsApproxKKT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:48.428296+00:00
-- url     : https://prove2.me/theorems/4c90aa9e-8606-4fc2-b166-5cb68b28695d
-- title:
--   $\varepsilon$-approximate KKT point
-- statement:
--   A point $x$ is an **$\varepsilon$-approximate KKT point** if $x\in\mathcal X$ and $\|g_\pi(x)\|\le\varepsilon$, the proximal gradient being taken with smoothness constant $L_1$ (Corollary 5.6: "The proximal gradient uses smoothness bound 1"). The gradient value $g=\nabla f(x)$ is given as data.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.4 (5a), p.19; Corollary 5.6, p.55

import Mathlib
import Definitions.Def_ConstrSOSP_Poly
import Definitions.Def_ConstrSOSP_ProxGradLE

namespace ConstrSOSP

/-- **ε-approximate KKT point** (arXiv:2604.02285, 2 Nov 2026, Definition 4.4 (5a), p.19, and
Corollary 5.6, p.55: "every ϵ-approximate KKT point … The proximal gradient uses smoothness
bound 1").

`IsApproxKKT A b L1 ε x g` holds iff `x ∈ X = {Ax ≤ b}` and `‖g_π(x)‖ ≤ ε`, the proximal gradient
being formed with the smoothness constant `L₁` and the gradient value `g = ∇f(x)`. -/
def IsApproxKKT {m d : ℕ} (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (L1 ε : ℝ)
    (x g : Fin d → ℝ) : Prop :=
  x ∈ Poly A b ∧ ProxGradLE (Poly A b) L1 g x ε

end ConstrSOSP


