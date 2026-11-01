-- Prove2me | Definitions.Def_ALAVI_Lag
-- name    : ALAVI_Lag
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:38.06023+00:00
-- url     : https://prove2.me/theorems/4726d459-b3d4-47c4-9250-8ec18687f4d4
-- title:
--   The Lagrangian $L_{u^*}(u,p)$ (4)
-- statement:
--   For a fixed point $u^*$, the **Lagrangian** is
--
--   $$
--   L_{u^*}(u,p)=\langle G(u^*),u\rangle+J(u)+\langle p,\Theta(u)\rangle .
--   $$
--
--   **Formalization Note.** $J(u)$ enters as a real number; the statements of the mission evaluate $L_{u^*}$ only at points of $\operatorname{dom}J$.
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, display (4), p.5

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj

namespace ALAVI

/-- **The Lagrangian (4)**, `L_{u*}(w, b) = ⟨G(u*), w⟩ + J(w) + ⟨b, Θ(w)⟩`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, (4), p.5.

Formalization Note: `J(w)` enters as `(J w).toReal`; every statement using `Lag` evaluates it
only at points of `dom J` (the iterates `uᵏ`, `k ≥ 2`, lie in `dom J` whenever `U ∩ dom J` is
nonempty). `u*` is any point of `E`. -/
noncomputable def Lag {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (G : E → E) (J : E → EReal) (Θ : E → F) (ustar w : E) (b : F) : ℝ :=
  inner ℝ (G ustar) w + (J w).toReal + inner ℝ b (Θ w)

end ALAVI


