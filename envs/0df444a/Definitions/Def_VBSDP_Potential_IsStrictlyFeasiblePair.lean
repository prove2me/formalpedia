-- Prove2me | Definitions.Def_VBSDP_Potential_IsStrictlyFeasiblePair
-- name    : VBSDP_Potential_IsStrictlyFeasiblePair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:41.625587+00:00
-- url     : https://prove2.me/theorems/0385e107-2496-4953-ae5a-7550c0e66a57
-- title:
--   Strictly feasible primal-dual pair
-- statement:
--   For the primal affine matrix $F(x)$ and a dual matrix $Z$, the pair $(x,Z)$ is **strictly feasible** when $F(x)$ and $Z$ are positive definite and the dual equations hold:
--
--   $$F(x)\succ0,\qquad Z\succ0,\qquad \operatorname{Tr}(F_iZ)=c_i\quad(1\le i\le m).$$
--
--   This predicate specifies the domain visited by the potential reduction iterates. It also makes the determinants and trace in the logarithmic potential strictly positive when $n\ge1$.
--
--   **Formalization Note** Mathlib's `PosDef` includes symmetry. The $m$ indexed matrices use zero-based `Fin m`, while $F_0$ is separate.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 70 (PDF p. 22), §4 standing assumptions; p. 77 (PDF p. 29), text before (56), https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_lmi

namespace VBSDP.Potential

/-- Strict primal and dual feasibility for the pair in Sections 4–5. -/
def IsStrictlyFeasiblePair {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (VBSDP.Duality.lmi F₀ F x).PosDef ∧ Z.PosDef ∧ ∀ i, (F i * Z).trace = c i

end VBSDP.Potential


