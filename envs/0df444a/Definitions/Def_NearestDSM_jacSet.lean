-- Prove2me | Definitions.Def_NearestDSM_jacSet
-- name    : NearestDSM_jacSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:29.085818+00:00
-- url     : https://prove2.me/theorems/e162d626-f4f2-41f9-9eb3-7e1fccba34e6
-- title:
--   The generalized Jacobian $\partial F(y)$ in the form (2.7)
-- statement:
--   The generalized Jacobian of $F$ at $y$ is the set
--   $$
--   \partial F(y)=\{A\,\mathrm{Diag}(\mathrm{vec}(M))A^T \mid M\in\mathcal M(y)\}=\{V(M)\mid M\in\mathcal M(y)\}.
--   $$
--
--   The local estimate (3.25) and Corollary 3.11 are stated in terms of this set.
--
--   **Formalization Note** The paper introduces $\partial F(y)$ as Clarke's generalized Jacobian and states the formula above as its value for this $F$. The mission takes the formula as the definition and does not formalize Clarke's construction.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, display (2.7), p.8; Clarke's definition (1.7), p.5

import Mathlib
import Definitions.Def_NearestDSM_Mset
import Definitions.Def_NearestDSM_Vmat

namespace NearestDSM

/-- The generalized Jacobian `∂F(y) = {A Diag(vec(M)) Aᵀ | M ∈ M(y)}` of `F`, in the form
computed in Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, display (2.7), p.8.

**Formalization Note.** The paper introduces `∂F(y)` as Clarke's generalized Jacobian (1.7), p.5,
and states (2.7) as its value for this `F`. The mission encodes `∂F(y)` by the formula (2.7); it
does not formalize Clarke's definition. -/
def jacSet {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) :
    Set (Matrix (Fin (n + 1) ⊕ Fin n) (Fin (n + 1) ⊕ Fin n) ℝ) :=
  Vmat '' Mset Xh y

end NearestDSM


