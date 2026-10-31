-- Prove2me | Definitions.Def_ParamSDPTraj_Popt
-- name    : ParamSDPTraj_Popt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:24.522711+00:00
-- url     : https://prove2.me/theorems/85b30ae4-eab9-466a-95a2-368d0e2f6f22
-- title:
--   Primal optimal set-valued map $\mathcal P^*(t)$
-- statement:
--   The **primal optimal set-valued map** sends $t$ to the set of optimal solutions of $(P_t)$:
--
--   $$\mathcal P^*(t)=\{X\in\mathcal P(t)\mid \langle C(t),X\rangle=p^*(t)\},\qquad p^*(t)=\min_{X\in\mathcal P(t)}\langle C(t),X\rangle.$$
--
--   **Formalization Note** The condition $\langle C(t),X\rangle=p^*(t)$ is written as minimality over $\mathcal P(t)$, so no real infimum occurs. The set is empty when the minimum is not attained.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, §2.2, p.7

import Mathlib
import Definitions.Def_ParamSDPTraj_Pfeas

namespace ParamSDPTraj

/-- **Primal optimal set-valued map 𝒫*.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, §2.2, p.7: "P∗(t) = {X ∈ P(t) | ⟨C(t), X⟩ = p∗(t)}", where p∗(t) is the minimum of
⟨C(t), X⟩ over P(t).

**Formalization Note** "⟨C(t), X⟩ = p∗(t)" is written as minimality over `Pfeas`, so no real
infimum (and no junk value on an empty or unbounded set) occurs. The set is empty when the
minimum is not attained. -/
def Popt {n m : ℕ} (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → Fin m → ℝ)
    (C : ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X ∈ Pfeas A b t ∧ ∀ Y ∈ Pfeas A b t, pair (C t) X ≤ pair (C t) Y}

end ParamSDPTraj


