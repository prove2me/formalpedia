-- Prove2me | Definitions.Def_ParamSDPTraj_Dopt
-- name    : ParamSDPTraj_Dopt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:36.610503+00:00
-- url     : https://prove2.me/theorems/3ec0e9af-f3cf-46f3-a773-012f33eaa869
-- title:
--   Dual optimal set-valued map $\mathcal D^*(t)$
-- statement:
--   The **dual optimal set-valued map** sends $t$ to the set of optimal matrices $Z$ of $(D_t)$:
--
--   $$\mathcal D^*(t)=\{Z\in\mathcal D(t)\mid \exists y\in\mathbb R^m,\ \mathcal A^*(t)[y]+Z=C(t),\ \langle b(t),y\rangle=d^*(t)\},$$
--
--   where $d^*(t)$ is the maximum of $\langle b(t),y\rangle$ over the dual feasible pairs $(y,Z)$.
--
--   **Formalization Note** The condition $\langle b(t),y\rangle=d^*(t)$ is written as maximality over all dual feasible pairs, so no real supremum occurs.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, §2.2, p.7

import Mathlib
import Definitions.Def_ParamSDPTraj_adjA

namespace ParamSDPTraj

/-- **Dual optimal set-valued map 𝒟*.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, §2.2, p.7: "D∗(t) = {Z ∈ D(t) | ⟨b(t), y⟩ = d∗(t), A∗(t)[y] + Z = C(t), y ∈ Rm}", where
d∗(t) is the maximum of ⟨b(t), y⟩ over the dual feasible pairs (y, Z).

**Formalization Note** The set of Z admitting a y with (y, Z) dual feasible and ⟨b(t), y⟩ maximal
over all dual feasible pairs; "= d∗(t)" is written as maximality, so no real supremum occurs. -/
def Dopt {n m : ℕ} (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → Fin m → ℝ)
    (C : ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {Z | ∃ y : Fin m → ℝ, adjA A t y + Z = C t ∧ Z.PosSemidef ∧
    ∀ (y' : Fin m → ℝ) (Z' : Matrix (Fin n) (Fin n) ℝ), adjA A t y' + Z' = C t → Z'.PosSemidef →
      dotProduct (b t) y' ≤ dotProduct (b t) y}

end ParamSDPTraj


