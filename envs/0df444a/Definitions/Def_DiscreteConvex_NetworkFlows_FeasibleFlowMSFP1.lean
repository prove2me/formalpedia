-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_FeasibleFlowMSFP1
-- name    : DiscreteConvex_NetworkFlows_FeasibleFlowMSFP1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:15:01.270374+00:00
-- url     : https://prove2.me/theorems/01cc010e-bcaa-489e-9aa3-a50dd5f0b837
-- title:
--   Feasibility for the submodular flow problem MSFP1 (Eqs. 9.52-9.53)
-- statement:
--   A flow $\xi : A \to \mathbb R$ is **feasible for MSFP1** with upper capacity $\bar c$, lower capacity $\underline c$, and submodular function $\rho$ if it meets the capacity constraint (9.52) and its boundary lies in the base polyhedron $B(\rho)$ (9.53), i.e. $\partial\xi(X) \le \rho(X)$ for every $X \subseteq V$ and $\partial\xi(V) = 0$ — stated directly via these defining inequalities rather than through a separately formalized base-polyhedron object, to keep this mission self-contained (see `MODERATION_NOTES.md`).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.258, Eqs. (9.52)-(9.53).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.258, Eqs. (9.52)-(9.53)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_Boundary

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.258, Eqs. (9.52)-(9.53): feasibility for the
submodular flow problem MSFP1, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- A flow `ξ : A → ℝ` is **feasible for MSFP1** with upper capacity `c̄`, lower capacity `c`,
and submodular function `ρ` if it meets the capacity constraint (9.52) and its boundary lies
in the base polyhedron `B(ρ)` (9.53), i.e. `∂ξ(X) ≤ ρ(X)` for every `X ⊆ V` and `∂ξ(V) = 0`. -/
def FeasibleFlowMSFP1 {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (ρ : Finset V → WithTop ℝ) (ξ : A → ℝ) : Prop :=
  (∀ a : A, cLower a ≤ (ξ a : WithBot ℝ) ∧ (ξ a : WithTop ℝ) ≤ cUpper a) ∧
    (∀ X : Finset V, ((∑ v ∈ X, Boundary tail head ξ v : ℝ) : WithTop ℝ) ≤ ρ X) ∧
    (∑ v : V, Boundary tail head ξ v) = 0

end DiscreteConvex.NetworkFlows


