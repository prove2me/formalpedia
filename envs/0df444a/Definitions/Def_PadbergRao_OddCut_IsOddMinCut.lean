-- Prove2me | Definitions.Def_PadbergRao_OddCut_IsOddMinCut
-- name    : PadbergRao_OddCut_IsOddMinCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:38:55.807843+00:00
-- url     : https://prove2.me/theorems/40013e8b-023a-4e95-b97d-7745673a1aca
-- title:
--   Odd sets $\lambda(U)$ odd, and odd minimum cut-sets (problem (1.1))
-- statement:
--   Let $V_1 \subseteq V$ be the set of nodes labelled **odd**. For $U \subseteq V$ the total label $\lambda(U)$ is **odd** if $U$ contains an odd number of odd-labelled nodes, i.e. $|U \cap V_1|$ is odd, and **even** otherwise; in particular the empty set has even label. A cut-set $(U : V - U)$ is **odd** if $\lambda(U)$ is odd.
--
--   A set $X \subseteq V$ defines an **odd minimum cut-set** $(X : V - X)$ if $\lambda(X)$ is odd and
--
--   $$
--   c(X : V - X) \;=\; \min\{\, c(U : V - U) \;:\; U \subseteq V,\ \lambda(U) \text{ odd} \,\},
--   $$
--
--   that is, $c(X : V - X) \le c(U : V - U)$ for every $U \subseteq V$ with $\lambda(U)$ odd. Finding such an $X$ is the odd minimum cut-set problem (1.1) of Padberg and Rao; it is the separation problem for Edmonds' blossom inequalities.
--
--   **Formalization Note** $\lambda(U)$ odd is `IsOddSet odd U := Odd (U ∩ odd).card`. The minimum is stated as a lower bound against every odd competitor $U$ (no real infimum is taken), and the competitors range over all node sets, not over any restricted family.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 68, Section 1, Eq. (1.1)

import Mathlib
import Definitions.Def_PadbergRao_OddCut_cutCapacity

namespace PadbergRao.OddCut

/-- `λ(U)` is odd: the node set `U` contains an odd number of the odd-labelled nodes `odd = V₁`.
The empty set has even label. Padberg–Rao 1982, p. 68, Section 1. -/
def IsOddSet {V : Type*} [DecidableEq V] (odd U : Finset V) : Prop :=
  Odd (U ∩ odd).card

/-- `(X : V − X)` is an odd minimum cut-set, i.e. `X` solves problem (1.1):
`λ(X)` is odd and `c(X : V − X) ≤ c(U : V − U)` for every `U ⊆ V` with `λ(U)` odd.
Padberg–Rao 1982, p. 68, Eq. (1.1). -/
def IsOddMinCut {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (odd X : Finset V) :
    Prop :=
  IsOddSet odd X ∧ ∀ U : Finset V, IsOddSet odd U → cutCapacity c X ≤ cutCapacity c U

end PadbergRao.OddCut


