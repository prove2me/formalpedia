-- Prove2me | Definitions.Def_PvsNP_reductions
-- name    : PvsNP_reductions
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T01:13:42.556355+00:00
-- url     : https://prove2.me/theorems/03026c10-3f43-48fa-89a4-e08df8b2b55f
-- title:
--   Karp reductions, $\mathsf{NP}$-hardness and $\mathsf{NP}$-completeness
-- statement:
--   A **polynomial-time many-one (Karp) reduction** from a decision problem $L$ to a decision problem $K$, written $L \le_p K$, is a polynomial-time computable map $f : \{0,1\}^* \to \{0,1\}^*$ with $L(x) = K(f(x))$ for every input $x$.
--
--   A problem $L$ is **$\mathsf{NP}$-hard** if $K \le_p L$ for every $K \in \mathsf{NP}$, and **$\mathsf{NP}$-complete** if in addition $L \in \mathsf{NP}$. This follows Arora–Barak, Definition 2.7.
-- source:
--   Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009, Definition 2.7

import Definitions.Def_PvsNP_complexity_classes

/-!
# Polynomial-time many-one reductions, NP-hardness and NP-completeness

Following Arora–Barak, *Computational Complexity: A Modern Approach* (2009), Definition 2.7.
-/

namespace PvsNP

/-- `PolyTimeReducible L K` (Karp reduction `L ≤ₚ K`): there is a polynomial-time computable map
`f` on bitstrings with `L x = K (f x)` for every input `x`. -/
def PolyTimeReducible (L K : DecisionProblem) : Prop :=
  ∃ f : List Bool → List Bool, IsPolyTime f ∧ ∀ x, L x = K (f x)

/-- `NPHard L`: every problem in `NP` reduces to `L` by a polynomial-time many-one reduction. -/
def NPHard (L : DecisionProblem) : Prop :=
  ∀ K ∈ NP, PolyTimeReducible K L

/-- `NPComplete L`: `L` lies in `NP` and is `NP`-hard. -/
def NPComplete (L : DecisionProblem) : Prop :=
  L ∈ NP ∧ NPHard L

end PvsNP


