-- Prove2me | Definitions.Def_HousingRI_IsStrict
-- name    : HousingRI_IsStrict
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:21.324934+00:00
-- url     : https://prove2.me/theorems/7dc96cf8-b521-4f6e-85b4-6a83fde95edf
-- title:
--   Strict preferences: no ties between acceptable objects
-- statement:
--   Let $N$ be a finite set of agents; agent $i$ owns object $i$, so $N$ is also the set of objects. Preferences are given by a real matrix $A$: agent $i$ weakly prefers object $j$ to object $k$ ($j\,R_i\,k$) when $A_{ik}\le A_{ij}$, strictly ($j\,P_i\,k$) when $A_{ik}<A_{ij}$. Object $j$ is acceptable to $i$ when $A_{ii}\le A_{ij}$.
--
--   The profile $A$ has **strict preferences** if no agent is indifferent between two distinct acceptable objects:
--
--   $$\forall i,j,k\in N:\quad A_{ii}\le A_{ij},\ A_{ii}\le A_{ik},\ j\ne k\ \Longrightarrow\ A_{ij}\ne A_{ik}.$$
--
--   Ties between unacceptable objects are allowed. This is the domain on which the top trading cycles outcome is the unique strong core allocation.
--
--   **Formalization Note** Only the order of each row of $A$ matters; every complete transitive preference relation on a finite set is represented this way.
-- source:
--   Biró, Klijn, Klimentova, Viana, Shapley-Scarf Housing Markets: Respecting Improvement, Integer Programming, and Kidney Exchange, arXiv:2102.00167v1, §2, p.6 (strict preferences).

import Mathlib

namespace HousingRI

/-- **Strict preferences** (Biró, Klijn, Klimentova, Viana, *Shapley-Scarf Housing Markets:
Respecting Improvement, Integer Programming, and Kidney Exchange*, arXiv:2102.00167v1, §2, p.6):
"Agent i's preferences are called strict if they do not exhibit ties between acceptable objects,
i.e., for all acceptable j, k ∈ N with j ≠ k we have jPik or kPij. A housing market has strict
preferences if each agent has strict preferences."

**Formalization Note.** Agents and objects form one type `N` (object `i` is agent `i`'s
endowment). Preferences are a utility matrix `A : N → N → ℝ`: `j Rᵢ k` is `A i k ≤ A i j`, only
the order of each row matters, and object `j` is acceptable to `i` when `A i i ≤ A i j`. Ties
between unacceptable objects are allowed, as on the page. -/
def IsStrict {N : Type*} (A : N → N → ℝ) : Prop :=
  ∀ i j k : N, A i i ≤ A i j → A i i ≤ A i k → j ≠ k → A i j ≠ A i k

end HousingRI


