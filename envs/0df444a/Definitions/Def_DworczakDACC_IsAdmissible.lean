-- Prove2me | Definitions.Def_DworczakDACC_IsAdmissible
-- name    : DworczakDACC_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:00.587311+00:00
-- url     : https://prove2.me/theorems/6fe5a810-4647-4632-a6d6-a2d39643b12a
-- title:
--   Admissible order $\Phi$: every agent is named infinitely often
-- statement:
--   Let $N=M\cup W$ be the set of all agents (men $M$, women $W$). An **order** is a sequence $\Phi:\mathbb N\to N$; it names the agent who proposes in each round. The order is **admissible** when every agent is named infinitely often:
--
--   $$\forall a\in N,\ \forall n\in\mathbb N,\ \exists k\ge n:\ \Phi(k)=a .$$
--
--   The paper assumes this property of every sequence $\Phi$ it considers; it is what guarantees that every agent who is not holding the best option in its budget set eventually gets to propose.
--
--   **Formalization Note** The set of agents is the sum type $D\oplus H$ (men $D$, women $H$). $\Phi$ is indexed from $0$: $\Phi(0)$ proposes in the paper's round $1$.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), §3, p. 6

import Mathlib

namespace DworczakDACC

/-- **An order of proposals: a sequence `Φ : ℕ → N` taking every value infinitely often.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), §3, p. 6:
"fix a sequence Φ : ℕ → N such that each value in N is taken infinitely many times. Whenever I
refer to a sequence Φ in this paper, I assume that Φ has this property."

The set of agents is `N = D ⊕ H` (men `D`, women `H`). `IsAdmissible Φ` says that for every agent
`a` and every `n` there is a later index `k ≥ n` with `Φ k = a`.

**Formalization Note.** `Φ` is indexed from `0`: `Φ 0` is the proposer of the paper's round 1,
and `Φ k` the proposer of round `k + 1`. -/
def IsAdmissible {D H : Type*} (Φ : ℕ → D ⊕ H) : Prop :=
  ∀ a : D ⊕ H, ∀ n : ℕ, ∃ k, n ≤ k ∧ Φ k = a

end DworczakDACC


