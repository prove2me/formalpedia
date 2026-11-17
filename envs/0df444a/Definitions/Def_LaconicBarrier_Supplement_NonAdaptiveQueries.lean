-- Prove2me | Definitions.Def_LaconicBarrier_Supplement_NonAdaptiveQueries
-- name    : LaconicBarrier_Supplement_NonAdaptiveQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:31:16.586337+00:00
-- url     : https://prove2.me/theorems/b705e68f-f72a-47ed-b025-c29a48cd522c
-- title:
--   Reductions with non-adaptive queries
-- statement:
--   A black-box reduction $\mathcal R$ has **non-adaptive queries** if it fixes its entire list of oracle queries before receiving any oracle reply: from $\lambda$, the index $x$, the advice $z$, its coins and the challenger messages it has received before its first oracle reply, one can compute a list $(q_0, q_1, \dots)$ such that the $j$-th oracle query of $\mathcal R$, whenever it is made, equals $q_j$.
--
--   This hypothesis enters the last sentence of Theorem 8.3: a reduction with non-adaptive queries yields a non-adaptive multiprover protocol.
--
--   **Formalization Note** In the mission's execution law each oracle reply follows its query at once, so the part of the view before the first reply is exactly the part up to the first query. Later challenger messages may still affect what the reduction sends to the challenger and when it stops, but not which strings it queries.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.21, p.22

import Mathlib
import Definitions.Def_LaconicBarrier_Reduction

namespace LaconicBarrier.Supplement

/-- A reduction with **non-adaptive queries** (Jain, Mathialagan, Roy, *From Succinct Arguments to
Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256
1af78662…), Definition 4.21, p.22: "A reduction has non-adaptive queries if it fixes its entire list
of oracle queries before receiving any oracle reply"): there is a list `Q(λ, x, z, ρ, view₀)` of
queries, computed from the part `view₀` of the view before the first oracle reply, such that the
`j`-th query the reduction makes (counting from `0`) is the `j`-th entry of that list.

**Formalization Note** Oracle replies follow their queries immediately in the execution law, so
`view₀` is the view up to the first query: the challenger messages received before it. Later
challenger messages may still influence the reduction's messages to the challenger and when it
stops, but not which strings it queries. -/
def NonAdaptiveQueries (R : Reduction) : Prop :=
  ∃ Q : (lam : ℕ) → (x z : List Bool) → (Fin (R.coins lam x.length) → Bool) → List Ev →
      List (List Bool),
    ∀ (lam : ℕ) (x z : List Bool) (ρ : Fin (R.coins lam x.length) → Bool) (evs : List Ev)
      (q : List Bool), R.next lam x z ρ evs = .query q →
        (Q lam x z ρ (evs.takeWhile (fun e => !e.isReply)))[evs.countP Ev.isReply]? = some q

end LaconicBarrier.Supplement


