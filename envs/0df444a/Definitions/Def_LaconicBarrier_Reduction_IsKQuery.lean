-- Prove2me | Definitions.Def_LaconicBarrier_Reduction_IsKQuery
-- name    : LaconicBarrier_Reduction_IsKQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:01.782213+00:00
-- url     : https://prove2.me/theorems/9104cf6b-a58d-491e-b5ee-335b64784672
-- title:
--   $k$-query reductions
-- statement:
--   A reduction is **$k$-query** if it makes at most $k(\lambda, |x|)$ oracle calls during one target-game execution; it is **one-query** if $k = 1$.
--
--   **Formalization Note** The count is imposed on every view, reachable or not: after $k$ replies the reduction never queries again. A reduction that respects the bound on reachable views can be modified on unreachable ones without changing any execution.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definitions 4.18–4.19, p.22

import Mathlib
import Definitions.Def_LaconicBarrier_Reduction

namespace LaconicBarrier

/-- A **`k`-query** reduction (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256
1af78662…), Definition 4.18, p.22: "it makes at most `k(λ, |x|)` oracle calls during one
target-game execution"; Definition 4.19: one-query is `k = 1`): on no view that already contains
`k(λ, |x|)` oracle replies does it query again.

**Formalization Note** The count is over every view, reachable or not; a reduction that makes at most
`k` calls on every reachable view can be changed on the unreachable ones to satisfy this without
changing any execution. -/
def Reduction.IsKQuery (R : Reduction) (k : ℕ → ℕ → ℕ) : Prop :=
  ∀ (lam : ℕ) (x z : List Bool) (ρ : Fin (R.coins lam x.length) → Bool) (evs : List Ev)
    (q : List Bool), k lam x.length ≤ evs.countP Ev.isReply → R.next lam x z ρ evs ≠ .query q

end LaconicBarrier


