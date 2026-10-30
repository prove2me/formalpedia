-- Prove2me | Definitions.Def_LindenReversibility_Protocol_IsLocal
-- name    : LindenReversibility_Protocol_IsLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:24.401975+00:00
-- url     : https://prove2.me/theorems/2df5fc5e-aa00-4034-a06e-21e69465096b
-- title:
--   A protocol made of local operations
-- statement:
--   A protocol (a finite tree of steps) is **local** if, at every step, the acting party's family of operators $K_1,\dots,K_n$ is a complete family of measurement operators, $\sum_k K_k^\dagger K_k = I$, on that party's system.
--
--   This is the condition under which the branch weights of the protocol are probabilities summing to one; it is the hypothesis "for any local protocol" of eq. (22).
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, p.2 (local operations) and p.3 (sentence before (22))

import Mathlib
import Definitions.Def_LindenReversibility_IsKrausFamily
import Definitions.Def_LindenReversibility_Protocol

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, p.2: a protocol is
made of genuine local operations: at every step, the acting party's family of operators is a
complete family of measurement operators (`IsKrausFamily`, `∑_k K_kᴴ K_k = 1`). -/
def Protocol.IsLocal {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] : Protocol A B C → Prop
  | .stop => True
  | .stepA _ K next => IsKrausFamily K ∧ ∀ i, (next i).IsLocal
  | .stepB _ K next => IsKrausFamily K ∧ ∀ i, (next i).IsLocal
  | .stepC _ K next => IsKrausFamily K ∧ ∀ i, (next i).IsLocal

end LindenReversibility


