-- Prove2me | Definitions.Def_FreeOrderEPTAS_orderOf
-- name    : FreeOrderEPTAS_orderOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:19.294626+00:00
-- url     : https://prove2.me/theorems/8e433ae6-d2c2-49cb-a9db-d8cc2739be63
-- title:
--   The permutation built from an assignment
-- statement:
--   From an assignment $x$: the last variables to be inspected are those of the first machine, just before them those of the second machine, and so on, each group in index order. Variables without a machine come after all assigned ones.
--
--   **Formalization Note** `orderOf x` sorts the jobs by a key: $m-1-i$ for the first machine $i$ holding the job, and $m$ for a job on no machine. It is a total function, and `σ t` is the variable at time `t`.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.5, p.20

import Mathlib
import Definitions.Def_FreeOrderEPTAS_SCInstance

namespace FreeOrderEPTAS

variable {m n : ℕ}

/-- The sort key of job `j`: `m - 1 - i` for the first machine `i` holding it, `m` if there is none. -/
def orderKey (x : Assignment m n) (j : Fin n) : ℕ :=
  match (List.finRange m).find? (fun i => x i j) with
  | some i => i.rev.val
  | none => m

/-- The permutation of §3.5 (arXiv:2007.13121v3, p.20): the last variables are those of the first
machine, just before them those of the second, and so on, each group in index order. `σ t` is the
variable inspected at time `t`. Unassigned variables come after all assigned ones. -/
def orderOf (x : Assignment m n) : Equiv.Perm (Fin n) :=
  Tuple.sort (orderKey x)

end FreeOrderEPTAS


