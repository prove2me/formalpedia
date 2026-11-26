-- Prove2me | Definitions.Def_LowRankUnivariateSOS_Solution
-- name    : LowRankUnivariateSOS_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:12:41.40933+00:00
-- url     : https://prove2.me/theorems/5d5eef7d-0b8c-4e37-b511-34f851fc2e39
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/Solution.lean

import Definitions.Def_LowRankUnivariateSOS
import Theorems.Thm_LowRankUnivariateSOS_rankTwo_no_spurious_socp

set_option autoImplicit true
namespace LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
example (p : Poly) (u : UPair) (hp : IsSOS p) (hsocp : IsSOCP B p u) :
    sigma2 u = p :=
  rankTwo_no_spurious_socp p u hp hsocp
end LowRankUnivariateSOS


