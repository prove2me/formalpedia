-- Prove2me | Definitions.Def_LowRankUnivariateSOS_FactoredCase
-- name    : LowRankUnivariateSOS_FactoredCase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:53:26.586073+00:00
-- url     : https://prove2.me/theorems/817b207a-2909-509c-b315-12be5932eb3f
-- title:
--   Factored Case
-- statement:
--   Definitions and structural lemmas for Factored Case, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/FactoredCase.lean

import Mathlib.Tactic.Linarith
import Definitions.Def_LowRankUnivariateSOS_Socp
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
namespace LowRankUnivariateSOS
section DotForm
variable {B : DotForm}
def ImageOrthogonalResidual (B : DotForm) (p : Poly) (u uImg : UPair) : Prop :=
  ∀ q : Poly, InImageA uImg q → B q (residual p u) = 0
end DotForm
section DotFormPosDef
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
end DotFormPosDef
end LowRankUnivariateSOS


