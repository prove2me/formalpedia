-- Prove2me | Definitions.Def_LowRankUnivariateSOS_RankTwoMain
-- name    : LowRankUnivariateSOS_RankTwoMain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:00:14.026802+00:00
-- url     : https://prove2.me/theorems/f9b6a31e-04ad-43f2-8cef-ed1ca6981edc
-- title:
--   Rank Two Main
-- statement:
--   Definitions and structural lemmas for Rank Two Main, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/RankTwoMain.lean

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
set_option autoImplicit true
noncomputable section
namespace LowRankUnivariateSOS
section DotForm
variable {B : DotForm}
end DotForm
section DotFormPosDef
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
end DotFormPosDef
end LowRankUnivariateSOS


