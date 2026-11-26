-- Prove2me | Definitions.Def_LowRankUnivariateSOS
-- name    : LowRankUnivariateSOS
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:01:57.932884+00:00
-- url     : https://prove2.me/theorems/dc230a3a-bb45-5aa7-bfcf-789aadff10c0
-- title:
--   Low Rank Univariate SOS
-- statement:
--   Definitions and structural lemmas for Low Rank Univariate SOS, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS.lean

import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_RankTwoMain
import Definitions.Def_LowRankUnivariateSOS_Socp
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
set_option autoImplicit true


