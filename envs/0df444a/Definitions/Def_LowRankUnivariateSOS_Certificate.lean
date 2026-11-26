-- Prove2me | Definitions.Def_LowRankUnivariateSOS_Certificate
-- name    : LowRankUnivariateSOS_Certificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:52:38.622941+00:00
-- url     : https://prove2.me/theorems/726cbef3-0267-4f1c-bce7-348d7a79ec21
-- title:
--   Certificate
-- statement:
--   Definitions and structural lemmas for Certificate, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Certificate.lean

import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
set_option autoImplicit true
noncomputable section
namespace LowRankUnivariateSOS
def InImagePlusSigmaKerCone (u : UPair) (q : Poly) : Prop :=
  ∃ v : UPair, ∃ ws : Finset UPair,
    (∀ w ∈ ws, InKerA u w) ∧ q = A u v + ws.sum sigma2
end LowRankUnivariateSOS


