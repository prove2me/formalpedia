-- Prove2me | Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
-- name    : LowRankUnivariateSOS_UnivariateAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:59:16.073578+00:00
-- url     : https://prove2.me/theorems/eb573245-dc87-4d72-b07d-6299ff94c720
-- title:
--   Univariate Algebra
-- statement:
--   Definitions and structural lemmas for Univariate Algebra, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebra.lean

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.List.Prime
import Mathlib.Data.Multiset.Filter
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
set_option autoImplicit true
noncomputable section
namespace LowRankUnivariateSOS
section DotForm
variable {B : DotForm}
end DotForm
end LowRankUnivariateSOS


