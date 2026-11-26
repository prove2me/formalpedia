-- Prove2me | Definitions.Def_LowRankUnivariateSOS_Socp
-- name    : LowRankUnivariateSOS_Socp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:52:38.240568+00:00
-- url     : https://prove2.me/theorems/2f426e57-4bfd-4393-b6ea-c8544289b874
-- title:
--   Socp
-- statement:
--   Definitions and structural lemmas for Socp, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
set_option autoImplicit true
noncomputable section
namespace LowRankUnivariateSOS
abbrev DotForm := LinearMap.BilinForm ℝ Poly
section BilinearLemmas
variable {B : DotForm}
end BilinearLemmas
section SocpDefs
variable (B : DotForm)
def objective (p : Poly) (u : UPair) : ℝ :=
  B (residual p u) (residual p u)
def IsFOCP (p : Poly) (u : UPair) : Prop :=
  ∀ v : UPair, B (A u v) (residual p u) = 0
def hessianTerm (p : Poly) (u v : UPair) : ℝ :=
  B (sigma2 v) (residual p u) + 2 * B (A u v) (A u v)
def IsSOCP (p : Poly) (u : UPair) : Prop :=
  IsFOCP B p u ∧ ∀ v : UPair, 0 ≤ hessianTerm B p u v
end SocpDefs
section Positivity
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
end Positivity
end LowRankUnivariateSOS


