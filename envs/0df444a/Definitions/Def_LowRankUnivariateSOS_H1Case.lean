-- Prove2me | Definitions.Def_LowRankUnivariateSOS_H1Case
-- name    : LowRankUnivariateSOS_H1Case
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:52:55.470233+00:00
-- url     : https://prove2.me/theorems/cceb235d-a413-5083-9382-007cf8180b20
-- title:
--   H1 Case
-- statement:
--   Definitions and structural lemmas for H1 Case, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
set_option autoImplicit true
noncomputable section
namespace LowRankUnivariateSOS
def scalePair (g : Poly) (u : UPair) : UPair :=
  ⟨g * u.fst, g * u.snd⟩
def perpPair (t : Poly) (u : UPair) : UPair :=
  ⟨-t * u.snd, t * u.fst⟩
end LowRankUnivariateSOS


