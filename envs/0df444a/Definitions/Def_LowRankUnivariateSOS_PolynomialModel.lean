-- Prove2me | Definitions.Def_LowRankUnivariateSOS_PolynomialModel
-- name    : LowRankUnivariateSOS_PolynomialModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:52:21.50317+00:00
-- url     : https://prove2.me/theorems/e7e6080d-38e9-5c98-b4c7-e9662408e704
-- title:
--   Polynomial Model
-- statement:
--   Definitions and structural lemmas for Polynomial Model, from Chenyang Yuan (yuanchenyang/lean_low_rank_univariate_sos; formalizing Legat, Yuan, and Parrilo, SIAM J. Optim. 2023; see pinned Apache-2.0 LICENSE and README.md)'s pinned Low-rank univariate sum of squares has no spurious second-order critical points (rank 2) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PolynomialModel.lean

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
set_option autoImplicit true
noncomputable section
namespace LowRankUnivariateSOS
open scoped BigOperators
abbrev Poly := Polynomial ℝ
instance : GCDMonoid Poly := EuclideanDomain.gcdMonoid Poly
structure UPair where
  fst : Poly
  snd : Poly
instance : DecidableEq UPair := by
  classical
  infer_instance
namespace UPair
instance : Zero UPair where
  zero := ⟨0, 0⟩
instance : Add UPair where
  add u v := ⟨u.fst + v.fst, u.snd + v.snd⟩
instance : Neg UPair where
  neg u := ⟨-u.fst, -u.snd⟩
instance : Sub UPair where
  sub u v := ⟨u.fst - v.fst, u.snd - v.snd⟩
instance : SMul ℝ UPair where
  smul a u := ⟨a • u.fst, a • u.snd⟩
end UPair
def sigma2 (u : UPair) : Poly :=
  u.fst ^ 2 + u.snd ^ 2
def A (u v : UPair) : Poly :=
  u.fst * v.fst + u.snd * v.snd
def residual (p : Poly) (u : UPair) : Poly :=
  sigma2 u - p
def IsSOS (p : Poly) : Prop :=
  ∃ q₁ q₂ : Poly, p = q₁ ^ 2 + q₂ ^ 2
def InImageA (u : UPair) (q : Poly) : Prop :=
  ∃ v : UPair, A u v = q
def InKerA (u v : UPair) : Prop :=
  A u v = 0
def InSigmaKerCone (u : UPair) (q : Poly) : Prop :=
  ∃ ws : Finset UPair, (∀ w ∈ ws, InKerA u w) ∧ q = ws.sum sigma2
end LowRankUnivariateSOS


