-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:07.389808+00:00
-- url     : https://prove2.me/theorems/d098cc7e-84e8-483d-a813-7f49ae60841c
-- title:
--   Exists Supp Of Eval Ne
-- statement:
--   Definitions and structural lemmas for Exists Supp Of Eval Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
section Laurent
variable {A : Type*} [CommRing A] [IsDomain A]
end Laurent
section Sharp
variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L]
def wtX (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool) : LVar ι ζ n → ℤ
  | Sum.inl (i, a) =>
    if i ∈ S then
      (if (if last then a.val + 1 = n else a.val = 0) then (if isVec i then 1 else -1) else 0)
    else 0
  | Sum.inr _ => 0
def wExp (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool) (e : LVar ι ζ n →₀ ℕ) : ℤ :=
  ∑ x ∈ e.support, (e x : ℤ) * wtX isVec S last x
abbrev cc (τ : Type*) (L : Type*) [CommRing L] : L →+* LaurentPolynomial (MvPolynomial τ L) :=
  (LaurentPolynomial.C).comp C
variable (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
def tw (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) :
    MvPolynomial (LVar ι ζ n) L →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L) :=
  eval₂Hom (cc _ L) fun x =>
    LaurentPolynomial.T (wtX isVec S last x) * LaurentPolynomial.C (sharpHom isVec S g gi (X x))
end Sharp
section Gen
variable {ι ζ : Type*} {n : ℕ}
variable (k : Type*) [Field k]
abbrev genφ (n : ℕ) : k →+* GenField k n := (algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C
variable {k}
def genH (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (G : MvPolynomial (LVar ι ζ n) k) :
    MvPolynomial (LVar ι ζ n) (GenField k n) :=
  sharpHom isVec S (genMat k n)⁻¹ (genMat k n) (map (genφ k n) G)
end Gen
section Consts
variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
end Consts
section Coord
variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
end Coord
section DetPart
variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
end DetPart
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


