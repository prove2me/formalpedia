-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:13.054673+00:00
-- url     : https://prove2.me/theorems/e27072f2-e95e-4f17-9850-996c23548d39
-- title:
--   Gen Space Facts
-- statement:
--   Definitions and structural lemmas for Gen Space Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/GenSpaceFacts.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
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
def genPoint {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : MvPolynomial (LVar ι ζ n) (GenField k n) :=
  sharpHom isVec S (genMat k n) (genMat k n)⁻¹
    (map ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) G)
def Carries {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) (N : Submodule k (MvPolynomial (LVar ι ζ n) k)) : Prop :=
  genPoint isVec S G ∈ Submodule.span (GenField k n)
    ((fun f => map ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) f) '' (N : Set _))
def genSpace {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : Submodule k (MvPolynomial (LVar ι ζ n) k) :=
  sInf {N | Carries isVec S G N}
def HasWeight {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (f : MvPolynomial (LVar ι ζ n) k) (ν : Fin n → ℤ) : Prop :=
  ∀ m : Fin n, IsWeightedHomogeneous
    (fun x : LVar ι ζ n => match x with
      | Sum.inl (i, a) => if i ∈ S ∧ a = m then (if isVec i then (1 : ℤ) else -1) else 0
      | Sum.inr _ => 0) f (ν m)
def IsWeightOf {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (N : Submodule k (MvPolynomial (LVar ι ζ n) k)) (ν : Fin n → ℤ) : Prop :=
  ∃ f ∈ N, f ≠ 0 ∧ HasWeight isVec S f ν
def GenSpaceFacts : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k),
    Carries isVec S G (genSpace isVec S G) ∧ G ∈ genSpace isVec S G ∧
    Module.Finite k (genSpace isVec S G) ∧
    genSpace isVec S G = Submodule.span k {f | f ∈ genSpace isVec S G ∧ ∃ ν, HasWeight isVec S f ν} ∧
    (∀ (h : (Matrix (Fin n) (Fin n) k)ˣ), ∀ f ∈ genSpace isVec S G,
      sharpHom isVec S (↑h : Matrix _ _ k) (↑h⁻¹ : Matrix _ _ k) f ∈ genSpace isVec S G) ∧
    ∀ (π : Equiv.Perm (Fin n)) (ν : Fin n → ℤ),
      IsWeightOf isVec S (genSpace isVec S G) ν → IsWeightOf isVec S (genSpace isVec S G) (ν ∘ π)
def LemmaVb : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) (j : ℤ), 1 ≤ n →
    (j ∈ (genAct k isVec S true G).coeff.support ↔
      ∃ ν, IsWeightOf isVec S (genSpace isVec S G) ν ∧ ∃ m : Fin n, m.val + 1 = n ∧ ν m = j) ∧
    (j ∈ (genAct k isVec S false G).coeff.support ↔
      ∃ ν, IsWeightOf isVec S (genSpace isVec S G) ν ∧ ∃ m : Fin n, m.val = 0 ∧ ν m = j)
def LemmaVbCor : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) (θ : ℤ), 1 ≤ n →
    (((θ : WithTop ℤ) ≤ valS isVec S G) ↔
      ∀ ν, IsWeightOf isVec S (genSpace isVec S G) ν → ∀ m, θ ≤ ν m) ∧
    ((lam1S isVec S G ≤ (θ : WithBot ℤ)) ↔
      ∀ ν, IsWeightOf isVec S (genSpace isVec S G) ν → ∀ m, ν m ≤ θ)
def LemmaVdEquiv : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (φ : MvPolynomial (LVar ι ζ n) k →ₗ[k] MvPolynomial (LVar ι ζ n) k)
    (φL : MvPolynomial (LVar ι ζ n) (GenField k n) →ₗ[GenField k n] MvPolynomial (LVar ι ζ n) (GenField k n)),
    (∀ f, φL (map ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) f) =
      map ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) (φ f)) →
    (∀ f, genPoint isVec S (φ f) = φL (genPoint isVec S f)) →
    ∀ G, valS isVec S G ≤ valS isVec S (φ G) ∧ lam1S isVec S (φ G) ≤ lam1S isVec S G
def PlaneIsFrame : Prop :=
  ∀ (W : Type) [CommRing W] [IsLocalRing W] (p r K : ℕ),
    IsLocalRing.maximalIdeal W = Ideal.span {(p : W)} →
    ∀ F : Submodule (IsLocalRing.ResidueField W) (Fin (r + K) → IsLocalRing.ResidueField W),
      Module.finrank (IsLocalRing.ResidueField W) F = r →
      ∃ g : (Matrix (Fin (r + K)) (Fin (r + K)) W)ˣ, ∀ ξ : Fin (r + K) → W,
        (fun a => IsLocalRing.residue W (ξ a)) ∈ F ↔
          ∀ b : Fin K, (p : W) ∣ Matrix.vecMul ξ (↑g : Matrix _ _ W) (Fin.natAdd r b)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


