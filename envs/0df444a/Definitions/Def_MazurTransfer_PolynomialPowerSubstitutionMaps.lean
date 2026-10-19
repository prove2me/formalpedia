-- Prove2me | Definitions.Def_MazurTransfer_PolynomialPowerSubstitutionMaps
-- name    : MazurTransfer_PolynomialPowerSubstitutionMaps
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:03:03.287834+00:00
-- url     : https://prove2.me/theorems/128cbe86-c960-44ce-bc2e-db51e59bbba8
-- title:
--   The literal maps for the polynomial power-substitution presentation
-- statement:
--   Let $R$ be a commutative ring and let $n$ be a natural number. Regard $R[T]$ as acting on $R[X]$ by $T\mapsto X^n$. The quotient $R[T][Y]/(Y^n-T)$ has the specified forward map to $R[X]$ and backward map from $R[X]$. The forward-after-backward composite is the identity. These literal constructors support the separate inverse-composite theorem and the resulting finite free power-substitution basis.
-- source:
--   Twelve original declarations from MazurTheorem PolynomialPowerSubstitutionPresentation.lean, Apache-2.0, Vas and contributors. Every retained data constructor and embedded proof body is unchanged. The separate nontrivial backward-after-forward theorem and final equivalence are excluded for dependency-ordered theorem publication. All twelve original closed types and ten data constructor values are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: the original power-substitution algebra isomorphism, raised polynomial bases, and arbitrarily-large actual order-thirteen FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the polynomial ring with coefficient parameter acting by
X^n is the literal monic root algebra of Y^n-T.
Named downstream consumer: the power-substitution finite free basis used to
raise the degree of actual order-13 FiniteMapData.
-/
import Mathlib

noncomputable section
universe u
namespace MazurTransfer.PolynomialPowerSubstitutionPresentation
open Polynomial
variable (R : Type u) [CommRing R] (n : ℕ)

def Source (_n : ℕ) : Type u := Polynomial R
instance sourceCommRing : CommRing (Source R n) := inferInstanceAs (CommRing (Polynomial R))
instance sourceBaseAlgebra : Algebra R (Source R n) := inferInstanceAs (Algebra R (Polynomial R))

def sourceX : Source R n := (X : Polynomial R)
def powerMap : Source R n →+* Polynomial R := (aeval ((X : Polynomial R)^n)).toRingHom
scoped instance powerAlgebra : Algebra (Source R n) (Polynomial R) := (powerMap R n).toAlgebra

def relation : Polynomial (Source R n) := X^n - C (sourceX R n)
abbrev RootRing := AdjoinRoot (relation R n)

theorem relation_eval : (relation R n).eval₂ (powerMap R n) (X : Polynomial R) = 0 := by
  rw [relation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change X^n - aeval ((X : Polynomial R)^n) X = 0
  rw [aeval_X, sub_self]

def forward : RootRing R n →+* Polynomial R :=
  AdjoinRoot.lift (powerMap R n) X (relation_eval R n)
def backward : Polynomial R →+* RootRing R n :=
  eval₂RingHom ((AdjoinRoot.of (relation R n)).comp (C : R →+* Source R n))
    (AdjoinRoot.root (relation R n))





theorem forward_backward : (forward R n).comp (backward R n) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro r
    change forward R n (backward R n (C r)) = C r
    rw [backward, coe_eval₂RingHom, eval₂_C]
    change forward R n (AdjoinRoot.of (relation R n) (C r)) = C r
    exact (AdjoinRoot.lift_of (relation_eval R n) (x := (C r : Source R n))).trans
      (aeval_C ((X : Polynomial R)^n) r)
  · simp [forward, backward]





end MazurTransfer.PolynomialPowerSubstitutionPresentation
#print axioms MazurTransfer.PolynomialPowerSubstitutionPresentation.forward_backward


