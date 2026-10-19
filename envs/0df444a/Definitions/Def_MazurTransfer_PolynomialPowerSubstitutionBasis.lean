-- Prove2me | Definitions.Def_MazurTransfer_PolynomialPowerSubstitutionBasis
-- name    : MazurTransfer_PolynomialPowerSubstitutionBasis
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:10:34.367172+00:00
-- url     : https://prove2.me/theorems/ae30b750-66ea-48e4-98dd-4e3f0b5597ef
-- title:
--   The original bases for polynomial power substitution
-- statement:
--   Let $R$ be a nontrivial commutative ring and $n>0$. The action $T\mapsto X^n$ gives the specified basis of $R[X]$ of size $n$ over $R[T]$. More generally, a specified polynomial basis indexed by $I$ for a parameter $f$ induces the original basis indexed by $\operatorname{Fin}(n)\times I$ for the parameter $f^n$. These constructors increase the degree of actual order-thirteen finite-map data.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Two original constructors from PolynomialPowerSubstitutionBasis.lean, with unchanged bodies and only the import replaced by the public presentation-equivalence interface. Both original closed types and both original data values are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: the actual first- and inverse-chart parameter powers and arbitrarily-large integral FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a monic presentation gives the polynomial power-substitution
basis, and scalar towers raise any existing polynomial basis by a factor n.
Named downstream consumers: both actual order-13 parameter powers and their
level-set bases in arbitrarily large whole-curve FiniteMapData.
-/
import Definitions.Def_MazurTransfer_PolynomialPowerSubstitutionEquiv

noncomputable section
universe u v
namespace MazurTransfer.PolynomialPowerSubstitutionBasis
open Polynomial Module
open PolynomialPowerSubstitutionPresentation
variable (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ)

def powerBasis (hn : n ≠ 0) : Basis (Fin n) (Source R n) (Polynomial R) := by
  letI : Nontrivial (Source R n) := inferInstanceAs (Nontrivial (Polynomial R))
  have hd : (relation R n).natDegree = n := natDegree_X_pow_sub_C
  let b := (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (sourceX R n) hn)).basis
  exact (b.map (presentationEquiv R n).toLinearEquiv).reindex (finCongr hd)

variable {A : Type u} [CommRing A] [Algebra R A] {ι : Type v}

def raisedBasis (f : A)
    (b : letI : Algebra (Polynomial R) A := (aeval f).toRingHom.toAlgebra
      Basis ι (Polynomial R) A) (hn : n ≠ 0) :
    letI : Algebra (Polynomial R) A := (aeval (f^n)).toRingHom.toAlgebra
    Basis (Fin n × ι) (Polynomial R) A := by
  letI : Algebra (Polynomial R) A := (aeval f).toRingHom.toAlgebra
  letI : Algebra (Source R n) A := ((aeval f).toRingHom.comp (powerMap R n)).toAlgebra
  letI : IsScalarTower (Source R n) (Polynomial R) A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let bp : Basis (Fin n × ι) (Source R n) A := (powerBasis R n hn).smulTower b
  letI : Algebra (Polynomial R) A := (aeval (f^n)).toRingHom.toAlgebra
  let e : Source R n ≃+* Polynomial R := RingEquiv.refl (Polynomial R)
  refine bp.mapCoeffs e ?_
  intro c x
  change aeval (f^n) c * x = aeval f (powerMap R n c) * x
  change aeval (f^n) c * x = aeval f (c.comp ((X : Polynomial R)^n)) * x
  let p : Polynomial R := c
  change aeval (f^n) p * x = aeval f (p.comp ((X : Polynomial R)^n)) * x
  rw [aeval_comp, map_pow, aeval_X]

end MazurTransfer.PolynomialPowerSubstitutionBasis
#print axioms MazurTransfer.PolynomialPowerSubstitutionBasis.raisedBasis


