-- Prove2me | Definitions.Def_MazurTransfer_PolynomialBasisPowerLevelSets
-- name    : MazurTransfer_PolynomialBasisPowerLevelSets
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:11:54.456141+00:00
-- url     : https://prove2.me/theorems/bbc3f72b-bc3a-436c-ac75-a8226f29ba0c
-- title:
--   Finite free level sets of powers of a polynomial-basis parameter
-- statement:
--   Let $R$ be a nontrivial commutative ring, let $A$ be an $R$-algebra, and suppose $A$ has a specified basis of $d$ elements over $R[T]$ with $T$ acting as $f$. For $n>0$, the parameter $f^n$ defines a finite polynomial map. For any nontrivial commutative $R$-algebra $S$ and $s\in S$, the evaluated quotient $(S\otimes_R A)/(1\otimes f^n-s\otimes1)$ has the specified basis indexed by $\operatorname{Fin}(n)\times\operatorname{Fin}(d)$ and is finite free of rank $nd$. These are the original degree-raising level-set constructors.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Three original declarations from PolynomialBasisPowerLevelSets.lean with unchanged bodies and only imports replaced by the public power-basis and official FLT level-set-equivalence interfaces. All original closed types and the original level-set basis value are compared in the kernel. Reuses official Anthropic FLT at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2 with attribution retained. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: the actual first- and inverse-chart parameter powers and arbitrarily-large integral FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Reuses the complete official Anthropic FLT levelSetEquiv at pin
6e837e75355538c7f80bab5b956861e86c4eacc2, retaining its upstream attribution.
Design boundary: powers of a parameter with a finite polynomial basis
have finite maps and finite free evaluated tensor quotients of rank n*d.
Named downstream consumer: arbitrarily large actual order-13 FiniteMapData.
-/
import Definitions.Def_MazurTransfer_PolynomialPowerSubstitutionBasis
import Definitions.Def_MazurTransfer_OfficialFLTPolynomialLevelSetEquiv

noncomputable section
universe u
namespace MazurTransfer.PolynomialBasisPowerLevelSets
open Polynomial Module
open scoped TensorProduct
variable (R : Type u) [CommRing R] [Nontrivial R]
variable (A : Type u) [CommRing A] [Algebra R A]
variable (d n : ℕ) (f : A)
variable (b : letI : Algebra (Polynomial R) A := (aeval f).toRingHom.toAlgebra
    Basis (Fin d) (Polynomial R) A)

include b

theorem parameter_power_finite (hn : n ≠ 0) :
    (aeval (f^n) : Polynomial R →ₐ[R] A).toRingHom.Finite := by
  letI : Algebra (Polynomial R) A := (aeval (f^n)).toRingHom.toAlgebra
  exact Module.Finite.of_basis
    (PolynomialPowerSubstitutionBasis.raisedBasis R n f b hn)

variable (S : Type u) [CommRing S] [Algebra R S]

def powerLevelSetBasis (hn : n ≠ 0) (s : S) :
    Basis (Fin n × Fin d) S (S ⊗[R] A ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] (f^n) - s ⊗ₜ[R] (1 : A)}) := by
  letI : Algebra (Polynomial R) A := (aeval (f^n)).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) A := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R A r = aeval (f^n) (C r)
    rw [aeval_C]
  letI : Algebra (Polynomial R) S := (aeval s).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) S := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R S r = aeval s (C r)
    rw [aeval_C]
  let e := P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b.levelSetEquiv
    R A S (f^n) s (by change aeval (f^n) X = _; exact aeval_X _)
      (by change aeval s X = s; exact aeval_X s)
  exact ((PolynomialPowerSubstitutionBasis.raisedBasis R n f b hn).baseChange S).map e.symm.toLinearEquiv

theorem powerLevelSet_finite_free_finrank (hn : n ≠ 0) [Nontrivial S] (s : S) :
    let Q := S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (f^n) - s ⊗ₜ[R] (1 : A)}
    Module.Finite S Q ∧ Module.Free S Q ∧ Module.finrank S Q = n*d := by
  let B := powerLevelSetBasis R A d n f b S hn s
  exact ⟨Module.Finite.of_basis B, Module.Free.of_basis B, by
    simpa using Module.finrank_eq_card_basis B⟩

end MazurTransfer.PolynomialBasisPowerLevelSets
#print axioms MazurTransfer.PolynomialBasisPowerLevelSets.powerLevelSet_finite_free_finrank


