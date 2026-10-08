-- Prove2me | Definitions.Def_AuslanderReiten
-- name    : AuslanderReiten
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:00.656075+00:00
-- url     : https://prove2.me/theorems/19eecdfc-0aa8-411f-af2b-7709b5678b7b
-- statement:
--   Let K be the fraction field of the polynomial ring in three variables over the field with two elements, with parameters given by the images of those variables. A totally acyclic witness for a module Z over a ring R is an integer-indexed exact chain complex P of finitely generated projective R-modules such that Z is isomorphic to the cokernel of P₁ → P₀ and applying Hom_R(−,Q) gives an exact complex for every projective R-module Q. Explicitly, every map Pᵢ → Q annihilating the image of Pᵢ₊₁ factors through the differential Pᵢ → Pᵢ₋₁. For a field F, an F-algebra R, and an R-module Z with compatible F-action, Conclusions(F,R,Z) is the proposition that R and Z are finite-dimensional over F, Z is not projective but has a totally acyclic witness, Extⁱ_R(Z,Z) and Extⁱ_R(Z,R) vanish for every positive integer i, R modulo its Jacobson radical J is isomorphic as an F-algebra to F⁸, and J⁴ is nonzero. A System packages a K-algebra and a module with compatible scalar actions. FullStatement is the defined proposition that the three parameters are algebraically independent and there exists such a System satisfying Conclusions over K whose properties persist over every field extension E of K: the tensor product E ⊗_K Z admits an E ⊗_K R-module structure compatible with its E-action, satisfying (a ⊗ r)·(b ⊗ z) = ab ⊗ (r·z), and the resulting algebra and module satisfy Conclusions over E.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/AuslanderReiten.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/AuslanderReiten.lean; bytes 16..2656
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.Statement
universe u v

abbrev K := FractionRing (MvPolynomial (Fin 3) (ZMod 2))

def parameters (i : Fin 3) : K :=
  algebraMap (MvPolynomial (Fin 3) (ZMod 2)) K (MvPolynomial.X i)

def TotallyAcyclicWitness (R : Type u) [Ring R]
    (Z : Type u) [AddCommGroup Z] [Module R Z] : Prop :=
  ∃ P : ChainComplex (ModuleCat.{u} R) ℤ,
    (∀ i : ℤ, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧
    (∀ i : ℤ, LinearMap.range (P.d (i+1) i).hom = LinearMap.ker (P.d i (i-1)).hom) ∧
    (∀ (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
      (i : ℤ) (f : P.X i →ₗ[R] Q), f.comp (P.d (i+1) i).hom = 0 →
        ∃ g : P.X (i-1) →ₗ[R] Q, f = g.comp (P.d i (i-1)).hom) ∧
    Nonempty (Z ≃ₗ[R] (P.X 0 ⧸ LinearMap.range (P.d 1 0).hom))

def Conclusions (F R Z : Type u) [Field F] [Ring R] [Algebra F R]
    [AddCommGroup Z] [Module R Z] [Module F Z] [IsScalarTower F R Z] : Prop :=
  FiniteDimensional F R ∧
  FiniteDimensional F Z ∧
  ¬ Module.Projective R Z ∧
  TotallyAcyclicWitness R Z ∧
  (∀ i : ℕ, 0 < i →
    Subsingleton (Abelian.Ext (ModuleCat.of R Z) (ModuleCat.of R Z) i)) ∧
  (∀ i : ℕ, 0 < i →
    Subsingleton (Abelian.Ext (ModuleCat.of R Z) (ModuleCat.of R R) i)) ∧
  Nonempty ((R ⧸ Ring.jacobson R) ≃ₐ[F] (Fin 8 → F)) ∧
  (Ring.jacobson R)^4 ≠ ⊥

structure System where
  algebraCarrier : Type
  [ring : Ring algebraCarrier]
  [scalarAlgebra : Algebra K algebraCarrier]
  moduleCarrier : Type
  [additiveGroup : AddCommGroup moduleCarrier]
  [action : Module algebraCarrier moduleCarrier]
  [scalarAction : Module K moduleCarrier]
  [actionTower : IsScalarTower K algebraCarrier moduleCarrier]

attribute [instance] System.ring System.scalarAlgebra System.additiveGroup
  System.action System.scalarAction System.actionTower

def FullStatement : Prop :=
  AlgebraicIndependent (ZMod 2) parameters ∧
  ∃ s : System,
    Conclusions K s.algebraCarrier s.moduleCarrier ∧
    ∀ (E : Type v) [Field E] [Algebra K E],
      ∃ action : Module (E ⊗[K] s.algebraCarrier) (E ⊗[K] s.moduleCarrier),
      letI := action
      ∃ tower : IsScalarTower E (E ⊗[K] s.algebraCarrier) (E ⊗[K] s.moduleCarrier),
      letI := tower
      (∀ (a b : E) (r : s.algebraCarrier) (z : s.moduleCarrier),
        (a ⊗ₜ[K] r) • (b ⊗ₜ[K] z) = (a*b) ⊗ₜ[K] (r • z)) ∧
      Conclusions E (E ⊗[K] s.algebraCarrier) (E ⊗[K] s.moduleCarrier)

end ArExplicit.Statement

namespace ArExplicit.Statement
universe v



end ArExplicit.Statement
end
end OAI


