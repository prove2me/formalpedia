-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:54.788+00:00
-- url     : https://prove2.me/theorems/2f6d3221-9ec0-4b59-b7bf-5217d5a88b46
-- title:
--   Exists Unique Statement
-- statement:
--   Definitions and structural lemmas for Exists Unique Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/ExistsUniqueStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
section Family
variable {K : Type*} [Fintype K] (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)]
def ExistsUniqueStatement : Prop :=
  ∃ I : IFamily F ι, IsFieldIntersection I ∧
    ∀ J : IFamily F ι, IsFieldIntersection J →
      ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n → J V n L = I V n L
def SymmStatement : Prop :=
  ∀ I : IFamily F ι, IsFieldIntersection I →
    ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)),
      IsProjVarF V n → I V n (L ∘ σ) = I V n L
def MultilinStatement : Prop :=
  ∀ I : IFamily F ι, IsFieldIntersection I →
    ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ) (j : Fin n) (a b : K → ℤ),
      IsProjVarF V n →
      I V n (Function.update L j (a + b)) = I V n (Function.update L j a) + I V n (Function.update L j b)
end Family
section Projection
variable {K : Type*} [Fintype K] {K' : Type*} [Fintype K'] (F : Type*) [Field F]
  (ι : K → Type*) [∀ k, Fintype (ι k)] (ι' : K' → Type*) [∀ k, Fintype (ι' k)]
def ProjContractStatement : Prop :=
  ∀ I' : IFamily F ι', IsFieldIntersection I' →
    ∀ (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (V' : Ideal (MRingOver F ι')) (e d : ℕ)
      (L : Fin e → K → ℤ), IsBlockMap κ v → IsProjVarF V' e → IsProjVarF (imageVar F v V') d →
      d < e → I' V' e (fun j => pullDeg κ (L j)) = 0
def ProjDegStatement : Prop :=
  ∀ (I : IFamily F ι) (I' : IFamily F ι'), IsFieldIntersection I → IsFieldIntersection I' →
    ∀ (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (V' : Ideal (MRingOver F ι')) (e : ℕ)
      (L : Fin e → K → ℤ) (i' : ∀ k', ι' k'), IsBlockMap κ v → IsProjVarF V' e →
      IsProjVarF (imageVar F v V') e → IsChart V' i' →
      I' V' e (fun j => pullDeg κ (L j)) = (fnDeg v V' i' : ℤ) * I (imageVar F v V') e L
end Projection
section Fibre
variable {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]
def GeoNumStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : IFamily (ZMod p) ι), IsFieldIntersection I →
    ∀ (V : Ideal (MRing ι)) (n : ℕ) (a : Fin n → K → ℤ), IsMultiProjPrime V → (p : MRing ι) ∈ V →
      IsProjVarF (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
      geoNum n V a = I (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n a
end Fibre
section BaseField
variable {K : Type*} [Fintype K] (F F' : Type*) [Field F] [Field F'] [Algebra F F'] (ι : K → Type*)
  [∀ k, Fintype (ι k)]
def BaseChangeStatement : Prop :=
  ∀ (I : IFamily F ι) (I' : IFamily F' ι), IsFieldIntersection I → IsFieldIntersection I' →
    ∀ (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n →
      I V n L = ∑ᶠ W ∈ (V.map (MvPolynomial.map (algebraMap F F'))).minimalPrimes,
        (multAt (V.map (MvPolynomial.map (algebraMap F F'))) W : ℤ) * I' W n L
end BaseField
section Positivity
variable {K : Type*} [Fintype K] (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)]
def PositivityStatement : Prop :=
  ∀ I : IFamily F ι, IsFieldIntersection I →
    ∀ (V : Ideal (MRingOver F ι)) (n : ℕ), IsProjVarF V n →
      (∀ L : Fin n → K → ℤ, (∀ j k, 0 ≤ L j k) → 0 ≤ I V n L) ∧ 0 < I V n (fun _ _ => 1)
end Positivity
section Inhabit
variable (F : Type*) [Field F]
def PointIsVarStatement : Prop :=
  IsProjVarF (⊥ : Ideal (MRingOver F fun _ : Unit => Fin 1)) 0
def LineIsVarStatement : Prop :=
  IsProjVarF (⊥ : Ideal (MRingOver F fun _ : Unit => Fin 2)) 1
def LineSectionStatement : Prop :=
  IsRatSection (⊥ : Ideal (MRingOver F fun _ : Unit => Fin 2)) (fun _ => 1) (X ⟨(), 0⟩) 1 ∧
    ratDiv (⊥ : Ideal (MRingOver F fun _ : Unit => Fin 2)) (X ⟨(), 0⟩) 1 =
      Finsupp.single (Ideal.span {X ⟨(), 0⟩}) 1
def PointDegStatement : Prop :=
  ∀ I : IFamily F (fun _ : Unit => Fin 1), IsFieldIntersection I →
    I ⊥ 0 Fin.elim0 = 1
def LineDegStatement : Prop :=
  ∀ I : IFamily F (fun _ : Unit => Fin 2), IsFieldIntersection I →
    ∀ d : ℤ, I ⊥ 1 ![fun _ => d] = d
def QuadricStatement : Prop :=
  ∀ I : IFamily F (fun _ : Fin 2 => Fin 2), IsFieldIntersection I →
    I ⊥ 2 ![Pi.single 0 1, Pi.single 1 1] = 1 ∧ I ⊥ 2 ![Pi.single 0 1, Pi.single 0 1] = 0
end Inhabit
end ReciprocityTheory.ChartRestriction.G.AI.I1


