-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:10.3142+00:00
-- url     : https://prove2.me/theorems/08f7ff8f-7475-46da-bacf-dee427b12e74
-- title:
--   Generic Fibre Ker Target
-- statement:
--   Definitions and structural lemmas for Generic Fibre Ker Target, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MixedFieldContraction/GenericFibreKerTarget.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AI.I4
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
section Pull
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
def imageZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) : Ideal (MRing ι) :=
  P'.comap (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom
def IsPullHerm (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (A : HermLine ι) (A' : HermLine ι') :
    Prop :=
  A'.a = pullDeg κ A.a ∧ ∀ z' : (Σ k', ι' k') → ℂ, A'.h z' = A.h fun p => z' (v p)
end Pull
section Fibre
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
abbrev FibreBlock (κ : K → K') : Type _ := {k' : K' // k' ∉ Set.range κ}
noncomputable instance FibreBlock.fintype (κ : K → K') : Fintype (FibreBlock κ) := Fintype.ofFinite _
abbrev fibreIdx (ι' : K' → Type*) (κ : K → K') : FibreBlock κ → Type _ := fun k => ι' k.1
structure GenFibre (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) where

  Φ : Type
  [fieldΦ : Field Φ]

  Φ' : Type
  [fieldΦ' : Field Φ']
  [alg : Algebra Φ Φ']

  x : (Σ k, ι k) → Φ

  x' : (Σ k', ι' k') → Φ'
  ker_x : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Φ) = imageZ v P'
  gen : ∀ c : Φ, ∃ f g : MRing ι, aeval x g ≠ 0 ∧ c = aeval x f / aeval x g
  genericFibre_ker_target : RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Φ') = P'
  compat : ∀ p, x' (v p) = algebraMap Φ Φ' (x p)
attribute [instance] GenFibre.fieldΦ GenFibre.fieldΦ' GenFibre.alg
def fibreIdeal {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (κ : K → K')
    (G : GenFibre v P') : Ideal (MRingOver G.Φ (fibreIdx ι' κ)) :=
  RingHom.ker (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) :
    MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] G.Φ')
def fibreDeg (κ : K → K') (a : K' → ℤ) : FibreBlock κ → ℤ := fun k => a k.1
end Fibre
section Graph
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
instance sumElim.fintype : ∀ k : K ⊕ K₂, Fintype (Sum.elim ι ι₂ k)
  | .inl k => inferInstanceAs (Fintype (ι k))
  | .inr k => inferInstanceAs (Fintype (ι₂ k))
def inlV : (Σ k, ι k) → (Σ k, Sum.elim ι ι₂ k) := fun p => ⟨Sum.inl p.1, p.2⟩
def inrV : (Σ k, ι₂ k) → (Σ k, Sum.elim ι ι₂ k) := fun p => ⟨Sum.inr p.1, p.2⟩
def graphMap (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) :
    MRing (Sum.elim ι ι₂) →+* MvPolynomial K₂ (MRing ι ⧸ P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (Ideal.Quotient.mk P (X ⟨k, i⟩))
    | ⟨.inr k, j⟩ => C (Ideal.Quotient.mk P (g ⟨k, j⟩)) * X k
def graphIdeal (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) : Ideal (MRing (Sum.elim ι ι₂)) :=
  RingHom.ker (graphMap P g)
def IsBasePtFree (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) : Prop :=
  ∀ (k₂ : K₂) (i : ∀ k, ι k), ∃ N : ℕ,
    (∏ k, (X ⟨k, i k⟩ : MRing ι)) ^ N ∈ P ⊔ Ideal.span (Set.range fun j : ι₂ k₂ => g ⟨k₂, j⟩)
def linForm {ι₂ : K → Type} (A : ∀ k, ι₂ k → ι k → ℤ) : (Σ k, ι₂ k) → MRing ι :=
  fun q => ∑ i, C (A q.1 q.2 i) * X ⟨q.1, i⟩
def linApply {ι₂ : K → Type} (A : ∀ k, ι₂ k → ι k → ℤ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι₂ k) → ℂ :=
  fun q => ∑ i, (A q.1 q.2 i : ℂ) * z ⟨q.1, i⟩
end Graph
section Coord
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def blockFnField {Ω : Type*} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = y p / y q}
def blkOf (b : Fin 2) : Unit → Fin 2 := fun _ => b
def blkV (κ : Type*) (b : Fin 2) : (Σ _ : Unit, κ) → (Σ _ : Fin 2, κ) := fun p => ⟨b, p.2⟩
end Coord
end ReciprocityTheory.ChartRestriction.G.AI.I4


