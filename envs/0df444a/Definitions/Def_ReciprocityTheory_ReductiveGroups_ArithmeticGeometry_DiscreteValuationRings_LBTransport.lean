-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:39.677156+00:00
-- url     : https://prove2.me/theorems/c453284e-1fc3-4e95-af5c-38846f51860b
-- title:
--   LBTransport
-- statement:
--   Definitions and structural lemmas for LBTransport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
section Regroup
open scoped Classical
end Regroup
section Tr
open scoped Classical
variable {X Y : Scheme.{0}} (L : LB X)
def tr (V : Y.Opens) (ψ : Y ⟶ X) (a b : L.ι) : Γ(Y, V)ˣ :=
  if h : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b) then res h (pullU ψ _ (L.g a b)) else 1
end Tr
section Transport
open scoped Classical
variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
  (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
def piece (ρ : (Y ⟶ X) → L.ι) : Y.Opens := LB.wchart L φ (ρ ∘ φ) ⊓ LB.wchart L φ' (ρ ∘ φ')
variable {L φ φ'}
lemma piece_le_wchart {W : Y.Opens} {ρ : (Y ⟶ X) → L.ι} : W ⊓ piece L φ φ' ρ ≤ LB.wchart L φ (ρ ∘ φ) :=
  fun _ hy => hy.2.1
variable (L φ φ')
def cand (t : LB.Gen (LB.LinComb L φ ε)) (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) :
    Γ(Y, LB.wchart L φ' j' ⊓ piece L φ φ' ρ)ˣ :=
  (∏ k', tr L (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ *
    res piece_le_wchart (t.s (ρ ∘ φ))
variable {L φ ε φ' ε'}
end Transport
section SecTransport
open scoped Classical
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
abbrev rs {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (x : Γ(Z, U)) : Γ(Z, V) :=
  (Z.presheaf.map (homOfLE h).op).hom x
def candS (s : LB.Sec (LB.LinComb L φ ε)) (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) :
    Γ(Y, LB.wchart L φ' j' ⊓ piece L φ φ' ρ) :=
  (((∏ k', tr L (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ :
    Γ(Y, LB.wchart L φ' j' ⊓ piece L φ φ' ρ)ˣ) : Γ(Y, _)) * rs piece_le_wchart (s.f (ρ ∘ φ))
end SecTransport
section FSum
open scoped Classical
variable {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
def fsum (φ : K → (Y ⟶ X)) (ε : K → ℤ) : (Y ⟶ X) →₀ ℤ := ∑ k, Finsupp.single (φ k) (ε k)
end FSum
end ReciprocityTheory.ChartRestriction.G.DVR


