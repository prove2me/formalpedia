-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CompatAlongOfSquare
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CompatAlongOfSquare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:51.370833+00:00
-- url     : https://prove2.me/theorems/85db4343-fae0-4a91-9ae4-6d874814b6b0
-- title:
--   Compat Along Of Square
-- statement:
--   Definitions and structural lemmas for Compat Along Of Square, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
namespace UnifPullRig
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Core
variable {S S' B B' T T' T₁ T₁' G G' A A' : Scheme.{0}}
def RigAlong {L : LB G} {M : LB A} {f : T ⟶ G} {p : T ⟶ A} (w : LB.Iso (L.pull f) (M.pull p))
    (ε : S ⟶ T) (i : S ⟶ B) {eG : B ⟶ G} {eA : B ⟶ A} (rL : LB.Gen (L.pull eG))
    (rM : LB.Gen (M.pull eA)) : Prop :=
  ∀ (q : (PUnit → M.ι) × (PUnit → L.ι)) (V : S.Opens)
    (h₁ : V ≤ ε ⁻¹ᵁ ((M.pull p).U q.1 ⊓ (L.pull f).U q.2))
    (h₂ : V ≤ i ⁻¹ᵁ (L.pull eG).U q.2) (h₃ : V ≤ i ⁻¹ᵁ (M.pull eA).U q.1),
    res h₁ (pullU ε _ (w.s q)) * res h₂ (pullU i _ (rL.s q.2)) = res h₃ (pullU i _ (rM.s q.1))
def CompatAlong {L : LB G} {M : LB A} {f : T ⟶ G} {p : T ⟶ A} {f₁ : T₁ ⟶ G} {p₁ : T₁ ⟶ A}
    (w₁ : LB.Iso (L.pull f₁) (M.pull p₁)) (w : LB.Iso (L.pull f) (M.pull p)) (m : T ⟶ T₁) : Prop :=
  ∀ (q : (PUnit → M.ι) × (PUnit → L.ι)) (V : T.Opens)
    (h₁ : V ≤ m ⁻¹ᵁ ((M.pull p₁).U q.1 ⊓ (L.pull f₁).U q.2))
    (h₂ : V ≤ (M.pull p).U q.1 ⊓ (L.pull f).U q.2),
    res h₁ (pullU m _ (w₁.s q)) = res h₂ (w.s q)
def Square {L : LB G} {M : LB A} {L' : LB G'} {M' : LB A'} {F : G' ⟶ G} {E : A' ⟶ A}
    {f : T ⟶ G} {p : T ⟶ A} {f' : T' ⟶ G'} {p' : T' ⟶ A'}
    (wL : LB.Iso L' (L.pull F)) (wM : LB.Iso M' (M.pull E))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) (h : T' ⟶ T) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
    E (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → F (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
    gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
      gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL'
variable {L : LB G} {M : LB A} {L' : LB G'} {M' : LB A'} {F : G' ⟶ G} {E : A' ⟶ A}
    {f : T ⟶ G} {p : T ⟶ A} {f' : T' ⟶ G'} {p' : T' ⟶ A'}
    {f₁ : T₁ ⟶ G} {p₁ : T₁ ⟶ A} {f₁' : T₁' ⟶ G'} {p₁' : T₁' ⟶ A'}
end Core
section Geometry
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)
end Geometry
end UnifPullRig
end GlobalTheory


