-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:11.073134+00:00
-- url     : https://prove2.me/theorems/0dc5a310-61df-4f50-9ded-e7c1b3edcda8
-- title:
--   Generator Scheme Properties
-- statement:
--   Definitions and structural lemmas for Generator Scheme Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
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
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory
namespace GenScheme
def pb {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, W)ˣ :=
  Units.map (f.appLE U W h).hom
section Calc
variable {X Y Z : Scheme.{0}}
end Calc
section One
variable {B Z : Scheme.{0}} (L : LB B) (b : Z ⟶ B)
def Compat (s : ∀ i : L.ι, Γ(Z, b ⁻¹ᵁ L.U i)ˣ) : Prop :=
  ∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_right : L.U i ⊓ L.U i' ≤ L.U i')) (s i') =
    pullU b _ (L.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : L.U i ⊓ L.U i' ≤ L.U i)) (s i)
variable (j : L.ι) (hj : ⊤ ≤ b ⁻¹ᵁ L.U j)
def extend (t : Γ(Z, ⊤)ˣ) (i : L.ι) : Γ(Z, b ⁻¹ᵁ L.U i)ˣ :=
  pb b (L.U j ⊓ L.U i) _ (fun x hx => ⟨hj trivial, hx⟩) (L.g j i) * res le_top t
variable {L}
end One
section Many
variable {B : Scheme.{0}} {κ : Type} {N : κ → LB B} {G : Scheme.{0}} {q : G ⟶ B}
  {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ}
variable (N q u) in

def Univ : Prop :=
  ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ),
    (∀ k, Compat (N k) b (s k)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i,
      (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val =
        (s k i).val
end Many
end GenScheme
end GlobalTheory


