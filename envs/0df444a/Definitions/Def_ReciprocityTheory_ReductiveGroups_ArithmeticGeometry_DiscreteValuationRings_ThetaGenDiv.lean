-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenDiv
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:26.665505+00:00
-- url     : https://prove2.me/theorems/8997bb7a-cac7-4481-ba5a-3bc42d5d70f9
-- title:
--   Theta Gen Div
-- statement:
--   Definitions and structural lemmas for Theta Gen Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenDiv.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenLevel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
def expL (U : UnifPre I D A G) (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι)
    (σ : H0 U.LG.L 1) : Γ((thickObj R I e G).left, U.expW e p j₁ S jf jt) :=
  (res (inf_le_left.trans inf_le_left :
      U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
        (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ 1 *
    ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
      U.expW e p j₁ S jf jt ≤
        (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)).op).hom
      (((fstG I e G).left.app _).hom (σ.f j₁))
def expR (U : UnifPre I D A G) (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι)
    (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) : Γ((thickObj R I e G).left, U.expW e p j₁ S jf jt) :=
  ∑ α ∈ S.attach,
    ((thickObj R I e G).left.presheaf.map (homOfLE (U.expW_le_f e p j₁ jf jt α.2)).op).hom
        (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
      (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val
end ReciprocityTheory.ChartRestriction.G.DVR.TG
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
end ReciprocityTheory.ChartRestriction.G.DVR.TG


