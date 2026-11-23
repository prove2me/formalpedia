-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:37.469484+00:00
-- url     : https://prove2.me/theorems/17141112-f191-46e6-a50b-71771764dfa2
-- title:
--   Twist BC
-- statement:
--   Definitions and structural lemmas for Twist BC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/TwistBC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
def TwistBCSpanStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (k : ℕ), 1 ≤ k → ∀ (α : D.X)
    (R' : Type) [CommRing R'] [IsLocalRing R'] (f : R →+* R'), IsLocalHom f →
    ∀ s' : LB.Sec (LB.LinComb D.P.L
        (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i)
        (DegPre.famε k)),
      ∃ (n : ℕ) (r : Fin n → Γ(Spec (CommRingCat.of R'), ⊤)) (s : Fin n → D.SecB k α),
        ∀ j, s'.f j = ∑ i,
          ((Over.mk (Spec.map (CommRingCat.ofHom f)) ⊗ D.P.A).left.presheaf.map (homOfLE le_top).op).hom
            ((fst (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left.appTop.hom (r i)) *
          ((Over.mk (Spec.map (CommRingCat.ofHom f)) ⊗ D.P.A).left.presheaf.map
            (homOfLE (wchart_comp_le D.P.L (DegPre.famφB D α)
              (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left j)).op).hom
            (((snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left.app _).hom ((s i).f j))
end ReciprocityTheory.ChartRestriction.G.DVR


