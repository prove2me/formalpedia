-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:40:09.847393+00:00
-- url     : https://prove2.me/theorems/5e7d4e98-ba78-403d-a0d1-80186e3d6493
-- title:
--   Twist BCPf
-- statement:
--   Definitions and structural lemmas for Twist BCPf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/TwistBCPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
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
def TwistBaseChangeStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R)
    (k : ℕ), 1 ≤ k →
    ∀ (α : D.X), ∃ (m : ℕ) (b : Fin m → D.SecB k α), m = k ^ D.P.g ∧
      ∀ (R' : Type) [CommRing R'] (f : R →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b'
end ReciprocityTheory.ChartRestriction.G.DVR


