-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_TateTransport
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_TateTransport
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:44:33.236287+00:00
-- url     : https://prove2.me/theorems/dd546abd-7372-41cd-bb6c-b6d0e902060b
-- title:
--   Tate Transport
-- statement:
--   Definitions and structural lemmas for Tate Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/TateTransport.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
def TateTransportStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (Dw : Datum H),
    letI := H.starRing
    ∀ I₀ : TateIso Dw F (TF (R := R) F ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => WeilIs t.G t.PP.L n g g' (unitOn c)),
      ∃ I₁ : TateIso Dw F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
          (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c)),
        ∀ n, I₁.ζ n = I₀.ζ n
end ReciprocityTheory.ChartRestriction.G.H1


