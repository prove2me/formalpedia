-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExtVStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExtVStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:01.993779+00:00
-- url     : https://prove2.me/theorems/ab4d47b1-b04c-467a-b867-703a9aae449b
-- title:
--   Ext VStatement
-- statement:
--   Definitions and structural lemmas for Ext VStatement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExtVStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
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
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory IsLocalRing NumberField
def ExtVStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (maximalIdeal V) V →
    ∀ (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V))), IsProper tK.G.hom →
    ∀ (m : SABMap tK t (spMap (algebraMap V (FractionRing V))))
      (m' : SABMap tK t' (spMap (algebraMap V (FractionRing V)))),
      ∃ ψ : SABMap t t' (𝟙 (Sp V)), m.φ ≫ ψ.φ = m'.φ
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


