-- Prove2me | Definitions.Def_PricingWithTips3DM_87b54f5fbcefb1855733306a
-- name    : PricingWithTips3DM_87b54f5fbcefb1855733306a
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:28:45.216269+00:00
-- url     : https://prove2.me/theorems/aa7c6730-bb89-4c53-86eb-64a164122650
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteDropSemantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_5f13282bdcbed83283f67f78
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Affine source shift for terminal stack pop routes

Dropping a verifier-fixed number of rows from an affine progression advances
each base by that many strides and saturating-subtracts the shared count.
This is the descriptor-level form needed by pop routes.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Descriptor obtained after dropping a fixed prefix of progression rows. -/
def transitionStackRouteDropPrefix (amount : Nat)
    (progression : AffineUnaryTripleProgression) :
    AffineUnaryTripleProgression :=
  { base₁ := progression.base₁ + amount * progression.step₁
    base₂ := progression.base₂ + amount * progression.step₂
    base₃ := progression.base₃ + amount * progression.step₃
    step₁ := progression.step₁
    step₂ := progression.step₂
    step₃ := progression.step₃
    count := progression.count - amount }

/-- Advancing the bases and shortening the count denotes exactly `List.drop`
on the original affine row stream. -/
theorem transitionStackRouteDropPrefix_rows
    (amount : Nat) (progression : AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionRows
        (transitionStackRouteDropPrefix amount progression) =
      (affineUnaryTripleProgressionRows progression).drop amount := by
  rw [affineUnaryTripleProgressionRows_eq_ofFn,
    affineUnaryTripleProgressionRows_eq_ofFn]
  apply List.ext_get
  · simp [transitionStackRouteDropPrefix]
  · intro index hleft hright
    simp [transitionStackRouteDropPrefix]
    constructor
    · ring
    · constructor <;> ring

end CLRS.Chapter34.Turing.CookLevin


