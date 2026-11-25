-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T14:40:06.387172+00:00
-- url     : https://prove2.me/theorems/62538ab8-9a4f-47e5-aca8-8af3acbbd004
-- title:
--   Comm Alg Functor Cohomology Two Eq Zero Of Is Initial
-- statement:
--   Definitions and structural lemmas for Comm Alg Functor Cohomology Two Eq Zero Of Is Initial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommAlgFunctorCohomologyTwoEqZeroOfIsInitial.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AbCoh.Vanish
def topInit {X : Scheme.{0}} (hX : IsAffineOpen (⊤ : X.Opens)) : IsInitial (op ⟨⊤, hX⟩ : AffOp X) :=
  IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, hX⟩ from le_top (a := U.unop.1))).op)
    fun _ _ ↦ rfl
end GlobalTheory.AbCoh.Vanish


