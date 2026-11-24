-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:32:58.2918+00:00
-- url     : https://prove2.me/theorems/d3619120-0369-4c1d-86a1-c248368cfac9
-- title:
--   Different Ideal Conditions
-- statement:
--   Definitions and structural lemmas for Different Ideal Conditions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferentIdealConditions.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion
namespace PfN
section
open Ideal UniqueFactorizationMonoid
end
section
open Ideal NumberField Polynomial
end
section
open NumberField IntermediateField Ideal
open scoped Pointwise
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
abbrev cm (P : Ideal (𝓞 (hostE ζ a b))) : Ideal (𝓞 (KinE ζ a b)) :=
  P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)))
end
end PfN
end Formalism.HermitianLattices.FiltrationBoundaryCriterion


