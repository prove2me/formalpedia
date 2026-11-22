-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:42.079816+00:00
-- url     : https://prove2.me/theorems/b72ea0e5-bed6-4aa6-96bc-21a26ab7535d
-- title:
--   EJoint
-- statement:
--   Definitions and structural lemmas for EJoint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EJoint.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_EntryDegree
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
namespace MinorFormHomogeneity
section Lin
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
def Amat (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) :
    TpV ν r1 ⊕ ZV ν r0 r1 → ZV ν r0 r1 → K
  | Sum.inl t, x => if t = (x.1, x.2.2) then (if x.1 ∈ TT then ξ x.1 x.2.1 else 0) else 0
  | Sum.inr y, x => if y = x then 1 else 0
end Lin
end MinorFormHomogeneity
end Formalism.InvariantFactorPaths.G7


