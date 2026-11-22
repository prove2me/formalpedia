-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:53.108817+00:00
-- url     : https://prove2.me/theorems/6bec3509-bbfa-41b8-a35a-0c6575978912
-- title:
--   Euler Fac Mul Conj Inv Split
-- statement:
--   Definitions and structural lemmas for Euler Fac Mul Conj Inv Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace IdealNormInequalities
def smallTerm (M : ℕ) (P : Ideal (𝓞 K)) : ℝ :=
  if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then
    -((-1 : ℝ) ^ M * Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)))
  else -((Ideal.absNorm P : ℝ) ^ (-(M : ℤ)))
end IdealNormInequalities
open IdealNormInequalities
end Formalism.HermitianLattices.Ext.L3


