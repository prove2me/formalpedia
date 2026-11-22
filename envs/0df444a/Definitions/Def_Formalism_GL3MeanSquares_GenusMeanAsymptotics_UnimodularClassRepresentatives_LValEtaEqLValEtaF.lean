-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:49.460302+00:00
-- url     : https://prove2.me/theorems/c8186a51-3883-4655-bda9-066db15d8f46
-- title:
--   LVal Eta Eq LVal Eta F
-- statement:
--   Definitions and structural lemmas for LVal Eta Eq LVal Eta F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LValEtaEqLValEtaF.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
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
namespace Regroup
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
theorem comap_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
end Regroup
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
end Formalism.HermitianLattices.Ext.L3


