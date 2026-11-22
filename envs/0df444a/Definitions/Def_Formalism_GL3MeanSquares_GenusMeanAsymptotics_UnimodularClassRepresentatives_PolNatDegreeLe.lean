-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_PolNatDegreeLe
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_PolNatDegreeLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:52.975278+00:00
-- url     : https://prove2.me/theorems/0b17460a-365d-4588-8d9e-97bfc10245f0
-- title:
--   Pol Nat Degree Le
-- statement:
--   Definitions and structural lemmas for Pol Nat Degree Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/PolNatDegreeLe.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
namespace Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Node
noncomputable def pol (A B : Matrix n n K) : K[X] := det ((X : K[X]) • A.map C + B.map C)
end Node
end Formalism.HermitianLattices.Ext.L3.HU


