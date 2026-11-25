-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
-- name    : GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:25:10.860946+00:00
-- url     : https://prove2.me/theorems/2a2b104a-e957-4a06-9a3f-0125fdc8c457
-- title:
--   Finite Coord
-- statement:
--   Definitions and structural lemmas for Finite Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteCoord.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
namespace AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
abbrev traceDual : Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b
def localCoord (v : HeightOneSpectrum (𝓞 K)) (i : ι) :
    CompletionsOver L v →ₗ[v.adicCompletion K] v.adicCompletion K :=
  ((Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i).comp
    (tensorEquiv L v).symm.toLinearEquiv.toLinearMap
end AdeleBaseChange
end
end GroundTheory.Global


