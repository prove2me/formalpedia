-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:08.303054+00:00
-- url     : https://prove2.me/theorems/27449d2d-b220-4763-9192-c21f3bda4ad8
-- title:
--   Cnt IOne Of Not Mem
-- statement:
--   Definitions and structural lemmas for Cnt IOne Of Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CntIOneOfNotMem.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
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
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
def mulW (𝔭 : Ideal (𝓞 F)) {w : 𝓞 K} (hw : w ∈ extP K 𝔭) (j : ℕ) : AQ K 𝔭 (j + 1) →+ AQ K 𝔭 (j + 2) :=
  (Submodule.mapQ (extP K 𝔭 ^ (j + 1)) (extP K 𝔭 ^ (j + 2)) (LinearMap.mulLeft (𝓞 K) w) (by
    intro z hz
    show w * z ∈ extP K 𝔭 ^ (j + 2)
    rw [pow_succ' _ (j + 1)]
    exact Ideal.mul_mem_mul hw hz)).toAddMonoidHom
theorem map_mem {𝔭 : Ideal (𝓞 F)} {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) : ι ϖ ∈ extP K 𝔭 :=
  Ideal.mem_map_of_mem _ h1
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds


