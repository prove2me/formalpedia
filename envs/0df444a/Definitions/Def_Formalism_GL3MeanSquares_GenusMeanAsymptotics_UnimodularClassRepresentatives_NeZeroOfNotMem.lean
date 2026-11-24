-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:54.122119+00:00
-- url     : https://prove2.me/theorems/70769e23-e252-469f-9a39-7750951a6ec7
-- title:
--   Ne Zero Of Not Mem
-- statement:
--   Definitions and structural lemmas for Ne Zero Of Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NeZeroOfNotMem.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
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
namespace Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
structure IsUnif0 (𝔭 : Ideal (𝓞 F)) (π₀ s₀ : 𝓞 F) : Prop where
  mem : π₀ ∈ 𝔭
  notMem : π₀ ∉ 𝔭 ^ 2
  s_notMem : s₀ ∉ 𝔭
  le : Ideal.span {s₀} * 𝔭 ≤ Ideal.span {π₀}
end Formalism.HermitianLattices.Ext.L3.HU


