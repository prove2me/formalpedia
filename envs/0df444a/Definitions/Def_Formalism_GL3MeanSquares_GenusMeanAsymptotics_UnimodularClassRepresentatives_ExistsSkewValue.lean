-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:16.311975+00:00
-- url     : https://prove2.me/theorems/25538b57-86eb-4550-b320-55b0acac6de8
-- title:
--   Exists Skew Value
-- statement:
--   Definitions and structural lemmas for Exists Skew Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSkewValue.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.HU
open HermitianSublattices idealPowerSpanBounds
section Abstract
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]
end Abstract
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
abbrev Hq (H : Matrix κ κ (𝓞 K)) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))
variable [Fact (IsFixF K F)]
end Formalism.HermitianLattices.Ext.L3.HU


