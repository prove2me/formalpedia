-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:45.505025+00:00
-- url     : https://prove2.me/theorems/e68be81e-8873-4a76-9943-ee1e7dfa0e4a
-- title:
--   Card Unitary Reduction
-- statement:
--   Definitions and structural lemmas for Card Unitary Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryReduction.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff

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
namespace Cell
section Abs
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A A' C : Type*} [CommRing A] [StarRing A] [CommRing A'] [CommRing C] [StarRing C]
end Abs
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
def muQ {𝔭 : Ideal (𝓞 F)} {j : ℕ} (c : ℕ) {d : 𝓞 F} (hd : d ∈ 𝔭 ^ j) :
    (𝓞 K ⧸ extP K 𝔭 ^ c) →+ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)) :=
  (Submodule.mapQ (extP K 𝔭 ^ c) (extP K 𝔭 ^ (j + c)) (LinearMap.mulLeft (𝓞 K) (ι d)) (by
    intro a ha
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, pow_add]
    exact Ideal.mul_mem_mul ((mem_pow_iff 𝔭 j d).2 hd) ha)).toAddMonoidHom
end Cell
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable [Fact (IsFixF K F)]
end Formalism.HermitianLattices.Ext.L3.HU


