-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:41.383942+00:00
-- url     : https://prove2.me/theorems/7db139a4-339b-4063-ba6a-85b8dccbe7b6
-- title:
--   Card Quot Ext PPow
-- statement:
--   Definitions and structural lemmas for Card Quot Ext PPow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardQuotExtPPow.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjQ_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow

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
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
scoped instance starO : StarRing (𝓞 K) where
  star := conjO K
  star_involutive := L3.conjO_conjO
  star_mul a b := by
    show conjO K (a * b) = conjO K b * conjO K a
    rw [map_mul, mul_comm]
  star_add := map_add (conjO K)
scoped instance starQ [hF : Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    StarRing (𝓞 K ⧸ extP K 𝔭 ^ k) where
  star := NormLifting.conjQ _ (conjO_mem_pow hF.out 𝔭 k)
  star_involutive a := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    show NormLifting.conjQ _ _ (NormLifting.conjQ _ _ _) = _
    rw [NormLifting.conjQ_mk, NormLifting.conjQ_mk, L3.conjO_conjO]
  star_mul a b := by
    show NormLifting.conjQ _ _ (a * b) = NormLifting.conjQ _ _ b * NormLifting.conjQ _ _ a
    rw [map_mul, mul_comm]
  star_add := map_add _
def piQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) →+* (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ k))
def idQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k j : ℕ) :
    Ideal (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (extP K 𝔭 ^ j).map (Ideal.Quotient.mk _)
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds


