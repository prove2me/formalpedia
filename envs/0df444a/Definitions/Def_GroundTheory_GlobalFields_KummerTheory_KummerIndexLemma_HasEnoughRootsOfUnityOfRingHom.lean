-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
-- name    : GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:53.292065+00:00
-- url     : https://prove2.me/theorems/f4f071b2-db85-4c16-9bee-979c50a5b6aa
-- title:
--   Has Enough Roots Of Unity Of Ring Hom
-- statement:
--   Definitions and structural lemmas for Has Enough Roots Of Unity Of Ring Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Theorems.Thm_GroundTheory_Global_coe_integerEquivAdicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_ProfCoh_kummerPairingLeft_apply
import Theorems.Thm_GroundTheory_ProfCoh_kummerPairingRight_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coe_integerEquivAdicCompletionIntegers
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.ProfCoh.kummerPairingLeft_apply
attribute [local simp] GroundTheory.ProfCoh.kummerPairingRight_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero
namespace KummerIndex
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
abbrev localUnits : Subgroup (v.adicCompletion K)ˣ :=
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units
def localClass (p : ℕ) : Kˣ →* UnitsModPow (v.adicCompletion K) p :=
  (QuotientGroup.mk' (unitsPow (v.adicCompletion K) p)).comp
    (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K))
def localUnitClasses (p : ℕ) : Subgroup (UnitsModPow (v.adicCompletion K) p) :=
  (localUnits v).map (QuotientGroup.mk' (unitsPow (v.adicCompletion K) p))
def ordMod (p : ℕ) : (v.adicCompletion K)ˣ →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p))
  map_one' := by simp
  map_mul' x y := by
    have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
    rw [Units.val_mul, map_mul, log_mul hx hy, ← ofAdd_add]
    push_cast
    ring_nf
end KummerIndex
end GroundTheory.Global


