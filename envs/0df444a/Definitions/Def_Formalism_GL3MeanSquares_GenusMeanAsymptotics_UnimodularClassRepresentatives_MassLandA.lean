-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:01.223804+00:00
-- url     : https://prove2.me/theorems/3306ba4f-f184-47d3-b921-3a9a4205ec1f
-- title:
--   Mass Land A
-- statement:
--   Definitions and structural lemmas for Mass Land A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandA.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
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
variable (K : Type) [Field K] [NumberField K] [StarRing K]
def conjAlg : K ≃ₐ[ℚ] K := (starRingAut : RingAut K).toRatAlgEquiv
abbrev cmF : IntermediateField ℚ K := IntermediateField.fixedField (Subgroup.zpowers (conjAlg K))
theorem conjAlg_apply (x : K) : conjAlg K x = star x := rfl
theorem mem_cmF_iff (x : K) : x ∈ cmF K ↔ star x = x := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h _ (Subgroup.mem_zpowers _)
  · intro h f hf
    have hs : conjAlg K ∈ MulAction.stabilizer (K ≃ₐ[ℚ] K) x :=
      MulAction.mem_stabilizer_iff.2 (by rw [AlgEquiv.smul_def, conjAlg_apply, h])
    have := MulAction.mem_stabilizer_iff.1 ((Subgroup.zpowers_le.2 hs) hf)
    rwa [AlgEquiv.smul_def] at this
theorem star_coe_cmF (x : cmF K) : star (x : K) = x := (mem_cmF_iff K x).1 x.2
instance : IsGalois (cmF K) K := IsGalois.of_fixed_field K (Subgroup.zpowers (conjAlg K))
def conjF : K ≃ₐ[cmF K] K :=
  { conjAlg K with commutes' := fun x => star_coe_cmF K x }
variable {K}
end Formalism.HermitianLattices.Ext.L3


