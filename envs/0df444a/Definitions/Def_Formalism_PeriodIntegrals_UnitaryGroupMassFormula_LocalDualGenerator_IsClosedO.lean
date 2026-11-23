-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:12.901435+00:00
-- url     : https://prove2.me/theorems/6901009c-e7bb-4090-ac2a-adb8b2c67443
-- title:
--   Is Closed O
-- statement:
--   Definitions and structural lemmas for Is Closed O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing
namespace PI.LocDualGen.FpU
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
theorem t2 : T2Space K := by
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed, ← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hv : valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨Units.mk0 _ hv, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ h0
  have hz' : valuation K z < valuation K x := hz
  have h0' : x + z = 0 := h0
  have : z = -x := by linear_combination h0'
  rw [this, Valuation.map_neg] at hz'
  exact lt_irrefl _ hz'
theorem isClosed_O : IsClosed ((𝒪[K] : Set K)) := by
  haveI : T2Space K := t2 (K := K)
  exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).isClosed
theorem iota_mem (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    algebraMap ℚ_[l] K (a : ℚ_[l]) ∈ 𝒪[K] := by
  have hcl : IsClosed {a : ℤ_[l] | algebraMap ℚ_[l] K (a : ℚ_[l]) ∈ 𝒪[K]} :=
    (isClosed_O (K := K)).preimage (hcont.comp continuous_subtype_val)
  refine PadicInt.denseRange_intCast.induction_on a hcl ?_
  intro n
  simp only [Set.mem_setOf_eq, PadicInt.coe_intCast, map_intCast]
  exact intCast_mem _ n
def iotaR (hcont : Continuous (algebraMap ℚ_[l] K)) : ℤ_[l] →+* 𝒪[K] :=
  ((algebraMap ℚ_[l] K).comp (PadicInt.Coe.ringHom (p := l))).codRestrict 𝒪[K]
    (fun a => iota_mem K l hcont a)
section Res
variable [CharP 𝓀[K] l]
abbrev algRes : Algebra (ZMod l) 𝓀[K] := ZMod.algebra _ l
attribute [local instance] algRes
abbrev fdim : ℕ := Module.finrank (ZMod l) 𝓀[K]
def bb : Module.Basis (Fin (fdim K l)) (ZMod l) 𝓀[K] := Module.finBasis (ZMod l) 𝓀[K]
def blift (i : Fin (fdim K l)) : 𝒪[K] := (residue_surjective (bb K l i)).choose
def Phi (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) : 𝒪[K] :=
  ∑ i, iotaR K l hcont (c i) * blift K l i
end Res
end PI.LocDualGen.FpU


