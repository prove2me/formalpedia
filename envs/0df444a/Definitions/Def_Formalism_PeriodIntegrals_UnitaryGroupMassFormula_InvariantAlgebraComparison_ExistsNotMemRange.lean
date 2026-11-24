-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_ExistsNotMemRange
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_ExistsNotMemRange
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:14:35.706831+00:00
-- url     : https://prove2.me/theorems/88282d50-e70f-4342-95a4-86622ac1d7cd
-- title:
--   Exists Not Mem Range
-- statement:
--   Definitions and structural lemmas for Exists Not Mem Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantAlgebraComparison/ExistsNotMemRange.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_InvAlgOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.BridgeInvAlg
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
open Formalism.L2.SG.AdBridge
namespace GrothendieckRing
theorem exists_not_mem_range (I : AutInst) : ∃ ω : I.E, ω ∉ (algebraMap I.F I.E).range := by
  by_contra h
  push Not at h
  have h1 : Module.finrank I.F I.E = 1 := by
    rw [finrank_eq_one_iff_of_nonzero' (1 : I.E) one_ne_zero]
    intro w
    obtain ⟨c, hc⟩ := RingHom.mem_range.1 (h w)
    exact ⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩
  have h2 := I.cm.deg2
  omega
def om (I : AutInst) : I.E := (exists_not_mem_range I).choose
theorem om_not_mem (I : AutInst) : om I ∉ (algebraMap I.F I.E).range :=
  (exists_not_mem_range I).choose_spec
theorem linIndep_one_om (I : AutInst) : LinearIndependent I.F ![(1 : I.E), om I] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, rfl⟩
  · exfalso
    apply om_not_mem I
    refine ⟨-(s / t), ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have ht' : algebraMap I.F I.E t ≠ 0 := (map_ne_zero _).2 ht
    rw [map_neg, map_div₀, neg_eq_iff_eq_neg, div_eq_iff ht']
    linear_combination hst
def bE (I : AutInst) : Module.Basis (Fin 2) I.F I.E :=
  basisOfLinearIndependentOfCardEqFinrank (linIndep_one_om I)
    (by rw [Fintype.card_fin, I.cm.deg2])
end GrothendieckRing
open GrothendieckRing
end PI.UnitaryGroupMassFormula.BridgeInvAlg


