-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:25.613294+00:00
-- url     : https://prove2.me/theorems/4f45163a-e979-415c-b59e-c92d34fa4435
-- title:
--   Has Subst Ren
-- statement:
--   Definitions and structural lemmas for Has Subst Ren, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/HasSubstRen.lean

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime]
def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha
section Rename₂
variable {σ τ : Type} [Finite σ] (r : σ → τ)
theorem hasSubst_ren : HasSubst (fun s => (X (r s) : MvPowerSeries τ ℂ_[p])) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_X _)
def ren : MvPowerSeries σ ℂ_[p] →ₐ[ℂ_[p]] MvPowerSeries τ ℂ_[p] :=
  substAlgHom (hasSubst_ren r)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hl0 : PowerSeries.constantCoeff l = 0)
end Rename₂
end PI.UnitaryGroupMassFormula.PhDualGram
end


