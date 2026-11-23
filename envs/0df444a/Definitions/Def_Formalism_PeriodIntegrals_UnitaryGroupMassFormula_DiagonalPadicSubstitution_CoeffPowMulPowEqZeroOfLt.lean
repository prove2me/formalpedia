-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:54.398792+00:00
-- url     : https://prove2.me/theorems/02548d02-8c2c-4823-a212-7b41be6d8bdd
-- title:
--   Coeff Pow Mul Pow Eq Zero Of Lt
-- statement:
--   Definitions and structural lemmas for Coeff Pow Mul Pow Eq Zero Of Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
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
namespace PI.BeDiagZp
open MvPowerSeries
namespace IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
def ballSub (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
def expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • f ^ n
end IntegralPowerSeriesBall
open IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
end PI.BeDiagZp


