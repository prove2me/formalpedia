-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:34.857869+00:00
-- url     : https://prove2.me/theorems/3f72e56a-142e-4d81-be9c-e425e17439f4
-- title:
--   Power Series Diagonal Linear
-- statement:
--   Definitions and structural lemmas for Power Series Diagonal Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean

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
namespace PI.BeDiagZp.SubstW
def Rint (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [norm_mul]
    have := norm_nonneg a
    have := norm_nonneg b
    nlinarith
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha
def SerS {K : Type*} [CommRing K] (S : Subring K) (σ : Type*) : Subring (MvPowerSeries σ K) :=
  (MvPowerSeries.map S.subtype).range
end PI.BeDiagZp.SubstW
namespace PI.BeDiagZp
open SubstW
end PI.BeDiagZp
namespace PI.BeDiagZp.SubstW
variable {p : ℕ} [Fact p.Prime]
def expTr {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • F ^ n
end PI.BeDiagZp.SubstW
namespace PI.BeDiagZp
open SubstW
end PI.BeDiagZp


