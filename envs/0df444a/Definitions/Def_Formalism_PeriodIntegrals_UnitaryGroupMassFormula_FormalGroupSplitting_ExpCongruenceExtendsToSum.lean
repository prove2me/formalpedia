-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:27.585491+00:00
-- url     : https://prove2.me/theorems/d3537f07-de2c-4d58-89e7-6a1644a3ff0c
-- title:
--   Exp Congruence Extends To Sum
-- statement:
--   Definitions and structural lemmas for Exp Congruence Extends To Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]
def AllIn (W : Subring K) {σ : Type} (F : MvPowerSeries σ K) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ W
section Rename₂
variable {ι ι' : Type} [Fintype ι]
theorem hasSubst_inl : MvPowerSeries.HasSubst
    (fun j : ι ⊕ ι => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries ((ι ⊕ ι) ⊕ ι') K)) := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
def rho : MvPowerSeries (ι ⊕ ι) K →ₐ[K] MvPowerSeries ((ι ⊕ ι) ⊕ ι') K :=
  MvPowerSeries.substAlgHom hasSubst_inl
variable (g : Dat K) (hex0 : PowerSeries.constantCoeff g.ex = 0)
  (hl0 : PowerSeries.constantCoeff g.l = 0)
include hex0 hl0
end Rename₂
end PI.FglPhSplit.Wk
end


