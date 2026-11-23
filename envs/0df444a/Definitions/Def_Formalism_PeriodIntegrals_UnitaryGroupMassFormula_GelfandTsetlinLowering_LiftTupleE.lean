-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:44.74331+00:00
-- url     : https://prove2.me/theorems/f4581c2d-5e0b-460a-bd47-0f1c9dbaface
-- title:
--   Lift Tuple E
-- statement:
--   Definitions and structural lemmas for Lift Tuple E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleE.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD
def colWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (L : Finset (Fin K)) : Fin N → ℕ :=
  (∑ i : Fin n, ((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
    (if i.1 = 0 then (bb h lam sg i).toNat else 0) • initW N (i.1 + 1))) +
  ∑ k : Fin K, (if k ∈ L then initW N (sz k + 1) else initW N (sz k))
end PI.WGL.LTE


