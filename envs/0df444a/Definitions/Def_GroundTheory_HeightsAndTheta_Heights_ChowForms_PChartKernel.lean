-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:54.623801+00:00
-- url     : https://prove2.me/theorems/ad2ec52e-9df0-4406-9d39-a337e5f264f0
-- title:
--   PChart Kernel
-- statement:
--   Definitions and structural lemmas for PChart Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace ChartKernel
variable {F : Type} [Field F] {n : ℕ}
variable (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
def chartSubst : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* MvPolynomial (Fin e × Fin n) (ChartInc I t e) :=
  eval₂Hom (C.comp ((chartX I t e).comp C))
    (Sum.elim (fun m => C (chartX I t e (X m)))
      (genSubst (fun m => chartX I t e (X m)) (fun m => chartX I t e (C (t m)))))
def chartEv : MvPolynomial (Fin e × Fin n) (ChartInc I t e) →+* ChartInc I t e :=
  eval₂Hom (RingHom.id _) (fun ij => chartIncHom I t e (X ij))
variable {I t e}
end ChartKernel
end
end GroundTheory.Heights₂.Heights


