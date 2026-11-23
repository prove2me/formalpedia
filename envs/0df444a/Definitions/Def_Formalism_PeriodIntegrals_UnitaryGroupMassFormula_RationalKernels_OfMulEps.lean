-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:04.727777+00:00
-- url     : https://prove2.me/theorems/c990ab9a-0d3d-4e81-8a9f-40c1baa9956c
-- title:
--   Of Mul Eps
-- statement:
--   Definitions and structural lemmas for Of Mul Eps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/OfMulEps.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}
variable (M : GMap K σ G T EE ρE)
def L (z : MonoidAlgebra K G) : Module.End ℂ M.V := ∑ g, σ (z.coeff g) • M.rho g
end PI.Dv.RK


