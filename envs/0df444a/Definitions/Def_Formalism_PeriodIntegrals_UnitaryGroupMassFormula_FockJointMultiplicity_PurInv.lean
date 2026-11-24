-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:09.487892+00:00
-- url     : https://prove2.me/theorems/78d62554-6df3-4db3-94af-33a588a94a38
-- title:
--   Pur Inv
-- statement:
--   Definitions and structural lemmas for Pur Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurInv.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PI.FJMB
variable {σ : Type*}
def fill {K : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (M : Fin m → Fin n → K) (p : σ → K) : σ → K :=
  Function.extend ι (fun x => M x.1 x.2) p
def rowAddM {K : Type*} [Field K] {m n : ℕ} (M : Fin m → Fin n → K) (a b : Fin m) (t : K) : Fin m → Fin n → K :=
  fun i k => if i = b then M i k + t * M a k else M i k
def colAddM {K : Type*} [Field K] {m n : ℕ} (M : Fin m → Fin n → K) (c d : Fin n) (t : K) : Fin m → Fin n → K :=
  fun i k => if k = d then M i k + t * M i c else M i k
end PI.FJMB


