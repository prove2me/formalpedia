-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:58.506798+00:00
-- url     : https://prove2.me/theorems/e9831afa-cdd3-489a-8490-4e4b4d691095
-- title:
--   Quasi Determinant Conj Inv
-- statement:
--   Definitions and structural lemmas for Quasi Determinant Conj Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/QuasiDeterminantConjInv.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix
def qF {R : Type*} [Ring R] {n : ℕ} (F : ℂ → Fin n → Fin n → R) (u : ℂ) : R :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) * (List.ofFn fun k : Fin n => F (u - (k : ℂ)) (σ k) k).prod
end PI.UnitaryGroupMassFormula.DSIC


