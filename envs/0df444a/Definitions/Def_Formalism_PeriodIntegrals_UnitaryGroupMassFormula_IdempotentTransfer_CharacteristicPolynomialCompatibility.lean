-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:49.516299+00:00
-- url     : https://prove2.me/theorems/be5a62b8-ae87-4f7f-b369-f5e2e7e846ba
-- title:
--   Characteristic Polynomial Compatibility
-- statement:
--   Definitions and structural lemmas for Characteristic Polynomial Compatibility, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/CharacteristicPolynomialCompatibility.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.Tr
open PI.Dv Module
section Eps
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical in

def epsSum (P : Pair K G) : MonoidAlgebra K G :=
  ∑ h : P.H, (((P.chi h)⁻¹ : Kˣ) : K) • MonoidAlgebra.of K G (h : G)
end Eps
section Idem
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end Idem
section Alg
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
end Alg
section Lat
open NumberField
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K] {G : Type} [Group G] [Fintype G]
end Lat
end PI.Dv.Tr


