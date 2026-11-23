-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_LatticeInjective
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_LatticeInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:59.946871+00:00
-- url     : https://prove2.me/theorems/2c9cf4fd-ab14-4870-a461-13c427f7162b
-- title:
--   Lattice Injective
-- statement:
--   Definitions and structural lemmas for Lattice Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/LatticeInjective.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EagonNorthcottZ
open MvPolynomial
abbrev Ex (D : ℕ) : P D ≃ₐ[ℤ] MvPolynomial (Fin D) (MvPolynomial (Fin D) ℤ) := sumAlgEquiv ℤ (Fin D) (Fin D)
def cmp {D : ℕ} (β : Fin D →₀ ℕ) (f : P D) : P D := rename Sum.inr (coeff β (Ex D f))
end PI.EagonNorthcottZ


