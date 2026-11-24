-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:48.644066+00:00
-- url     : https://prove2.me/theorems/bfbf72b9-a6e0-49be-aed4-9adc48052250
-- title:
--   Highest Weight Multiplicity
-- statement:
--   Definitions and structural lemmas for Highest Weight Multiplicity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl
namespace Hom
variable {R : Type} [CommRing R] {k : ℕ}
def Good (wt : Fin k × Fin k → ℤ) (δ d : ℤ) (p : Polynomial (MvPolynomial (Fin k × Fin k) R)) :
    Prop :=
  ∀ i : ℕ, IsWeightedHomogeneous wt (p.coeff i) (d + i * δ)
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}
end Hom
open Hom
end PI.OddDualWeyl


