-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_DetDer
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_DetDer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:11.655886+00:00
-- url     : https://prove2.me/theorems/be3e0872-3ea6-4657-beb8-b789ae9ad94c
-- title:
--   Det Der
-- statement:
--   Definitions and structural lemmas for Det Der, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowDerivationChainRule/DetDer.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.RL.W
section General
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
end General
def REder (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) :
    Derivation K (MvPolynomial (Fin k × Fin k) K) (MvPolynomial (Fin k × Fin k) K) :=
  ∑ t : Fin k, (X (a, t) : MvPolynomial (Fin k × Fin k) K) • pderiv (b, t)
end PI.RL.W


