-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:23.376813+00:00
-- url     : https://prove2.me/theorems/9f8dfb7f-a4b4-48cc-9cb2-2d76b735e40b
-- title:
--   Eq Single Of Degree Eq One
-- statement:
--   Definitions and structural lemmas for Eq Single Of Degree Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/EqSingleOfDegreeEqOne.lean

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
namespace Formalism.FG
namespace InjVAux
open MvPowerSeries
variable {R : Type*} [CommRing R] {τ : Type*}
def HasOrd (n : ℕ) (z : MvPowerSeries τ R) : Prop :=
  ∀ d : τ →₀ ℕ, d.degree < n → coeff d z = 0
def Good (N k : ℕ) (x x' : MvPowerSeries τ R) : Prop :=
  HasOrd k x ∧ HasOrd k x' ∧ HasOrd (N + k) (x - x')
end InjVAux
end Formalism.FG


