-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:04.288669+00:00
-- url     : https://prove2.me/theorems/65ada41e-5572-461f-a2f5-162d4f0b9fec
-- title:
--   Height V
-- statement:
--   Definitions and structural lemmas for Height V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.FG.HeightVAux
open MvPowerSeries Formalism.G Formalism.LT
section Rename
variable {K : Type*} [Field K] {l m : ℕ} [NeZero m]
end Rename
section Subst
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [DecidableEq ι] {τ : Type*}
end Subst
section Padic
variable {l : ℕ} [Fact l.Prime]
def liftZ {σ : Type*} (g : MvPowerSeries σ ℚ_[l]) (hg : IntegralMv g) : MvPowerSeries σ ℤ_[l] :=
  fun n => ⟨coeff n g, hg n⟩
end Padic
section Main
end Main
end Formalism.FG.HeightVAux
namespace Formalism.FG
end Formalism.FG


