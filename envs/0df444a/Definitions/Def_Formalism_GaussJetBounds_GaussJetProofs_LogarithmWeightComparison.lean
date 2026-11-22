-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
-- name    : Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:26.433497+00:00
-- url     : https://prove2.me/theorems/786dca4b-0000-4c1b-ab15-4709fd4de8f0
-- title:
--   Logarithm Weight Comparison
-- statement:
--   Definitions and structural lemmas for Logarithm Weight Comparison, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LogarithmWeightComparison.lean

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Theorems.Thm_Formalism_FG_SolveVAux_low_P
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff low_P)
def truncBelow {K : Type u} [Field K] {τ : Type v} (N : ℕ) (f : MvPowerSeries τ K) :
    MvPowerSeries τ K :=
  fun m => if m.degree < N then coeff m f else 0
section Shift
variable {K : Type u} [Field K] {τ : Type v} [DecidableEq τ]
def genLogTrunc (l : ℕ) (p : τ → τ) (x : τ) (M : ℕ) : MvPowerSeries τ K :=
  ∑ e ∈ Finset.range M, ((l : K) ^ e)⁻¹ • (X (p^[e] x)) ^ ((l ^ 2) ^ e)
end Shift
end Formalism.DworkPowerSeriesWeights


