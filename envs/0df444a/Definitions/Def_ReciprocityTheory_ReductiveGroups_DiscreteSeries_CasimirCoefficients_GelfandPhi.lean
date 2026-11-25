-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:58.317903+00:00
-- url     : https://prove2.me/theorems/b83da6ca-6a97-5fe0-962e-23e1391c7c76
-- title:
--   Gelfand Phi
-- statement:
--   Definitions and structural lemmas for Gelfand Phi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPhi.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiffAt_phiM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
theorem phiM_contDiffOn (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (PhiM μ) (OmegaSet n) :=
  fun _ hz => (contDiffAt_phiM μ hz).contDiffWithinAt
def phiT (μ : Fin n → ℤ) : smoothS n :=
  ⟨(OmegaSet n).indicator (PhiM μ), (phiM_contDiffOn μ).congr fun _ hz => Set.indicator_of_mem hz _⟩
def xRev (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
  fun a b => -Matrix.single (Fin.rev a) (Fin.rev b) 1
def xTr (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
  fun a b => Matrix.single b a 1
end ReciprocityTheory.ChartRestriction.DS.S7


