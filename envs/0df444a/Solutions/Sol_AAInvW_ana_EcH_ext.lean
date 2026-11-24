-- Prove2me | solution 1 for AAInvW.ana_EcH_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:38:38.64064+00:00
-- url     : https://prove2.me/submissions/88669dbf-db0f-4a7c-9ef7-e6fbf7b5cbdc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
import Theorems.Thm_AAInvW_ana_hpartMem
import Theorems.Thm_AAInvW_rd_extension_h


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace AAInvW
theorem _root_.solution (hH : HInvol H) {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    {g : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U) (hgU : g ∈ U) (hg : inUH H g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, inUH H h → f h = F h) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcH H Z f g = fderiv ℝ F g (g * hpart1 H Z) + Complex.I • fderiv ℝ F g (g * hpart2 H Z) := by
  unfold EcH
  rw [rd_extension_h n H E f F U g _ hH hU hgU hg hF hfF (ana_hpartMem hH Z).1,
    rd_extension_h n H E f F U g _ hH hU hgU hg hF hfF (ana_hpartMem hH Z).2.1]
end AAInvW
