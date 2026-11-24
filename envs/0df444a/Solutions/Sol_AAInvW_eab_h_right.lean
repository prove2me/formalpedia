-- Prove2me | solution 1 for AAInvW.eab_h_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:16:12.933164+00:00
-- url     : https://prove2.me/submissions/78ca43ed-c90a-4273-b88c-949c9abca0e9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
import Theorems.Thm_AAInvW_ana_rdRight
import Theorems.Thm_AAInvW_ana_conj_hpart1
import Theorems.Thm_AAInvW_ana_conj_hpart2
import Theorems.Thm_AAInvW_ana_EcH_ext
import Theorems.Thm_AAInvW_ana_conj_single
import Theorems.Thm_AAInvW_ana_mul


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
namespace AAInvW
theorem _root_.solution : EabHRight := by
  intro n H E _ _ f a b s g hH hf hs hg
  have hgs := ana_mul hg hs
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g * s) hgs
  change EcH H (Matrix.single a b 1) (fun x => f (x * s)) g =
    ∑ c, ∑ d, (s⁻¹ c a * s b d) • EcH H (Matrix.single c d 1) f (g * s)
  have h1 : EcH H (Matrix.single a b 1) (fun x => f (x * s)) g =
      EcH H (s⁻¹ * Matrix.single a b 1 * s) f (g * s) := by
    unfold EcH
    rw [ana_rdRight hH hs, ana_rdRight hH hs, ana_conj_hpart1 hH hs, ana_conj_hpart2 hH hs]
  rw [h1]
  simp only [ana_EcH_ext hH hU hgU hgs hF hfF]
  change anaPhi hH (fderiv ℝ F (g * s)) (g * s) (s⁻¹ * Matrix.single a b 1 * s) =
    ∑ c, ∑ d, (s⁻¹ c a * s b d) • anaPhi hH (fderiv ℝ F (g * s)) (g * s) (Matrix.single c d 1)
  rw [ana_conj_single, map_sum]
  simp only [map_sum, map_smul]
end AAInvW
