-- Prove2me | solution 1 for AAInvW.ana_rdSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:23:16.919206+00:00
-- url     : https://prove2.me/submissions/db403d48-2191-43e6-89b3-bc0381ca05d1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Theorems.Thm_AAInvW_rd_extension_h
import Theorems.Thm_AAInvW_ana_sub


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
theorem _root_.solution (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {A B g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hA : inLH H A) (hB : inLH H B) (hg : inUH H g) :
    RdV (A - B) f g = RdV A f g - RdV B f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rd_extension_h n H E f F U g (A - B) hH hU hgU hg hF hfF (ana_sub hA hB), rd_extension_h n H E f F U g (A) hH hU hgU hg hF hfF (hA), rd_extension_h n H E f F U g (B) hH hU hgU hg hF hfF (hB), Matrix.mul_sub, map_sub]
end AAInvW
