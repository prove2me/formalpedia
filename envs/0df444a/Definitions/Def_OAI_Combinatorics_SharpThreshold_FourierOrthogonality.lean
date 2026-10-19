-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
-- name    : OAI_Combinatorics_SharpThreshold_FourierOrthogonality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:04:16.782773+00:00
-- url     : https://prove2.me/theorems/bc225283-1e50-4d39-80ad-75f18099b910
-- title:
--   Normalization facts for one biased coordinate
-- statement:
--   For one $p$-biased bit with weights $w_p(1)=p$ and $w_p(0)=1-p$, and $\chi_p(b)=([b]-p)/\sqrt{p(1-p)}$:
--   $$
--   \sum_{b\in\{0,1\}}w_p(b)=1,\qquad\sum_{b\in\{0,1\}}w_p(b)\chi_p(b)=0 .
--   $$
--
--   These are the one-coordinate cases of total mass one and mean zero for nonconstant characters. Products of them give orthogonality of the full basis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierOrthogonality.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierOrthogonality.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis

namespace OAI

universe u

noncomputable section
open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

@[simp] lemma scalarWeight_sum (p : ℝ) : ∑ b : Bool, scalarWeight p b = 1 := by
  simp [scalarWeight]

@[simp] lemma chi_mean (p : ℝ) :
    ∑ b : Bool, scalarWeight p b * chi p b = 0 := by
  simp only [Fintype.sum_bool, scalarWeight, chi, ite_true,
    Bool.false_eq_true, ite_false]
  ring

end Problem313.BiasedFourier

end

end OAI


