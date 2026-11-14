-- Prove2me | Definitions.Def_APFPaper5_K1_CrossForm
-- name    : APFPaper5_K1_CrossForm
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:07:48.309069+00:00
-- url     : https://prove2.me/theorems/bc1200e0-1610-45f7-8d0b-e7853946239f
-- title:
--   Half the additive cost excess on a supplied real plane
-- statement:
--   Defines crossForm(q,x,y) as half of q(x+y)-q(x)-q(y) on two real coordinates. Bilinearity, positivity and any physical interpretation require additional hypotheses.
--
--   **Representation and scope.** The forward polarization expression matches the symmetric polarization for a quadratic q; for arbitrary q it is only a defined excess, not a bilinear form.
--
--   **Supplied data or hypotheses.** An arbitrary real function q on two real coordinates; no quadratic or positivity law.
--
--   **Claim boundaries.** A real coordinate pair is supplied, not constructed from exclusive physical marks. The family interface term is an analogy on a different domain and with a factor of one half; it is not an identified ledger supplier.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_CrossForm.lean; Sib v15, SHA-256 b940f099b33e7c33542e101ed7fbb6ccfb12e121afffe34019a2f0b2330f3f5f. [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'lines_or_section': '245-350'}]

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_CrossForm
title: The cross form of a cost on the plane of two exclusive marks
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:271-350 (polarization of a quadratic ledger). The codebank and the Paper 1
 Supplement call the same difference, on families, the interface term.
standing: a DEFINITION on a supplied cost q of combinations. A combination is a pair of real coefficients, one
 along a fixed mark (true) and one along the mark exclusive to it (false).
statement: crossForm q x y is half of what the cost of x and y together exceeds the sum of their costs.
-/
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper5.K1

/-- Half the excess of the cost of two combinations together over the sum of their costs. -/
noncomputable def crossForm (q : ℝ → ℝ → ℝ) (x y : Bool → ℝ) : ℝ :=
  (q (x true + y true) (x false + y false) - q (x true) (x false) - q (y true) (y false)) / 2

end APFPaper5.K1


