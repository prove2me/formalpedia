-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_PottsThresholds
-- name    : ZeroFreeRRG_Hardcore_PottsThresholds
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T04:51:12.979412+00:00
-- url     : https://prove2.me/theorems/b915c778-084e-4a23-a0ec-a128e92f3991
-- title:
--   Potts and coloring replica-symmetry-breaking thresholds
-- statement:
--   For degree $d$ and $q$ states, let $T_{d,q}$ consist of $\beta\in(0,1)$ for which some admissible Potts cavity law has positive Bethe functional. The Potts threshold is
--
--   $$\beta_{\rm RSB}(d,q)=\sup T_{d,q},\qquad\sup\varnothing=0.$$
--
--   For $q$-colorings, let $U_q$ consist of real degrees $r\ge3$ with a positive witness for the interpolated degree-$r$ Bethe functional at $\beta=0$. The coloring threshold is $d_{\rm RSB}(q)=\inf U_q$, with $\inf\varnothing=+\infty$. These thresholds define the parameter ranges in the Potts and coloring zero-freeness theorem.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, equations (32) and (34), printed pp. 33 and 36.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical
namespace ZeroFreeRRG.Hardcore

/-- Positive-witness parameters in the antiferromagnetic Potts model, equation (32). -/
def pottsWitness (d q : ℕ) : Set ℝ :=
  {β | 0 < β ∧ β < 1 ∧ ∃ ν ∈ cavityLaws (.potts q) β, 0 < betheK (.potts q) β d ν}

/-- Potts replica-symmetry-breaking parameter, with supremum of the empty set set to zero. -/
noncomputable def betaRSB (d q : ℕ) : ℝ :=
  if pottsWitness d q = ∅ then 0 else sSup (pottsWitness d q)

/-- Positive-witness real degrees for proper colourings, equation (34). -/
def coloringWitness (q : ℕ) : Set ℝ :=
  {r | 3 ≤ r ∧ ∃ ν ∈ cavityLaws (.potts q) 0, 0 < betheR (.potts q) 0 r ν}

/-- Colouring degree threshold in the extended reals, with infimum of the empty set equal to infinity. -/
noncomputable def coloringDegreeRSB (q : ℕ) : EReal :=
  sInf ((fun r : ℝ => (r : EReal)) '' coloringWitness q)

end ZeroFreeRRG.Hardcore


