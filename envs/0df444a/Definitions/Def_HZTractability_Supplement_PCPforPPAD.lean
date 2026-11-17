-- Prove2me | Definitions.Def_HZTractability_Supplement_PCPforPPAD
-- name    : HZTractability_Supplement_PCPforPPAD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:27:50.001128+00:00
-- url     : https://prove2.me/theorems/cbe00ea2-4422-4dcb-82bc-0e3e02003267
-- title:
--   The PCP-for-PPAD conjecture (weak Pure-Circuit formulation)
-- statement:
--   The **PCP-for-PPAD conjecture**, in the formulation used by the paper: there is a rational $\delta$ with $0<\delta\le1$ such that weak $\delta$-Pure-Circuit (without the input-once restriction) is PPAD-hard, i.e. every problem in PPAD reduces to it by a polynomial-time search reduction.
--
--   The paper quotes [DFHM26, Theorem 2.2]: PCP for PPAD is equivalent to PPAD-hardness of weak $\delta$-Pure-Circuit for some fixed $\delta>0$, with or without the input-once restriction. The proposition is a hypothesis of Theorem 1.2 and is never asserted.
--
--   **Formalization Note** Of the equivalent forms the paper lists, the one without the input-once restriction is the weakest proposition, so a theorem assuming it is the strongest. PPAD-hardness is the published `CEPolytopeHard.PPADHard` over `QuasiStrictNE.PPAD` and `CardinalMatching.SearchReduces`. The reduction is polynomial-time, as in the paper's "polynomial-time formulation of the conjecture" (p.20), not quasilinear. Restricting $\delta$ to rationals loses nothing, because hardness for $\delta$ implies hardness for every smaller $\delta$.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §1.1, p.2 (PDF p.4); §5 and §5.1, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_HZTractability_Supplement_weakPureCircuit

set_option autoImplicit false

namespace HZTractability.Supplement

/-- **The PCP-for-PPAD conjecture, in the formulation the paper uses** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, §1.1, p.2 (PDF 4) and §5.1, p.20 (PDF 22)): "By
[DFHM26, Theorem 2.2], PCP for PPAD is equivalent to PPAD-hardness of weak δ-Pure-Circuit for some fixed
δ > 0, with or without the input-once restriction."

The proposition: there is a rational `δ` with `0 < δ ≤ 1` such that weak δ-Pure-Circuit (no
input-once restriction) is PPAD-hard. It is a hypothesis only; nothing asserts it.

**Formalization Note** Of the forms the paper lists as equivalent, the one without the input-once
restriction is the weakest proposition (hardness on a subclass of instances implies hardness on all),
so a theorem assuming it is the strongest. PPAD-hardness is the published `CEPolytopeHard.PPADHard`
(every problem of `QuasiStrictNE.PPAD` reduces to it by a polynomial-time Levin search reduction,
`CardinalMatching.SearchReduces`), the same notion as in the conclusion of Theorem 1.2. A rational
`δ` loses nothing: hardness for `δ` implies hardness for every smaller `δ'` (answers for `δ'` are
answers for `δ`). The reduction is polynomial-time, as on p.20 ("We use the polynomial-time
formulation of the conjecture"), not quasilinear. -/
def PCPforPPAD : Prop :=
  ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧ CEPolytopeHard.PPADHard (weakPureCircuit δ)

end HZTractability.Supplement


