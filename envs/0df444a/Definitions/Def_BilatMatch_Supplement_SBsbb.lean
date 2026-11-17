-- Prove2me | Definitions.Def_BilatMatch_Supplement_SBsbb
-- name    : BilatMatch_Supplement_SBsbb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:27:40.040833+00:00
-- url     : https://prove2.me/theorems/1ae94ffe-36df-443d-ae01-561ec73e69ef
-- title:
--   Second best under ex-post strong budget balance $\mathrm{SB}_{\mathrm{sbb}}$
-- statement:
--   For a matching market $\mathcal I$, the **second best under ex-post strong budget balance** is
--   $$\mathrm{SB}_{\mathrm{sbb}}(\mathcal I)=\sup\Big\{\mathrm{GFT}(\mathcal M):\ \mathcal M\text{ admissible, BIC, IIR, and }\sum_{u}p_u(\theta)=0\text{ at every report profile }\theta\Big\},$$
--   a supremum in the extended reals over feasible mechanisms, with BIC and IIR at every real type and report.
--
--   It is the benchmark of the ex-post budget-balanced clause of Theorem 4.1; it is at most $\mathrm{SB}(\mathcal I)$, which only asks for nonnegative expected revenue.
--
--   **Formalization Note** Ex-post strong budget balance is `HasSum (fun u => pay θ u) 0` at every profile (the payments are summable and sum to zero). The mechanisms are the published `BilatMatch.Mechanism`.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490adbe231952acc5fc467ea7dfe37f237d7ce95248cd45c10451aedf4984), Theorem 4.1, p.17 (pdf p.19); §4.3, p.23 (pdf p.25)

import Mathlib
import Definitions.Def_BilatMatch_ValphaOn

open MeasureTheory

namespace BilatMatch.Supplement

open BilatMatch

variable {B S : Type*}

/-- **Second best under ex-post strong budget balance** (Liu, Qin, Wang, *From Bilateral Trade to
Matching Markets: Sharp Gains from Trade*, arXiv:2609.30702, held version, sha256 ff1490ad…,
Theorem 4.1, p.17 (pdf p.19): "The second-best guarantee also holds under ex-post strong budget
balance, as a supremum over feasible mechanisms"; §4.3, p.23).

`SBsbb I = sup { GFT(M) : M admissible, BIC and IIR at every real type and report, and at every
report profile θ the payments sum to zero }`, an `EReal` supremum.

**Formalization Note** Ex-post strong budget balance is `HasSum (fun u => pay θ u) 0` at every
profile `θ` (the payments of all agents are summable and sum to `0`; for finitely many agents this is
`∑_u p_u(θ) = 0`). The mechanisms, admissibility, BIC and IIR are the published ones of
`BilatMatch.Mechanism`, with the whole-line report domain, as for `SB`. The no-trade mechanism is in
the set, so it is nonempty. -/
noncomputable def SBsbb (I : Market B S) : EReal :=
  ⨆ (A : Mechanism I) (_ : A.Admissible ∧ A.IsBICOn (wholeLine B S) ∧
      A.IsIIROn (wholeLine B S) ∧ ∀ θ, HasSum (fun u => A.pay θ u) 0),
    ((A.GFT : ℝ) : EReal)

end BilatMatch.Supplement


