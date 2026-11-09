-- Prove2me | Definitions.Def_CNFLearning873_Valiant_CSPBridge
-- name    : CNFLearning873_Valiant_CSPBridge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:04:24.637843+00:00
-- url     : https://prove2.me/theorems/2422c334-3012-4442-8503-b579ab7527c9
-- title:
--   Positive-width CNF as a finite Boolean CSP
-- statement:
--   Enumerate the finite target clause set and give each variable the domain $\{0,1\}$. Each constraint uses exactly its clause's variable scope, and accepts exactly the assignments satisfying that clause.
--
--   $$\operatorname{Sat}_{\mathrm{CSP}}(c,a)\iff\operatorname{Sat}_{\mathrm{CNF}}(c,\operatorname{decode}(a)).$$
--
--   This bridge provides access to the already published conditional local lemma target. It adds no intersection, degree, or counting-regime condition. Positive clause widths ensure nonempty CSP scopes; empty residual clauses are treated directly and are not passed through this bridge.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Theorem 3.1 and Boolean specialization, p.12 (PDF p.12)

import Definitions.Def_CNFLearning873_Valiant_CNF
import Definitions.Def_CountingLLL_DetCount_CSP

namespace CNFLearning873.Valiant

/-- Explicit Boolean-to-CSP bridge. Positive scopes only; empty residual clauses are
handled directly, never forced into this library representation. No CSP Standing or
Condition11 assumption is imposed. -/
noncomputable def toCSP {n : ℕ} (F : CNF n)
    (hp : ∀ c ∈ F, 0 < width c) : CountingLLL.DetCount.CSP where
  n := n
  m := F.toList.length
  q := fun _ => 2
  two_le_q := fun _ => le_rfl
  scope := fun i => support (F.toList.get i)
  scope_nonempty := fun i => Finset.card_pos.mp (hp _
    (Finset.mem_toList.mp (F.toList.get_mem i)))
  pred := fun i a => by
    classical
    exact decide (∃ v : ↥(support (F.toList.get i)),
      F.toList.get i v.val = some (decide (a v = 1)))

end CNFLearning873.Valiant


