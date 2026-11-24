-- Prove2me | Definitions.Def_RetirePartialInfo_Duality_Supplement_Verification
-- name    : RetirePartialInfo_Duality_Supplement_Verification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:21:40.135848+00:00
-- url     : https://prove2.me/theorems/6742569b-c57d-436c-95ed-9ab43ef65234
-- title:
--   Propositions 3.1–3.2 context (corrected growth reading) — local strong-solution classes used in Theorem 3.3
-- statement:
--   The supplied post-retirement function solves PDE (30), has $C^{1,2,2}$ regularity through the time boundary, and lies in some local $W_q^{1,2,2}$ with $q\ge3$. Its polynomial control covers both ends of the multiplier axis:
--
--   $$|v|+|\partial_yv|+|\partial_pv|\le C(1+y^k+y^{-k}),\qquad C,k>0.$$
--
--   The supplied VI function solves (32), is bounded, has its $C^1$ continuous representative, and lies in some local $W_q^{1,2,2}$ with $q\ge3$. These are local verification classes, distinct from the global existence claims refuted in the other milestones.
--
--   No sign estimate, inverse range, contact geometry, optimal stopping property or budget equality is included in these classes. They are conditions on the source's supplied functions, not structures postulating that such functions exist.
--
--   **Formalization Note** Appendix A's $v=-y^\phi w/\phi$ with bounded $w$ and $\partial_pw$ supports two-sided polynomial control. The one-sided estimate (31) fails for $\gamma>1$ when $\partial_pw\ne0$; this repaired verification reading excludes no CRRA parameter regime. The $C^1$ VI representative is the one specified on p.20 and in Appendix D.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), pp. 17–19, Propositions 3.1–3.2, and pp. 35–39, Appendices A–D

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Supplement_Restarted

open MeasureTheory Set Filter
open scoped Topology ENNReal
set_option autoImplicit false

namespace RetirePartialInfo.Duality.Supplement

/-- Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553
(version of June 8, 2021), pp.17–19, Propositions 3.1–3.2, and pp.35–39, Appendices A–D.
The strong solution class for the post-retirement function supplied to Theorem 3.3.
**Formalization Note.** There is no global W_q condition (the printed global existence
claim is refuted separately). The polynomial control allows both ends of the y-axis:
Appendix A has v=-y^φ w/φ and bounded w and ∂p w, so ∂p v can grow at infinity
when γ>1. The one-sided bound (31) would exclude this source regime. No derivative sign,
inverse range, budget equality or optimality is assumed. -/
def PostSolution (a : Data) (v : Value) : Prop :=
  PDE30 a v ∧ C122 a.par.T v ∧
  (∃ q : ℝ, 3 ≤ q ∧ LocalW a.par.T q v) ∧
  ∃ C k : ℝ, 0 < C ∧ 0 < k ∧ ∀ z ∈ timeClosure a.par.T,
    |flatten v z| + |dy v (z 0) (z 1) (z 2)| + |dp v (z 0) (z 1) (z 2)| ≤
      C * (1 + (z 1)^k + (z 1)^(-k))

/-- The bounded, locally Sobolev strong VI solution supplied to Theorem 3.3.
**Formalization Note.** C¹ up to the time boundary is the continuous representative
specified in Theorem 3.2 and Appendix D. None of (37)–(39), contact-set geometry,
stopping optimality or primal feasibility is built into this solution class. -/
def ObstacleSolution (a : Data) (f : Value) : Prop :=
  VI32 a f ∧ C1 a.par.T1 f ∧
  (∃ q : ℝ, 3 ≤ q ∧ LocalW a.par.T1 q f) ∧
  ∃ C : ℝ, ∀ z ∈ timeClosure a.par.T1, |flatten f z| ≤ C

end RetirePartialInfo.Duality.Supplement


