-- Prove2me | Definitions.Def_IPMJumpLB_IsJump
-- name    : IPMJumpLB_IsJump
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:25.12341+00:00
-- url     : https://prove2.me/theorems/a5df5910-caaf-4dff-adf9-39958377cb0c
-- title:
--   Jump between $\eta$-iterates (Definition 2.2)
-- statement:
--   A **jump** is a move from an $\eta$-iterate $(x, s, f)$ to another $\eta$-iterate $(x', s', f')$ such that at least one of the following holds: the slacks satisfy
--   $$
--   \tfrac12 \le \frac{s'_e}{s_e} \le 2 \quad \text{for all } e \in E, \tag{2}
--   $$
--   or the flows satisfy
--   $$
--   \tfrac12 \le \frac{f'_e}{f_e} \le 2 \quad \text{for all } e \in E. \tag{3}
--   $$
--   The vector that is not constrained in this way may change arbitrarily. This models one step of an $\ell_\infty$ path following interior point method, primal or dual.
--
--   **Formalization Note** Both endpoints are required to be $\eta$-iterates, so every denominator is a positive real.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Definition 2.2, Eqs. (2)–(3), p.3

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_slack
import Definitions.Def_IPMJumpLB_IsEtaIterate

namespace IPMJumpLB

/-- Definition 2.2 (Jump) (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), p.3): a move from an η-iterate `p = (x, f)` to another η-iterate
`q = (x', f')` such that the slacks satisfy `1/2 ≤ s'_e / s_e ≤ 2` for all arcs `e` (2), or the
flows satisfy `1/2 ≤ f'_e / f_e ≤ 2` for all arcs `e` (3). The vector not constrained in this way
may change arbitrarily.

**Formalization Note** Both endpoints are required to be η-iterates, so all denominators are
positive reals. -/
def IsJump {V E : Type*} [Fintype E] [DecidableEq V] (I : FlowInstance V E) (η : ℝ)
    (p q : (V → ℝ) × (E → ℝ)) : Prop :=
  IsEtaIterate I η p.1 p.2 ∧ IsEtaIterate I η q.1 q.2 ∧
    ((∀ e, 1 / 2 ≤ slack I q.1 e / slack I p.1 e ∧ slack I q.1 e / slack I p.1 e ≤ 2) ∨
      (∀ e, 1 / 2 ≤ q.2 e / p.2 e ∧ q.2 e / p.2 e ≤ 2))

end IPMJumpLB


