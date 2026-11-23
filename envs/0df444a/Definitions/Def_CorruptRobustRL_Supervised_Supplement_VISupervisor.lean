-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Supplement_VISupervisor
-- name    : CorruptRobustRL_Supervised_Supplement_VISupervisor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:10:54.677648+00:00
-- url     : https://prove2.me/theorems/98f63975-877e-4891-95e2-311e13517a4d
-- title:
--   Both abstract value-iteration inequalities, Condition C.2
-- statement:
--   Let $\mathcal T=(\overline Q,\underline Q,\mathcal A,\pi^{\mathrm{ucb}})$ be a Q-supervisor, and let $m=(\widehat r,\widehat p,b)$ be its model estimate. At every stage $h\in[H]$, state $x$ and action $a$, require both
--   $$\overline Q_h(x,a)\le\min\{H,\widehat r(x,a)+\widehat p(x,a)^\top\overline V_{h+1}+b(x,a)\},$$
--   $$\underline Q_h(x,a)\ge\max\{0,\widehat r(x,a)+\widehat p(x,a)^\top\underline V_{h+1}-b(x,a)\}.$$
--   Here $\overline V_h(x)=\overline Q_h(x,\pi_h^{\mathrm{ucb}}(x))$, $\underline V_h(x)=\max_{a\in\mathcal A_h(x)}\underline Q_h(x,a)$, and both terminal values are zero. The estimate is provided explicitly as a witness; its source ranges are a separate predicate.
--
--   These are one-sided inequalities. They do not require equality or being an output of the base algorithm.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 44, Condition C.2, (C.1)–(C.2)

import Definitions.Def_CorruptRobustRL_Supervised_Supervisor

namespace CorruptRobustRL.Supervised.Supplement

variable {X A : Type} [Fintype X]

/-- Both VI inequalities (C.1),(C.2) of Condition C.2, at every state/action,
not an equality or a requirement to be the output of Algorithm 2. -/
def IsVISupervisor (H : ℕ) (T : QSupervisor X A) (m : ModelEst X A) : Prop :=
  ∀ h < H, ∀ x a,
    T.Qbar h x a ≤ min (H : ℝ)
      (m.r x a + (∑ y, m.p x a y * T.Vbar H (h + 1) y) + m.b x a) ∧
    max 0 (m.r x a + (∑ y, m.p x a y * T.Vlow H (h + 1) y) - m.b x a) ≤
      T.Qlow h x a

end CorruptRobustRL.Supervised.Supplement


