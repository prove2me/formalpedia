-- Prove2me | Definitions.Def_CalibeatBandit_calibeatPolicy
-- name    : CalibeatBandit_calibeatPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:42.898929+00:00
-- url     : https://prove2.me/theorems/958f7a93-a765-440e-99bf-da1a64ce7c81
-- title:
--   The bandit calibeating learner as a policy
-- statement:
--   The **bandit calibeating learner** with parameters $(\eta,\mu)$ is the policy that in round $t$ plays $p_t=(1-\mu)x_t+\mu u$, computed by the bandit calibeating algorithm from the recommended actions $J_1,\dots,J_t$, its own past actions $I_s$ and the observed rewards $y_s(I_s)$, $s<t$. It never sees an unplayed reward.
--
--   The definition also names, for a run of the protocol driven by any policy, the algorithm's $x_t(\omega)$, $p_t(\omega)$ and $v_t(\omega)$ along the realized history.
--
--   **Formalization Note** `calibeatPolicy K η μ t J I r = algP η μ J I r t`.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §3.2, pp.10–11 (PDF 10–11); Theorem 3.2, p.11

import Mathlib
import Definitions.Def_CalibeatBandit_ProtocolRun
import Definitions.Def_CalibeatBandit_algState

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory

/-- **The bandit calibeating learner** with learning rate `η` and exploration parameter `μ`, as a
policy: in round `t` it plays `p_t = (1 − μ) x_t + μ u` (`algP`), computed from the recommended
actions `J_1, …, J_t`, its own past actions `I_s` and observed rewards `y_s(I_s)`, `s < t`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §3.2,
pp.10–11 ("the bandit feedback algorithm specified above"), with every internal learner
instantiated by (3.3), starting from uniform weights (Theorem 3.2, p.11).

**Formalization Note.** The policy reads only `J s` for `s ≤ t` and `I s`, `r s` for `s < t`
(see `algState`); in particular it never sees an unplayed reward. -/
noncomputable def calibeatPolicy (K : ℕ) (η μ : ℝ) : Policy K :=
  fun t J I r => algP η μ J I r t

namespace ProtocolRun

variable {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {policy : Policy K}

/-- `x_t(ω)`: the algorithm's solution of (3.1) along the realized history of the run. -/
noncomputable def algX (run : ProtocolRun K T P policy) (η μ : ℝ) (t : ℕ) (ω : Ω) : Fin K → ℝ :=
  CalibeatBandit.algX η μ (fun s => run.J s ω) (fun s => run.I s ω) (fun s => run.obs s ω) t

/-- `p_t(ω)`: the algorithm's mixed strategy along the realized history of the run. -/
noncomputable def algP (run : ProtocolRun K T P policy) (η μ : ℝ) (t : ℕ) (ω : Ω) : Fin K → ℝ :=
  CalibeatBandit.algP η μ (fun s => run.J s ω) (fun s => run.I s ω) (fun s => run.obs s ω) t

/-- `v_t(ω)`: the algorithm's corrected reward estimate along the realized history of the run. -/
noncomputable def algV (run : ProtocolRun K T P policy) (η μ : ℝ) (t : ℕ) (ω : Ω) : Fin K → ℝ :=
  CalibeatBandit.algV η μ (fun s => run.J s ω) (fun s => run.I s ω) (fun s => run.obs s ω) t

end ProtocolRun

end CalibeatBandit


