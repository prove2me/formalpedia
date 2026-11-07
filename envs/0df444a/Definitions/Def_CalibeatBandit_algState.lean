-- Prove2me | Definitions.Def_CalibeatBandit_algState
-- name    : CalibeatBandit_algState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:50.941065+00:00
-- url     : https://prove2.me/theorems/a20d543a-921b-4bef-afb9-ab3edb94e08d
-- title:
--   The bandit calibeating algorithm: state recursion and $x_t,p_t,v_t,H^{\mathrm{SR}}_t,H^{\mathrm{Rec}}_t$
-- statement:
--   The **bandit calibeating algorithm** with learning rate $\eta$ and exploration parameter $\mu$ keeps $2K+1$ exponential-weights learners (3.3), all with learning rate $\eta$ and uniform initial weights: $L^{\mathrm{SR}}_i$ and $L^{\mathrm{Rec}}_i$ over $\mathcal A$ for each $i\in\mathcal A$, and $L^{\mathrm{mix}}$ over the two actions $\{\mathrm{SR},\mathrm{Rec}\}$. In round $t$, given the recommended action $J_t$:
--
--   1. $m^a_{t,i}$ is the output of $L^a_i$ and $M^a_t=[m^a_{t,1}\mid\cdots\mid m^a_{t,K}]$; $(\lambda_t,1-\lambda_t)$ is the output of $L^{\mathrm{mix}}$;
--   2. $x_t$ solves (3.1): $(I-\lambda_tM^{\mathrm{SR}}_t)x_t=(1-\lambda_t)M^{\mathrm{Rec}}_te_{J_t}$;
--   3. the learner plays $p_t=(1-\mu)x_t+\mu u$, $u=\frac1K\mathbf 1$, and draws $I_t\sim p_t$;
--   4. observing only $y_t(I_t)$, it forms $\hat y_t(j)=y_t(I_t)\mathbb 1\{I_t=j\}/p_t(j)$ and $v_t(j)=\hat y_t(j)+(e-2)\eta/p_t(j)$;
--   5. $L^{\mathrm{SR}}_i$ receives the reward vector $x_t(i)v_t$, $L^{\mathrm{Rec}}_i$ receives $\mathbb 1\{J_t=i\}v_t$, and $L^{\mathrm{mix}}$ receives $(H^{\mathrm{SR}}_t,H^{\mathrm{Rec}}_t)$, computed from the distributions returned at the beginning of round $t$.
--
--   Unrolled, $m^{\mathrm{SR}}_{t,i}(j)\propto\exp(\eta\sum_{s<t}x_s(i)v_s(j))$, $m^{\mathrm{Rec}}_{t,i}(j)\propto\exp(\eta\sum_{s<t}\mathbb 1\{J_s=i\}v_s(j))$, and $\lambda_t\propto\exp(\eta\sum_{s<t}H^{\mathrm{SR}}_s)$. The definition gives the state before round $t$ and the round-$t$ quantities $x_t$, $p_t$, $v_t$, $H^{\mathrm{SR}}_t$, $H^{\mathrm{Rec}}_t$ as functions of the learner's observations: the recommended actions $J_s$ ($s\le t$), its own actions $I_s$ and observed rewards $r_s=y_s(I_s)$ ($s<t$, and $s=t$ for $v_t$ and the $H$'s).
--
--   **Formalization Note** Exponential weights (3.3) on a cumulative reward vector $G$ is the published `FewExperts.hedgeWeights`. Rounds are $0,1,\dots$; `algState … 0` is the initial (uniform) state; $x_t$ is the explicit solution `fixedPointSol`; $e$ is `Real.exp 1`.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Algorithm 1, p.10 (PDF 10), with §3.2 items 1–4, pp.10–11 (PDF 10–11) and Theorem 3.2's instantiation, p.11

import Mathlib
import Definitions.Def_FewExperts_hedgeWeights
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf

set_option autoImplicit false

namespace CalibeatBandit

open Matrix

/-- The internal state of the bandit calibeating algorithm before a round: the cumulative reward
vectors fed so far to the `2K + 1` exponential-weights learners.
* `cumSR i j = ∑_{s<t} x_s(i) v_s(j)` (learner `L^SR_i`, reward `x_s(i) v_s`);
* `cumRec i j = ∑_{s<t} 1{J_s = i} v_s(j)` (learner `L^Rec_i`, reward `1{J_s = i} v_s`);
* `cumHSR = ∑_{s<t} H^SR_s`, `cumHRec = ∑_{s<t} H^Rec_s` (learner `L^mix`). -/
structure LearnerState (K : ℕ) where
  cumSR : Fin K → Fin K → ℝ
  cumRec : Fin K → Fin K → ℝ
  cumHSR : ℝ
  cumHRec : ℝ

namespace LearnerState

variable {K : ℕ}

/-- No rewards yet: every learner starts from uniform weights (zero cumulative rewards). -/
def init (K : ℕ) : LearnerState K := ⟨0, 0, 0, 0⟩

/-- `M^SR_t`, with column `i` the exponential weights `m^SR_{t,i}` of learner `L^SR_i`. -/
noncomputable def matSR (η : ℝ) (s : LearnerState K) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun j i => FewExperts.hedgeWeights η (s.cumSR i) j

/-- `M^Rec_t`, with column `i` the exponential weights `m^Rec_{t,i}` of learner `L^Rec_i`. -/
noncomputable def matRec (η : ℝ) (s : LearnerState K) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun j i => FewExperts.hedgeWeights η (s.cumRec i) j

/-- `λ_t`, the weight that the two-action learner `L^mix` puts on `SR`. -/
noncomputable def lam (η : ℝ) (s : LearnerState K) : ℝ :=
  FewExperts.hedgeWeights η ![s.cumHSR, s.cumHRec] 0

/-- `x_t`, the solution of (3.1) for the current state and recommended action `J`. -/
noncomputable def roundX (η : ℝ) (s : LearnerState K) (J : Fin K) : Fin K → ℝ :=
  fixedPointSol (s.lam η) (s.matSR η) (s.matRec η) J

end LearnerState

/-- Exploration: `p = (1 − μ) x + μ u` with `u = (1/K)·𝟏` the uniform distribution. -/
noncomputable def explore {K : ℕ} (μ : ℝ) (x : Fin K → ℝ) : Fin K → ℝ :=
  fun j => (1 - μ) * x j + μ / K

/-- Reward estimation: `ŷ(j) = y(I) 1{I = j} / p(j)` and `v(j) = ŷ(j) + (e − 2) η / p(j)`, where
`r = y(I)` is the observed reward. -/
noncomputable def estimate {K : ℕ} (η : ℝ) (p : Fin K → ℝ) (I : Fin K) (r : ℝ) : Fin K → ℝ :=
  fun j => (if I = j then r / p j else 0) + (Real.exp 1 - 2) * η / p j

namespace LearnerState

variable {K : ℕ}

/-- One round of the bandit algorithm from state `s`, recommended action `J`, played action `I`
and observed reward `r`: feed `x(i) v` to `L^SR_i`, `1{J = i} v` to `L^Rec_i`, and
`(H^SR, H^Rec)` to `L^mix`. -/
noncomputable def step (η μ : ℝ) (s : LearnerState K) (J I : Fin K) (r : ℝ) : LearnerState K :=
  let x := s.roundX η J
  let v := estimate η (explore μ x) I r
  { cumSR := fun i j => s.cumSR i j + x i * v j
    cumRec := fun i j => s.cumRec i j + (if J = i then v j else 0)
    cumHSR := s.cumHSR + HSRof η (s.matSR η) x v
    cumHRec := s.cumHRec + HRecOf η (s.matRec η) J v }

end LearnerState

/-- **The bandit calibeating algorithm: its state before round `t`**, as a function of the
learner's observations: recommended actions `J`, played actions `I`, observed rewards `r`
(`r s = y_s(I_s)`). Only the entries `s < t` are read.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Algorithm 1
(p.10) with the bandit modifications of §3.2 (pp.10–11), every internal learner instantiated by
exponential weights (3.3) with the same learning rate `η`, starting from uniform weights
(Theorem 3.2, p.11). Round `t`:
1. `m^SR_{t,i}`, `m^Rec_{t,i}` and `(λ_t, 1 − λ_t)` are the exponential weights of the
   cumulative rewards of `L^SR_i`, `L^Rec_i`, `L^mix`; `M^a_t = [m^a_{t,1} | ⋯ | m^a_{t,K}]`;
2. `x_t` solves (3.1) `(I − λ_t M^SR_t) x_t = (1 − λ_t) M^Rec_t e_{J_t}`;
3. `p_t = (1 − μ) x_t + μ u` and `I_t ∼ p_t`;
4. `ŷ_t(j) = y_t(I_t) 1{I_t = j}/p_t(j)`, `v_t(j) = ŷ_t(j) + (e − 2)η/p_t(j)`;
5. `L^SR_i` gets `x_t(i) v_t`, `L^Rec_i` gets `1{J_t = i} v_t`, `L^mix` gets `(H^SR_t, H^Rec_t)`.

**Formalization Note.** Rounds are `0, 1, …`; `algState … 0` is the initial state.
Exponential weights (3.3), `w(j) = exp(η G(j)) / ∑_k exp(η G(k))` on the cumulative reward vector
`G = ∑_{s<t} z_s`, is the published `FewExperts.hedgeWeights` (zero cumulative reward gives uniform
weights).
`x_t` is the explicit solution `fixedPointSol` of (3.1). `e` is `Real.exp 1`. -/
noncomputable def algState {K : ℕ} (η μ : ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ) :
    ℕ → LearnerState K
  | 0 => LearnerState.init K
  | t + 1 => (algState η μ J I r t).step η μ (J t) (I t) (r t)

/-- `x_t`: the solution of (3.1) in round `t`. -/
noncomputable def algX {K : ℕ} (η μ : ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ) (t : ℕ) : Fin K → ℝ :=
  (algState η μ J I r t).roundX η (J t)

/-- `p_t = (1 − μ) x_t + μ u`: the mixed strategy played in round `t`. -/
noncomputable def algP {K : ℕ} (η μ : ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ) (t : ℕ) : Fin K → ℝ :=
  explore μ (algX η μ J I r t)

/-- `v_t`: the optimistically corrected reward estimate of round `t`. -/
noncomputable def algV {K : ℕ} (η μ : ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ) (t : ℕ) : Fin K → ℝ :=
  estimate η (algP η μ J I r t) (I t) (r t)

/-- `H^SR_t`: the `SR` feedback of `L^mix` in round `t`. -/
noncomputable def algHSR {K : ℕ} (η μ : ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ) (t : ℕ) : ℝ :=
  HSRof η ((algState η μ J I r t).matSR η) (algX η μ J I r t) (algV η μ J I r t)

/-- `H^Rec_t`: the `Rec` feedback of `L^mix` in round `t`. -/
noncomputable def algHRec {K : ℕ} (η μ : ℝ) (J I : ℕ → Fin K) (r : ℕ → ℝ) (t : ℕ) : ℝ :=
  HRecOf η ((algState η μ J I r t).matRec η) (J t) (algV η μ J I r t)

end CalibeatBandit


