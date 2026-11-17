-- Prove2me | Definitions.Def_CalibeatBandit_Supplement_robustPolicy
-- name    : CalibeatBandit_Supplement_robustPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:28:46.138207+00:00
-- url     : https://prove2.me/theorems/73c1d560-927a-4593-bd01-ec4f5a83bdf1
-- title:
--   Algorithm 2 (Robust Calibeating)
-- statement:
--   **Algorithm 2.** Input $\tfrac12<\zeta<1$. Let $\varepsilon=T^{-\zeta}$ and $u=K^{-1}\mathbf 1$ (the uniform distribution). For $1\le s\le T$ let
--   $$L_s=K\log K+\log\big(4s(s+1)T^2\big),\qquad C_s=\sqrt{\frac{2(KT^\zeta+2)L_s}{s}}+\frac{(KT^\zeta+1)L_s}{3s}.$$
--   The mode starts at *follow* and $\widehat G_{0,i,j}=0$. In round $t=1,\dots,T$ the learner observes $q_t$, and then:
--
--   1. **Follow mode.** Let $p_t=(1-\varepsilon)q_t+\varepsilon u$. Draw $J_t\sim q_t$ and $E_t\sim\mathrm{Ber}(\varepsilon)$ independently. Set $I_t=J_t$ if $E_t=0$; otherwise draw $I_t\sim u$. Observe $y_t(I_t)$ and compute $\widehat y_t(j)=y_t(I_t)\mathbf 1\{I_t=j\}/p_t(j)$. Update $\widehat G_{t,i,j}=\widehat G_{t-1,i,j}+q_t(i)\big(\widehat y_t(j)-\widehat y_t(i)\big)$ and $\widehat H_t=\sum_i\max_j\widehat G_{t,i,j}$. If $\widehat H_t>3tC_t$, switch to *calibeating* mode and initialize a fresh copy of the bandit calibeating algorithm with the parameters of Theorem 3.2 and horizon bound $T$.
--   2. **Calibeating mode.** Run one round of that copy with recommendation $q_t$.
--
--   As a learner, the algorithm is described by the conditional law of $I_t$ given the history and $J_t$. Before the first switch this law is $(1-\varepsilon)e_{J_t}+\varepsilon u$. After a switch at the end of round $\tau$ it is the mixed strategy of the calibeating copy in its own round $t-\tau$, computed from the post-switch history.
--
--   The algorithm follows the recommendation while an estimate of the recommendation's swap regret stays below the thresholds, and falls back on the worst-case algorithm of Theorem 3.2 otherwise. Theorem 3.5 is its guarantee.
--
--   **Formalization Note** Rounds are $0,\dots,T-1$, and the test at the end of 0-indexed round $u$ is the paper's test in round $u+1$. The switching round is played in follow mode. The copy is the base mission's `calibeatPolicy K η* μ*` with the tuned parameters $\eta^*=\min\{1/(8K),\sqrt{(2K\log K+\log2)/(14KT)}\}$ and $\mu^*=4K\eta^*$ (published `etaStar`, `muStar`; proof of Theorem 3.2, p.36). It starts from uniform weights with its round counter at $0$. $\widehat G$ and $\widehat H$ are computed on the follow rounds, i.e. every round up to the first switch. `log` is the natural logarithm.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Algorithm 2, p.12 (PDF 12); parameters of Theorem 3.2 from its proof, §C.2, p.36 (PDF 36)

import Mathlib
import Definitions.Def_CalibeatBandit_Supplement_QProtocolRun
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_etaStar

set_option autoImplicit false

namespace CalibeatBandit

namespace Supplement

/-- The exploration rate `ε = T^{−ζ}` of Algorithm 2 (p.12). -/
noncomputable def robustEps (T : ℕ) (ζ : ℝ) : ℝ :=
  (T : ℝ) ^ (-ζ)

/-- `L_s = K log K + log(4s(s + 1)T²)` of Algorithm 2 (p.12), for `1 ≤ s ≤ T`. -/
noncomputable def robustL (K T s : ℕ) : ℝ :=
  K * Real.log K + Real.log (4 * s * (s + 1) * (T : ℝ) ^ 2)

/-- The average swap-regret thresholds of Algorithm 2 (p.12), for `1 ≤ s ≤ T`:
`C_s = √(2(KT^ζ + 2)L_s / s) + (KT^ζ + 1)L_s / (3s)`. -/
noncomputable def robustC (K T : ℕ) (ζ : ℝ) (s : ℕ) : ℝ :=
  Real.sqrt (2 * (K * (T : ℝ) ^ ζ + 2) * robustL K T s / s) +
    (K * (T : ℝ) ^ ζ + 1) * robustL K T s / (3 * s)

/-- The follow-mode mixed strategy `p_t = (1 − ε) q_t + ε u`, `u = K⁻¹𝟏` (Algorithm 2, p.12). -/
noncomputable def followMix {K : ℕ} (ε : ℝ) (q : Fin K → ℝ) : Fin K → ℝ :=
  fun j => (1 - ε) * q j + ε / K

/-- The importance-weighted estimate `ŷ_t(j) = y_t(I_t) 1{I_t = j} / p_t(j)` (Algorithm 2, p.12),
from the played action `I`, the observed reward `r = y_t(I_t)` and the mixed strategy `p`. -/
noncomputable def robustYhat {K : ℕ} (p : Fin K → ℝ) (I : Fin K) (r : ℝ) : Fin K → ℝ :=
  fun j => if I = j then r / p j else 0

/-- `Ĝ_{n,i,j} = ∑_{t=1}^n q_t(i)(ŷ_t(j) − ŷ_t(i))` after `n` follow-mode rounds (Algorithm 2,
p.12), read from the recommended strategies `q`, the played actions `I` and the observed rewards
`r` (0-indexed rounds `0, …, n − 1`). -/
noncomputable def robustGhat {K : ℕ} (T : ℕ) (ζ : ℝ) (q : ℕ → Fin K → ℝ) (I : ℕ → Fin K)
    (r : ℕ → ℝ) (n : ℕ) (i j : Fin K) : ℝ :=
  ∑ u ∈ Finset.range n,
    q u i * (robustYhat (followMix (robustEps T ζ) (q u)) (I u) (r u) j -
      robustYhat (followMix (robustEps T ζ) (q u)) (I u) (r u) i)

/-- `Ĥ_n = ∑_i max_j Ĝ_{n,i,j}` (Algorithm 2, p.12). -/
noncomputable def robustHhat {K : ℕ} (T : ℕ) (ζ : ℝ) (q : ℕ → Fin K → ℝ) (I : ℕ → Fin K)
    (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i, ⨆ j, robustGhat T ζ q I r n i j

/-- The switching test of Algorithm 2 at the end of the paper's round `n` (1-indexed):
`Ĥ_n > 3nC_n`. -/
def robustCrossed {K : ℕ} (T : ℕ) (ζ : ℝ) (q : ℕ → Fin K → ℝ) (I : ℕ → Fin K) (r : ℕ → ℝ)
    (n : ℕ) : Prop :=
  3 * n * robustC K T ζ n < robustHhat T ζ q I r n

/-- Extend a prefix `f : Fin n → α` to a sequence `ℕ → α` by the default value `d`. -/
def extendFin {α : Type*} (d : α) {n : ℕ} (f : Fin n → α) : ℕ → α :=
  fun s => if h : s < n then f ⟨s, h⟩ else d

/-- **Algorithm 2 (Robust Calibeating)** with parameter `ζ` and horizon `T`, as a learner that
reads the recommendation.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Algorithm 2,
p.12. Input `1/2 < ζ < 1`; `ε = T^{−ζ}`, `u = K⁻¹𝟏`; thresholds `C_s` (`robustC`); the mode
starts at *follow* and `Ĝ_0 = 0`. In round `t = 1, …, T`, after observing `q_t`:
* in follow mode, `p_t = (1 − ε)q_t + εu`; `J_t ∼ q_t` and `E_t ∼ Ber(ε)` independently;
  `I_t = J_t` if `E_t = 0`, else `I_t ∼ u`; observe `y_t(I_t)`, set
  `ŷ_t(j) = y_t(I_t)1{I_t = j}/p_t(j)`, `Ĝ_{t,i,j} = Ĝ_{t−1,i,j} + q_t(i)(ŷ_t(j) − ŷ_t(i))`,
  `Ĥ_t = ∑_i max_j Ĝ_{t,i,j}`; if `Ĥ_t > 3tC_t`, switch to calibeating mode and initialize a
  fresh copy of the bandit calibeating algorithm with the parameters following Theorem 3.2 and
  horizon bound `T`;
* otherwise (calibeating mode), run one round of that copy with recommendation `q_t`.

The value at round `t` (0-indexed) is the conditional law of `I_t` given everything before the
draw of `I_t` (the history and `J_t`):
* if no test has fired at the end of rounds `0, …, t − 1`, it is `(1 − ε)e_{J_t} + εu`
  (`I_t = J_t` with probability `1 − ε`, uniform with probability `ε`);
* if the first test fired at the end of round `τ < t`, it is the mixed strategy of the
  calibeating copy `calibeatPolicy K η* μ*` in its own round `t − (τ + 1)`, run on the
  post-switch history `J_{τ+1}, …, I_{τ+1}, …, y_{τ+1}(I_{τ+1}), …`.

**Formalization Note.** Rounds are `0, …, T − 1`; the test at the end of 0-indexed round `u` is
the paper's test in its round `u + 1` (`robustCrossed … (u + 1)`), and `Ĝ`, `Ĥ` are computed on
follow-mode rounds only (every round up to the first firing is a follow round). The switching
round itself is played in follow mode; the copy starts in the next round with its own round
counter at `0` and from uniform weights. "The parameters following Theorem 3.2 and horizon bound
`T`" are the tuned `η* = etaStar K T`, `μ* = muStar K T` of the proof of Theorem 3.2 (p.36),
published by the base mission. The marginal `p_t = (1 − ε)q_t + εu` enters `ŷ_t`; the
conditional law given `J_t` is `(1 − ε)e_{J_t} + εu`; their agreement is the paper's sampling
rule. Prefixes are extended to sequences with `J_0` (an action) and `0` as default values;
only entries inside the prefix are read. `max_j` is `⨆ j` over the finite nonempty `Fin K`. -/
noncomputable def robustPolicy (K T : ℕ) (ζ : ℝ) : QPolicy K := fun t q J I r => by
  classical
  let d : Fin K := J 0
  let q' : ℕ → Fin K → ℝ := extendFin 0 q
  let J' : ℕ → Fin K := extendFin d J
  let I' : ℕ → Fin K := extendFin d I
  let r' : ℕ → ℝ := extendFin 0 r
  exact
    if h : ∃ u, u < t ∧ robustCrossed T ζ q' I' r' (u + 1) then
      calibeatPolicy K (etaStar K T) (muStar K T) (t - (Nat.find h + 1))
        (fun k => J' (Nat.find h + 1 + k)) (fun k => I' (Nat.find h + 1 + k))
        (fun k => r' (Nat.find h + 1 + k))
    else
      fun j => (1 - robustEps T ζ) * (if J (Fin.last t) = j then 1 else 0) + robustEps T ζ / K

end Supplement

end CalibeatBandit


