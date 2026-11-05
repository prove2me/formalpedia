-- Prove2me | Definitions.Def_CalendarDependentRM_DemandChain
-- name    : CalendarDependentRM_DemandChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:28.170952+00:00
-- url     : https://prove2.me/theorems/69ff10fb-7549-49d7-b360-48c504b2b0d4
-- title:
--   The Markov demand process over the stages: transition law, path probability, events, survival rate, transition assumption
-- statement:
--   The number of customer arrivals $D^k\in\{1,\dots,T\}$ in the stages $k=1,\dots,K$ follows a non-stationary Markov chain: conditional on $D^{k-1}$, the demand $D^k$ is independent of the earlier demands. The chain starts from a fixed value $D^0=\hat D^0$ given as problem data, and the transition laws $P\{D^k=p\mid D^{k-1}=q\}$ are arbitrary.
--
--   From these laws we obtain the probability of a whole demand path, the probability $P\{E\}$ of an event of the path and the conditional probability $P\{E\mid F\}$. The central event is $\{D^k\ge t,\ D^{k-1}=q\}$: period $t$ of stage $k$ is reached and the previous stage had demand $q$. The **survival rate** is
--
--   $$
--   \theta^k_t(q)=P\{D^k\ge t+1\mid D^k\ge t,\ D^{k-1}=q\}.
--   $$
--
--   The **transition assumption** with parameter $\epsilon$ says that every transition between stages of the horizon has probability at least $\epsilon$.
--
--   This definition carries all the randomness of the demand, and every statement of the mission is built on it.
--
--   **Formalization Note** Stages and demands are 0-based. The paper's primitive is $\theta$; the transition law is equivalent data, and $\theta$ is computed from it as a ratio of kernel tails, so that it is defined whether or not $D^{k-1}=q$ has positive probability. $P\{E\mid F\}$ is a ratio that reads $0$ when $P\{F\}=0$.
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, §2, pp.7–8

import Mathlib

open scoped Classical

namespace CalendarDependentRM

/-- **The Markov demand process over the stages.** Li, Rusmevichientong & Topaloglu,
*Revenue Management with Calendar-Aware and Dependent Demands*, arXiv:2409.02637v2, §2, pp. 7–8:
"The demands in successive stages follow a Markov process"; "the demand in the stage right before
the beginning of the selling horizon is `D⁰` and it is fixed at `D̂⁰` as problem data".

* `K`: the number of stages, `T`: the largest possible demand in a stage;
* `trans k q p`: the probability `P{D^k = p | D^{k-1} = q}`;
* `D0`: the fixed value `D̂⁰`.

**Formalization Note** Stages and demands are 0-based: `k : Fin K` is the paper's stage `k + 1`, and
the value `p : Fin T` is the paper's demand `p + 1`. The paper's primitive is the survival rate
`θ^k_t(q)`; the transition law `trans` is equivalent data, and `θ` is derived from it
(`DemandChain.theta`). The laws of `D^k` given `D^{k-1}` are arbitrary, as in the paper. `D0` forces
`T ≥ 1`. -/
structure DemandChain (K T : ℕ) where
  /-- The transition probability `P{D^k = p | D^{k-1} = q}`. -/
  trans : Fin K → Fin T → Fin T → ℝ
  trans_nonneg : ∀ k q p, 0 ≤ trans k q p
  trans_sum : ∀ k q, ∑ p, trans k q p = 1
  /-- The fixed demand `D̂⁰` before the selling horizon. -/
  D0 : Fin T

namespace DemandChain

variable {K T : ℕ} (C : DemandChain K T)

/-- The demand `D^{k-1}` in the stage before `k` on the demand path `d`, with `D⁰ = D̂⁰` before the
first stage. Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, p. 8. -/
def prev (d : Fin K → Fin T) (k : Fin K) : Fin T :=
  if h : (k : ℕ) = 0 then C.D0 else d ⟨(k : ℕ) - 1, by omega⟩

/-- The probability of the demand path `d = (D¹, …, D^K)` under the Markov process of
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §2, p. 7: the product of its transitions. -/
noncomputable def pathProb (d : Fin K → Fin T) : ℝ :=
  ∏ k, C.trans k (C.prev d k) (d k)

/-- `P{E}` for an event `E` of the demand path, Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, §2, p. 7. -/
noncomputable def prob (E : (Fin K → Fin T) → Prop) : ℝ :=
  ∑ d, if E d then C.pathProb d else 0

/-- `P{E | F}` for events of the demand path.

**Formalization Note** The ratio `P{E, F} / P{F}`, so it reads `0` when `P{F} = 0`, where the paper's
expression is undefined. Such an `F` occurs at stage one for `q ≠ D̂⁰`, for instance. In the fluid
program it multiplies a variable with no effect on the objective or the policy. -/
noncomputable def condProb (E F : (Fin K → Fin T) → Prop) : ℝ :=
  C.prob (fun d => E d ∧ F d) / C.prob F

/-- The event `{D^k ≥ t, D^{k-1} = q}`, Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, p. 8.

**Formalization Note** With 0-based indices, the paper's `D^k ≥ t` at the paper's period `t + 1` reads
`t ≤ d k`. -/
def reach (k : Fin K) (t q : Fin T) (d : Fin K → Fin T) : Prop :=
  t ≤ d k ∧ C.prev d k = q

/-- The tail `P{D^k ≥ t + 1 | D^{k-1} = q}` in 1-based demand, the kernel sum behind the survival
rate of Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §2, p. 7.

**Formalization Note** Indexed by `ℕ`, so that `tail k q T = 0`. -/
noncomputable def tail (k : Fin K) (q : Fin T) (t : ℕ) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin T => t ≤ (p : ℕ)), C.trans k q p

/-- **The survival rate** `θ^k_t(q) = P{D^k ≥ t + 1 | D^k ≥ t, D^{k-1} = q}`,
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §2, p. 7.

**Formalization Note** At 0-based `t`, it is `tail k q (t + 1) / tail k q t`. It is a kernel quantity,
so it is defined whether or not `D^{k-1} = q` has positive probability, as the paper's primitive is.
Where `tail k q t = 0`, Lean's `0 / 0 = 0` gives `θ = 0`; such a period is never reached. At the last
period `theta k (T - 1) q = 0`, the paper's `θ^k_T(q) = 0`. -/
noncomputable def theta (k : Fin K) (t : ℕ) (q : Fin T) : ℝ :=
  C.tail k q (t + 1) / C.tail k q t

/-- **The transition assumption** `P{D^{k+1} = p | D^k = q} ≥ ε` for all `p`, `q`,
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §2, p. 7.

**Formalization Note** The literal reading: it bounds the transitions between stages of the horizon,
into the paper's stages `2, …, K`, and says nothing on the law of `D¹` given `D̂⁰`. At `K = 1` it is
empty. -/
def Minorized (ε : ℝ) : Prop :=
  ∀ k : Fin K, (k : ℕ) ≠ 0 → ∀ q p, ε ≤ C.trans k q p

end DemandChain

end CalendarDependentRM


