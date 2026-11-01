-- Prove2me | Definitions.Def_MaxObjBandit_adaEtc
-- name    : MaxObjBandit_adaEtc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:39.41137+00:00
-- url     : https://prove2.me/theorems/c947b5ec-f32b-436a-8490-b0d25c6e2aec
-- title:
--   ADA-ETC (Algorithm 1) with a fixed tie-breaking priority, and the bound of Theorem 4
-- statement:
--   **ADA-ETC** (Adaptive Explore-then-Commit) with $K$ arms and horizon $T$ runs as follows, with $n^i_{t-1}$ the number of pulls of arm $i$ before time $t$ and the indices $\mathrm{UCB}$, $\mathrm{LCB}$ of (2), (3).
--
--   1. **Explore phase.** At times $t=1,\dots,K$, pull each arm once (arm $t$ at time $t$).
--   2. At each time $K<t\le T$: let $L_t\in\arg\max_i\mathrm{LCB}^i_{n^i_{t-1}}$. If
--   $$
--   \mathrm{LCB}^{L_t}_{n^{L_t}_{t-1}}>\max_{i\ne L_t}\mathrm{UCB}^i_{n^i_{t-1}}, \tag{4}
--   $$
--   commit to $i^*=L_t$: pull $i^*$ at time $t$ and at every later time (**Commit phase**). Otherwise pull an arm $E_t\in\arg\max_i\mathrm{UCB}^i_{n^i_{t-1}}$.
--
--   Both argmaxes break ties by a **fixed priority order** $\sigma$ on the arms: among the maximizers, the arm of smallest rank $\sigma(i)$ is chosen. The policy is a deterministic function of the history, so it belongs to $\Pi_T$.
--
--   The same module defines the instance-dependent bound of Theorem 4: with paper indices $1,\dots,K$, $\Delta_i=\mu_1-\mu_i$ and $\Delta_1=0$,
--   $$
--   \mu_1\sum_{i=2}^{K}\min\Big(\tfrac{11}{\Delta_i^2}+\tfrac{16}{\Delta_i^2}\log^+\tfrac{T\Delta_i^3}{K}+\tfrac{24}{\Delta_i^2}\sqrt{\log^+\tfrac{T\Delta_i^3}{K}},\tau\Big)+\mu_1\tau\sum_{i=2}^{K}\min\Big(2,\tfrac{648K}{T\Delta_i^3}\Big)+\sum_{i=2}^{K}e^{-\tau\Delta_i^2/2}T\Delta_i+\sum_{i=2}^{K}\min\Big(1,\tfrac{320K}{T\Delta_i^3}\Big)T(\Delta_i-\Delta_{i-1}).
--   $$
--
--   **Formalization Note** The paper breaks ties "arbitrarily"; with history-dependent tie-breaking Theorem 4 fails (see the goal theorem), so a fixed priority order $\sigma$ is a parameter of the algorithm. When $K=1$ the maximum in (4) is over the empty set, read as $-\infty$, so the single arm is committed to at time $2$ (it is the only arm in any case). The commitment in force at time $t$ is recomputed from the history: it is the leader at the first time at which (4) held. Means in the bound are read with the paper's 1-based indices (`paperMean`).
-- source:
--   Ozbay, Kamble, Maximal Objectives in the Multi-armed Bandit with Applications, arXiv:2006.06853v6, Algorithm 1, Eq. (4), p.20; Theorem 4, p.22

import Mathlib
import Definitions.Def_MaxObjBandit_regret
import Definitions.Def_MaxObjBandit_ucbIndex

open Classical

namespace MaxObjBandit

/-- The number of pulls of arm `i` in the history `h` strictly before position `s`. -/
def countBefore {K t : ℕ} (h : History K t) (s : Fin t) (i : Fin K) : ℕ :=
  (Finset.univ.filter fun r : Fin t => r < s ∧ (h r).1 = i).card

/-- The reward sequence of arm `i` read off the history `h`: `armRewards h i n` is the reward of the
`(n+1)`-th pull of arm `i` in `h` (the paper's `Uⁱ_{n+1}`), and `0` if arm `i` was pulled at most `n`
times in `h`. -/
noncomputable def armRewards {K t : ℕ} (h : History K t) (i : Fin K) (n : ℕ) : ℝ :=
  ∑ s : Fin t, if (h s).1 = i ∧ countBefore h s i = n then (h s).2 else 0

/-- `UCBⁱ_{nⁱ_{t−1}}` computed from the history `h` (arXiv:2006.06853v6, Eq. (2), p.20). -/
noncomputable def ucbOf (K T : ℕ) {t : ℕ} (h : History K t) (i : Fin K) : ℝ :=
  ucbIndex K T (armRewards h i) (armCount h i)

/-- `LCBⁱ_{nⁱ_{t−1}}` computed from the history `h` (arXiv:2006.06853v6, Eq. (3), p.20). -/
noncomputable def lcbOf (K T : ℕ) {t : ℕ} (h : History K t) (i : Fin K) : ℝ :=
  lcbIndex K T (armRewards h i) (armCount h i)

/-- An element of `argmax_{i ∈ [K]} f(i)`, ties broken by the fixed priority order `σ`: among the
maximizers of `f`, the arm with the smallest rank `σ i`.

**Formalization Note** The arms are scanned in increasing rank `σ.symm 0, σ.symm 1, …`, starting
from the arm of rank `0`, and the current choice is replaced only on a strict improvement. -/
noncomputable def prioArgmax {K : ℕ} (hK : 0 < K) (σ : Equiv.Perm (Fin K)) (f : Fin K → ℝ) :
    Fin K :=
  (List.finRange K).foldl (fun best r => if f best < f (σ.symm r) then σ.symm r else best)
    (σ.symm ⟨0, hK⟩)

/-- The leader `L_t ∈ argmax_{i∈[K]} LCBⁱ_{nⁱ_{t−1}}` of Step 1 of ADA-ETC (arXiv:2006.06853v6,
Algorithm 1, p.20), ties broken by `σ`. -/
noncomputable def leader (K T : ℕ) (hK : 0 < K) (σ : Equiv.Perm (Fin K)) {t : ℕ}
    (h : History K t) : Fin K :=
  prioArgmax hK σ (lcbOf K T h)

/-- The commit test (4): `LCB^{L_t}_{n^{L_t}_{t−1}} > max_{i∈[K]: i≠L_t} UCBⁱ_{nⁱ_{t−1}}`
(arXiv:2006.06853v6, Eq. (4), p.20).

**Formalization Note** Written as "every other arm's UCB is strictly below the leader's LCB". When
`K = 1` there is no other arm and the test holds (a maximum over the empty set is `−∞`). -/
def commitTest (K T : ℕ) (hK : 0 < K) (σ : Equiv.Perm (Fin K)) {t : ℕ} (h : History K t) : Prop :=
  ∀ i, i ≠ leader K T hK σ h → ucbOf K T h i < lcbOf K T h (leader K T hK σ h)

/-- The commitment in force when ADA-ETC chooses the arm at time `t + 1`, given the history `h` of
the first `t` times: `some i*` if the commit test (4) fired at an earlier time `K < s + 1 ≤ t`
(evaluated on the prefix of `h` of length `s`) or fires now (`K ≤ t`), with `i*` the leader at the
first such time; `none` otherwise (arXiv:2006.06853v6, Algorithm 1, Procedure, p.20). -/
noncomputable def commitArm (K T : ℕ) (hK : 0 < K) (σ : Equiv.Perm (Fin K)) :
    (t : ℕ) → History K t → Option (Fin K)
  | 0, h => if K ≤ 0 ∧ commitTest K T hK σ h then some (leader K T hK σ h) else none
  | t + 1, h =>
      match commitArm K T hK σ t (fun s => h s.castSucc) with
      | some i => some i
      | none =>
          if K ≤ t + 1 ∧ commitTest K T hK σ h then some (leader K T hK σ h) else none

/-- **ADA-ETC** (Adaptive Explore-then-Commit), `ADA-ETC_{K,T}` with ties broken by the fixed
priority order `σ` (arXiv:2006.06853v6, Algorithm 1, p.20).

* Explore phase, times `1, …, K` (`0`-based `t < K`): pull each arm once, arm `t + 1` at time
  `t + 1`.
* Times `K < t + 1 ≤ T`: if the commit test (4) has fired (now or earlier), pull the committed arm
  `i* = L` (the time at which (4) first fires already pulls `i*`); otherwise pull
  `E_t ∈ argmax_{i∈[K]} UCBⁱ_{nⁱ_{t−1}}`.

**Formalization Note** The page breaks ties in both argmaxes "arbitrarily"; here both use the fixed
priority order `σ` (a correction: with history-dependent tie-breaking Theorem 4 is false). The order
of the first `K` pulls does not affect the state after them. -/
noncomputable def adaEtc (K T : ℕ) (hK : 0 < K) (σ : Equiv.Perm (Fin K)) : Policy K :=
  fun t h =>
    if ht : t < K then ⟨t, ht⟩
    else
      match commitArm K T hK σ t h with
      | some i => i
      | none => prioArgmax hK σ (ucbOf K T h)

/-- The means in the paper's `1`-based labelling: `paperMean ν i = µᵢ = mean of arm i − 1` for
`1 ≤ i ≤ K`, and `0` otherwise. -/
noncomputable def paperMean {K : ℕ} (ν : BanditInstance K) (i : ℕ) : ℝ :=
  if h : 0 < i ∧ i ≤ K then ν.mean ⟨i - 1, by omega⟩ else 0

/-- The instance-dependent bound of Theorem 4 (arXiv:2006.06853v6, Theorem 4, p.22), with
`∆ᵢ = µ₁ − µᵢ`, paper indices `1, …, K` and `τ = ⌈T^{2/3}/K^{2/3}⌉`:
`µ₁ ∑_{i=2}^K min(11/∆ᵢ² + (16/∆ᵢ²) log⁺(T∆ᵢ³/K) + (24/∆ᵢ²) √(log⁺(T∆ᵢ³/K)), τ)
 + µ₁ τ ∑_{i=2}^K min(2, 648K/(T∆ᵢ³)) + ∑_{i=2}^K exp(−τ∆ᵢ²/2) T∆ᵢ
 + ∑_{i=2}^K min(1, 320K/(T∆ᵢ³)) T(∆ᵢ − ∆_{i−1})`.

**Formalization Note** `µ : ℕ → ℝ` is read with the paper's `1`-based indices; `∆₁ = 0` in the last
sum. -/
noncomputable def theorem4Bound (K T : ℕ) (μ : ℕ → ℝ) : ℝ :=
  let τ : ℝ := (tau K T : ℝ)
  let Δ : ℕ → ℝ := fun i => μ 1 - μ i
  μ 1 * ∑ i ∈ Finset.Icc 2 K,
      min (11 / Δ i ^ 2 + 16 / Δ i ^ 2 * logPlus ((T : ℝ) * Δ i ^ 3 / K)
        + 24 / Δ i ^ 2 * Real.sqrt (logPlus ((T : ℝ) * Δ i ^ 3 / K))) τ
    + μ 1 * τ * ∑ i ∈ Finset.Icc 2 K, min 2 (648 * (K : ℝ) / ((T : ℝ) * Δ i ^ 3))
    + ∑ i ∈ Finset.Icc 2 K, Real.exp (-(τ * Δ i ^ 2 / 2)) * (T : ℝ) * Δ i
    + ∑ i ∈ Finset.Icc 2 K, min 1 (320 * (K : ℝ) / ((T : ℝ) * Δ i ^ 3)) * (T : ℝ) * (Δ i - Δ (i - 1))

end MaxObjBandit


