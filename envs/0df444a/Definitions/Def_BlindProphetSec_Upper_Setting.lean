-- Prove2me | Definitions.Def_BlindProphetSec_Upper_Setting
-- name    : BlindProphetSec_Upper_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:31:36.506704+00:00
-- url     : https://prove2.me/theorems/3555986a-a335-437c-ac22-f262c5069bbb
-- title:
--   §1.2 and §5, pp. 3–4, 18–19 — random-order prophet secretary, general randomized stopping strategies, E(V_{σ_T}), E(max), the §5 instance and the time-j rule
-- statement:
--   This file fixes the model of the **prophet secretary problem** and the objects of the upper-bound construction of §5.
--
--   1. **Instances.** An instance with $N$ variables is a family of laws $\mu_0,\dots,\mu_{N-1}$ on $\mathbb R$; the values $V = (V_0,\dots,V_{N-1})$ are independent with $V_i \sim \mu_i$ (product measure $\bigotimes_i \mu_i$).
--   2. **Random order.** The arrival order is a permutation $\sigma$ of $\{0,\dots,N-1\}$, uniform and independent of the values; at (0-based) time $j$ the gambler sees the variable $\sigma_j$ and its value $V_{\sigma_j}$.
--   3. **Strategies.** A strategy $s$ is a family of decision rules $s_j(h,\omega)\in\{\text{stop},\text{continue}\}$, one per time $j$, where $h = \big((\sigma_0,V_{\sigma_0}),\dots,(\sigma_j,V_{\sigma_j})\big)$ is everything observed so far (identities and values, the current one included) and $\omega$ is an independent random seed, uniform on $[0,1]$. Each rule is required to be measurable in $(h,\omega)$. This is the class $\mathcal T_n$ of (randomized) stopping times of the gambler's filtration.
--   4. **Reward and value.** The stopping time $T$ is the first time at which the strategy says stop; the reward is $V_{\sigma_T}\mathbf 1_{T<\infty}$, i.e. $0$ if it never stops. The value of $s$ on the instance is
--   $$\mathbb E(V_{\sigma_T}) = \frac{1}{N!}\sum_{\sigma}\int V_{\sigma_T}\, d\Big(\bigotimes_i \mu_i \otimes \mathrm{Unif}[0,1]\Big),$$
--   an element of $[0,\infty]$. The conditional value given $\sigma_k = i$ is written in joint form $N\cdot\mathbb E(V_{\sigma_T}\mathbf 1_{\sigma_k=i})$, using $\mathbb P(\sigma_k=i)=1/N$.
--   5. **Prophet.** $\mathbb E(\max_i V_i)$, also in $[0,\infty]$.
--   6. **The §5 instance.** For $n\ge 1$ and $a\in[0,1]$: $n+1$ variables, where $V_1,\dots,V_n$ equal $n$ with probability $1/n^2$ and $0$ otherwise, and $V_{n+1}\equiv a$.
--   7. **The time-$j$ rule.** For $j\in[n+1]$: accept any of $V_1,\dots,V_n$ showing the value $n$, and accept $V_{n+1}$ if and only if it arrives at (1-based) time $j$ or later.
--
--   These are the objects about which Theorem 1.3 and the §5 computations are stated.
--
--   **Formalization Note** Indices are 0-based in Lean: the paper's $V_i$ is coordinate $i-1$, $V_{n+1}$ is `Fin.last n`, and the paper's time $j$ is Lean's time $j-1$. The time-$j$ rule recognizes $V_{n+1}$ by its identity, not by its value (the values $a$, $0$ and $n$ may coincide). The average over the $N!$ permutations replaces a measure on permutations. Expectations are lower Lebesgue integrals of $\max(\cdot,0)$ in $[0,\infty]$, so no integrability hypothesis is needed; on instances with nonnegative values this is the ordinary expectation. `jRule` carries its measurability proof, which shows the measurability requirement on strategies is satisfiable.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 3 (§1.2, model), p. 4 (reward V_{σ_T} 1_{T<∞}), pp. 18–19 (§5, instance and time-j rule)

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

namespace BlindProphetSec.Upper

open MeasureTheory

noncomputable section

/-- A (possibly randomized) stopping strategy for the prophet secretary problem with `N`
variables. At the 0-based time `j` the gambler has seen the identities and values
`(σ₀, V_{σ₀}), …, (σⱼ, V_{σⱼ})` of the variables shown so far (the current one included),
encoded as a map `Fin (j + 1) → Fin N × ℝ`, and an independent random seed `ω ∈ [0, 1]`;
`stop j h ω = true` means "stop now and take the current value". Measurability of each
decision rule is part of being a stopping time. -/
structure Strategy (N : ℕ) where
  stop : (j : Fin N) → (Fin (j.val + 1) → Fin N × ℝ) → ℝ → Bool
  measurable_stop : ∀ j : Fin N,
    Measurable (fun p : (Fin (j.val + 1) → Fin N × ℝ) × ℝ => stop j p.1 p.2)

/-- The history observed at 0-based time `j` when the values are `v` and the arrival order
is `σ` (the variable shown at time `l` is `σ l`): the pairs `(σ l, v (σ l))`, `l ≤ j`. -/
def history {N : ℕ} (v : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (j : Fin N) :
    Fin (j.val + 1) → Fin N × ℝ :=
  fun l => (σ ⟨l.val, Nat.lt_of_lt_of_le l.isLt j.isLt⟩,
    v (σ ⟨l.val, Nat.lt_of_lt_of_le l.isLt j.isLt⟩))

/-- The set of times at which strategy `s` says "stop" on `(v, σ, ω)`. -/
def stopSet {N : ℕ} (s : Strategy N) (v : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (ω : ℝ) :
    Finset (Fin N) :=
  Finset.univ.filter (fun j => s.stop j (history v σ j) ω = true)

/-- The gambler's reward `V_{σ_T} 1_{T < ∞}`: the value shown at the first time `T` at which
the strategy stops, and `0` if it never stops. -/
def reward {N : ℕ} (s : Strategy N) (v : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (ω : ℝ) : ℝ :=
  if h : (stopSet s v σ ω).Nonempty then v (σ ((stopSet s v σ ω).min' h)) else 0

/-- The expected reward `E(V_{σ_T})` of strategy `s` on the instance `μ` (independent values
`Vᵢ ∼ μ i`), with `σ` uniform on the permutations of `Fin N` and independent of the values and
of the seed: the average over the `N!` permutations of the expected reward under
`(⊗ᵢ μ i) ⊗ BlindProphetSec.Blind.unif01`. -/
def value {N : ℕ} (s : Strategy N) (μ : Fin N → Measure ℝ) : ENNReal :=
  (1 / (N.factorial : ENNReal)) * ∑ σ : Equiv.Perm (Fin N),
    ∫⁻ p, ENNReal.ofReal (reward s p.1 σ p.2) ∂((Measure.pi μ).prod BlindProphetSec.Blind.unif01)

/-- The conditional expected reward `E(V_{σ_T} | σ_k = i)` (0-based time `k`, variable `i`),
written in joint form as `N · E(V_{σ_T} 1_{σ_k = i})`, since `P(σ_k = i) = 1/N`. -/
def condValue {N : ℕ} (s : Strategy N) (μ : Fin N → Measure ℝ) (k i : Fin N) : ENNReal :=
  (N : ENNReal) * ((1 / (N.factorial : ENNReal)) *
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => σ k = i),
      ∫⁻ p, ENNReal.ofReal (reward s p.1 σ p.2) ∂((Measure.pi μ).prod BlindProphetSec.Blind.unif01))

/-- The instance of §5 with `n + 1` variables: the coordinates `i < n` (the paper's
`V₁, …, Vₙ`) equal `n` with probability `1/n²` and `0` otherwise; the last coordinate (the
paper's `V_{n+1}`) is the constant `a`. -/
def hardLaw (n : ℕ) (a : ℝ) : Fin (n + 1) → Measure ℝ := fun i =>
  if i.val < n then
    ENNReal.ofReal (1 / (n : ℝ) ^ 2) • Measure.dirac (n : ℝ) +
      ENNReal.ofReal (1 - 1 / (n : ℝ) ^ 2) • Measure.dirac 0
  else Measure.dirac a

/-- The time-`j` rule of §5 (`j` is a 1-based time): stop on a variable among `V₁, …, Vₙ`
whose value is `n`, and stop on the constant variable `V_{n+1}` if and only if it appears at
1-based time `j` or later. The seed is ignored. -/
def jRule (n : ℕ) (j : ℕ) : Strategy (n + 1) where
  stop l h _ := decide (((h (Fin.last l.val)).1 ≠ Fin.last n ∧ (h (Fin.last l.val)).2 = (n : ℝ)) ∨
    ((h (Fin.last l.val)).1 = Fin.last n ∧ j ≤ l.val + 1))
  measurable_stop l := by
    apply measurable_to_bool
    have h1 : Measurable
        (fun p : (Fin (l.val + 1) → Fin (n + 1) × ℝ) × ℝ => (p.1 (Fin.last l.val)).1) :=
      measurable_fst.comp ((measurable_pi_apply _).comp measurable_fst)
    have h2 : Measurable
        (fun p : (Fin (l.val + 1) → Fin (n + 1) × ℝ) × ℝ => (p.1 (Fin.last l.val)).2) :=
      measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)
    simp only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq]
    refine MeasurableSet.union (MeasurableSet.inter ?_ ?_) (MeasurableSet.inter ?_ ?_)
    · exact (h1 (measurableSet_singleton (Fin.last n))).compl
    · exact h2 (measurableSet_singleton _)
    · exact h1 (measurableSet_singleton _)
    · exact MeasurableSet.const _

end

end BlindProphetSec.Upper


