-- Prove2me | Definitions.Def_LinearZeroSumMG_findCCE
-- name    : LinearZeroSumMG_findCCE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:52:01.081484+00:00
-- url     : https://prove2.me/theorems/3fa1de90-c0d5-4a7c-b73d-b065b626a00d
-- title:
--   Algorithm 2 (FIND_CCE) and rounding rules
-- statement:
--   **Algorithm 2 (FIND_CCE).** Input: the estimates $\overline Q^k_h,\underline Q^k_h$, a state $x$ and $\varepsilon>0$.
--   1. Pick a pair $(\widetilde Q,\underset{\sim}{Q})\in\mathcal Q_\varepsilon\times\mathcal Q_\varepsilon$ with $\|\widetilde Q-\overline Q^k_h\|_\infty\le\varepsilon$ and $\|\underset{\sim}{Q}-\underline Q^k_h\|_\infty\le\varepsilon$.
--   2. Output the CCE $\widetilde\sigma(x)$ of the matrix game with payoff $\widetilde Q(x,\cdot,\cdot)$ for P1 and $\underset{\sim}{Q}(x,\cdot,\cdot)$ for P2.
--
--   A **rounding rule** performs step 1: given the episode $k$, the step $h$ and the parameters $(\overline w^k_h,(\Lambda^k_h)^{-1})$, $(\underline w^k_h,(\Lambda^k_h)^{-1})$ of the two estimates, it returns a pair of functions. It is **admissible** (for nets $N_k=\mathcal Q_\varepsilon$ of the episodes $k\in[K]$) if it is Borel measurable and, whenever both estimates lie in the class $\mathcal Q$ of episode $k$, the returned pair lies in $N_k\times N_k$ and is $\varepsilon$-close to them.
--
--   Rounding to a finite net is what makes the value estimates range over a finite class, so that a union bound gives uniform concentration (Lemma 2).
--
--   **Formalization Note** The pick may depend on $k$, $h$ and the parameters, but not on the state $x$: one rounded pair serves all states, as in Lemma 2's proof. The theorems quantify over every admissible rule.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Algorithm 2, p.11

import Mathlib
import Definitions.Def_LinearZeroSumMG_QClass

namespace LinearZeroSumMG

variable {S A : Type*} {d : ℕ}

/-- The parameters `(w, M) ∈ ℝ^d × ℝ^{d×d}` of a function `qFun φ H β ρ w M` of the class (5). -/
abbrev Params (d : ℕ) : Type := (Fin d → ℝ) × (Fin d → Fin d → ℝ)

/-- A rounding rule: given the episode `k`, the step `h`, and the parameters `(w̄, M)` of the upper
estimate `Q̄ = qFun φ H β 1 w̄ M` and `(w̲, M)` of the lower estimate `Q̲ = qFun φ H β (−1) w̲ M`, it
returns the pair `(Q̃, Q̰)` picked in line 2 of Algorithm 2. -/
abbrev RoundRule (S A : Type*) (d : ℕ) : Type _ :=
  ℕ → ℕ → Params d → Params d → (S → A → A → ℝ) × (S → A → A → ℝ)

/-- **Line 2 of Algorithm 2 (`FIND_CCE`): the rounding into the ε-net.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Algorithm 2, p.11:
"1: Input: `Q̄^k_h`, `Q̲^k_h`, `x` and discretization parameter `ε > 0`.
2: Pick a pair `(Q̃, Q̰)` in `𝒬_ε × 𝒬_ε` satisfying `‖Q̃ − Q̄^k_h‖_∞ ≤ ε` and `‖Q̰ − Q̲^k_h‖_∞ ≤ ε`."

`IsRoundingRule φ H β ε N K round` says:
1. for every episode `k ∈ [1, K]`, step `h`, and parameters `p = (w̄, M)`, `q = (w̲, M')` such that
   `qFun φ H β 1 w̄ M` and `qFun φ H β (−1) w̲ M'` lie in the class `𝒬` of episode `k`, the picked
   pair lies in `N k × N k` and is `ε`-close to them in `‖·‖_∞`;
2. for every `k`, `h` and every pair `f`, the set of inputs mapped to `f` is Borel measurable.

**Formalization Note**
- `N k` is the ε-net `𝒬_ε` used in episode `k` (the class depends on `k`).
- "Pick a pair" allows any qualifying pair. The theorems quantify over every rule with properties
  1–2; the rule may depend on `k`, on `h` and on the parameters (not only on the functions they
  define), but not on the state `x` (Lemma 2's proof rounds `Q̄^k_{h+1}` once, for all `x`). This
  covers every choice that is a function of FIND_CCE's input pair.
- Measurability (2) excludes only rules for which the analysis's random quantities are not
  measurable. -/
def IsRoundingRule (φ : S → A → A → Fin d → ℝ) (H : ℕ) (β ε : ℝ)
    (N : ℕ → Finset (S → A → A → ℝ)) (K : ℕ) (round : RoundRule S A d) : Prop :=
  (∀ k ∈ Finset.Icc 1 K, ∀ (h : ℕ) (p q : Params d),
    qFun φ H β 1 p.1 p.2 ∈ QClass φ H β k → qFun φ H β (-1) q.1 q.2 ∈ QClass φ H β k →
      (round k h p q).1 ∈ N k ∧ (round k h p q).2 ∈ N k ∧
      (∀ x a b, |(round k h p q).1 x a b - qFun φ H β 1 p.1 p.2 x a b| ≤ ε) ∧
      (∀ x a b, |(round k h p q).2 x a b - qFun φ H β (-1) q.1 q.2 x a b| ≤ ε)) ∧
  ∀ (k h : ℕ) (f : (S → A → A → ℝ) × (S → A → A → ℝ)),
    MeasurableSet {pq : Params d × Params d | round k h pq.1 pq.2 = f}

/-- **Algorithm 2 (`FIND_CCE`).** arXiv:2002.07066v3, Algorithm 2, p.11: "3: For the input `x`, let
`σ̃(x)` be the CCE (cf. equation (1)) of the matrix game with payoff matrices `Q̃(x, ·, ·)` for P1 and
`Q̰(x, ·, ·)` for P2. 4: Output: `σ̃(x)`."

`findCCE cce round k h p q x = cce (Q̃(x, ·, ·)) (Q̰(x, ·, ·))` where `(Q̃, Q̰) = round k h p q`; P1
maximizes `Q̃`, P2 minimizes `Q̰`. -/
noncomputable def findCCE (cce : (A → A → ℝ) → (A → A → ℝ) → (A × A → ℝ))
    (round : RoundRule S A d) (k h : ℕ) (p q : Params d) (x : S) : A × A → ℝ :=
  cce ((round k h p q).1 x) ((round k h p q).2 x)

end LinearZeroSumMG


