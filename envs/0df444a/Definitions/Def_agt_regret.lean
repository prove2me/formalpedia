-- Prove2me | Definitions.Def_agt_regret
-- name    : agt_regret
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-12T03:32:06.163141+00:00
-- url     : https://prove2.me/theorems/cdbf8f04-7722-4fcc-a3a0-e65e13a9691f
-- title:
--   The online model, regret, and correlated equilibria
-- statement:
--   This bundle fixes the online-learning vocabulary of Chapter 4 (Blum–Mansour) of *Algorithmic Game Theory*, §§4.2 and 4.4. There are $n$ actions; at each time $t$ an online algorithm selects a distribution over actions from the loss vectors seen so far, then the adversary reveals $\ell^t$ and the algorithm suffers the expected loss.
--
--   1. **`OnlineAlgorithm`** — an online algorithm is a rule mapping every finite history of observed loss vectors to the vector played next; **`algPlay`** applies it to the history $[\ell^0,\dots,\ell^{t-1}]$, so play at time $t$ depends only on strictly earlier losses.
--   2. **`algLoss`** — the cumulative expected loss $L_H^T = \sum_{t<T}\sum_i p^t_i \ell^t_i$; **`actionLoss`** — the benchmark $L_k^T = \sum_{t<T} \ell^t_k$ of a fixed action (§4.2).
--   3. **`swapLoss`** — the loss $L_{H,F}^T = \sum_{t<T}\sum_i p^t_i \ell^t_{F(i)}$ of the play rewired by a memoryless modification rule $F$; swap regret compares $L_H$ against $\min_F L_{H,F}$ (§4.2).
--   4. **`detPlay`** — the play of a deterministic algorithm, which selects a single action from the history (§4.3.1).
--   5. **`pwWeights`, `pwProb`** — the Polynomial Weights algorithm (§4.3.3): all weights start at $1$, the weight of action $i$ is multiplied by $(1-\eta\,\ell^t_i)$ after each step, and the play is the normalized weight vector.
--   6. **`IsCorrelatedEquilibrium`** — Definition 4.11 in the swap-function form: a joint distribution $Q$ on action vectors such that for every player and every switching rule $F$ on that player's own actions, $\mathbb{E}_Q[c_i(s)] \le \mathbb{E}_Q[c_i(F(s_i),s_{-i})] + \varepsilon$.
--
--   *A note on conventions.* Algorithms are deterministic functions of the history, with randomization carried by the mixed action — the standard formal reading of the full-information model; nothing in the definitions constrains outputs to be distributions or losses to be bounded, those are hypotheses of the theorems. In `pwProb` the normalizing quotient is Lean's total division: under the theorems' hypotheses ($0<\eta\le 1/2$, losses in $[0,1]$) every weight is positive and the quotient is a genuine distribution; the junk value $0$ outside that regime is never relied on.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Ch. 4, Sections 4.2-4.4, pp. 81-92

import Definitions.Def_agt_games

/-!
The adversarial online-learning model and regret vocabulary of Chapter 4
(Blum–Mansour, "Learning, Regret Minimization, and Equilibria") of
Nisan–Roughgarden–Tardos–Vazirani (eds.), *Algorithmic Game Theory* (2007),
§§4.2 and 4.4.

There are `n` actions.  At each time `t` an online algorithm selects a
distribution over the actions as a function of the loss vectors it has seen
so far; then the adversary reveals the loss vector `ℓ t : Fin n → ℝ` and the
algorithm suffers the expected loss `∑ i, p i * ℓ t i` (§4.2, full
information model).  An algorithm is represented by the deterministic map
from the observed history (the list `[ℓ 0, …, ℓ (t-1)]`) to the distribution
played, which is the standard formal reading of "selects `pᵗ` possibly
depending on the past".

Chapter 4 works with losses (players minimize), matching the book's scaling
of payoffs into `[0,1]`; boundedness is imposed by hypotheses on the
theorems, never by the definitions.
-/

namespace AGT

open Finset

variable {n : ℕ}

/-- An **online algorithm** on `n` actions: a rule assigning to every finite
history of observed loss vectors the mixed action played next (§4.2). -/
def OnlineAlgorithm (n : ℕ) : Type :=
  List (Fin n → ℝ) → Fin n → ℝ

/-- The distribution the algorithm `A` plays at time `t` against the loss
sequence `ℓ`: `A` applied to the history `[ℓ 0, …, ℓ (t-1)]` (§4.2). -/
def algPlay (A : OnlineAlgorithm n) (ℓ : ℕ → Fin n → ℝ) (t : ℕ) : Fin n → ℝ :=
  A ((List.range t).map ℓ)

/-- The cumulative (expected) loss `L_H^T = ∑_{t<T} ∑_i pᵗᵢ ℓᵗᵢ` of the
algorithm over the first `T` steps (§4.2). -/
def algLoss (A : OnlineAlgorithm n) (ℓ : ℕ → Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ∑ i, algPlay A ℓ t i * ℓ t i

/-- The cumulative loss `L_k^T = ∑_{t<T} ℓᵗ_k` of the single action `k`
(§4.2); the external-regret benchmark is its minimum over `k`. -/
def actionLoss (ℓ : ℕ → Fin n → ℝ) (k : Fin n) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ℓ t k

/-- The cumulative loss `L_{H,F}` of the play modified by the memoryless
rule `F` (§4.2): at each step the probability the algorithm put on action
`i` is shifted to `F i`, so the modified loss is `∑ i, pᵗᵢ ℓᵗ_{F i}`.  The
**swap regret** of `A` is `algLoss − min_F swapLoss` over all `F`. -/
def swapLoss (A : OnlineAlgorithm n) (ℓ : ℕ → Fin n → ℝ) (F : Fin n → Fin n)
    (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ∑ i, algPlay A ℓ t i * ℓ t (F i)

/-- A **deterministic** online algorithm selects a single action from the
history (§4.3.1); this is its play at time `t`. -/
def detPlay (D : List (Fin n → ℝ) → Fin n) (ℓ : ℕ → Fin n → ℝ) (t : ℕ) :
    Fin n :=
  D ((List.range t).map ℓ)

/-- The weights of the **Polynomial Weights** algorithm (§4.3.3): every
action starts at weight `1`, and after each step the weight of action `i` is
multiplied by `(1 - η ℓᵗᵢ)`. -/
def pwWeights (η : ℝ) (ℓ : ℕ → Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun i => pwWeights η ℓ t i * (1 - η * ℓ t i)

/-- The distribution played by the **Polynomial Weights** algorithm at time
`t`: weights normalized by their sum (§4.3.3).  For `0 < η ≤ 1/2` and losses
in `[0,1]` all weights are positive, so the quotient is a genuine
distribution; outside that regime the definition still evaluates (division
by zero yielding `0`) but the theorems impose the hypotheses. -/
noncomputable def pwProb (η : ℝ) (ℓ : ℕ → Fin n → ℝ) (t : ℕ) (i : Fin n) : ℝ :=
  pwWeights η ℓ t i / ∑ j, pwWeights η ℓ t j

/-- **`ε`-correlated equilibrium** (Definition 4.11, in the swap-function
form).  `Q` is a joint probability distribution on action vectors such that
no player can lower their expected cost by more than `ε` by applying any
switching rule `F` to their own coordinate of the drawn vector. -/
def IsCorrelatedEquilibrium {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] (ε : ℝ)
    (cost : ι → (∀ i, S i) → ℝ) (Q : (∀ i, S i) → ℝ) : Prop :=
  IsLottery Q ∧
    ∀ i (F : S i → S i),
      ∑ s, Q s * cost i s ≤
        ∑ s, Q s * cost i (Function.update s i (F (s i))) + ε

end AGT


