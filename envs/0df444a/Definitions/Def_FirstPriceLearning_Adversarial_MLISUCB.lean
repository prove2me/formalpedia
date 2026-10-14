-- Prove2me | Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB
-- name    : FirstPriceLearning_Adversarial_MLISUCB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:18.103978+00:00
-- url     : https://prove2.me/theorems/0ea71020-ec31-4a71-8379-7d0970b0990d
-- title:
--   Algorithm 4 (ML-IS-UCB): grid, levels, widths (13), estimates (14)–(15), elimination (16), and its run
-- statement:
--   The **Multi-Level Interval-Splitting UCB** (ML-IS-UCB) policy of Algorithm 4 for horizon $T$ uses the grid $\mathcal B=\{b^1,\dots,b^K\}$ with $b^i=(i-1)/K$, $K=\lceil\sqrt T\rceil$, together with $b^{K+1}:=1$; $L=\lceil\log_2T\rceil$ levels; a tuning parameter $\gamma>0$; and $T_0=(L+1)\lceil\sqrt T\rceil$.
--
--   1. **Initialization.** For $1\le t\le T_0$ the bidder bids $b_t=b^1=0$, and time $t$ is assigned to level $\ell$ when $\ell\lceil\sqrt T\rceil<t\le(\ell+1)\lceil\sqrt T\rceil$ ($\ell=0,1,\dots,L$). The level-0 block gives the held-out estimates $\hat p^0_j=|\Phi^0(T_0)|^{-1}\sum_{t\in\Phi^0(T_0)}\mathbb 1(b^j<m_t\le b^{j+1})$.
--   2. **Quantities at time $t>T_0$.** Write $\Phi^\ell(t)$ for the times $s\le t$ assigned to level $\ell$. For every $\ell$ and $i\in[K]$:
--   $$
--   n^\ell_{i,t}=\sum_{s\in\Phi^\ell(t-1)}\mathbb 1(b_s\le b^i),\qquad
--   w^\ell_{i,t}=\gamma\Big(\sqrt{2\log(LKT)\sum_{j\ge i}\tfrac1{n^\ell_{j,t}}\big(\hat p^0_j+\tfrac{\gamma\log(LKT)}{\lceil\sqrt T\rceil}\big)}+\tfrac{\log(LKT)}{n^\ell_{i,t}}\Big),
--   $$
--   $$
--   \hat p^\ell_{i,t}=\frac1{n^\ell_{i,t}}\sum_{s\in\Phi^\ell(t-1)}\mathbb 1(b_s\le b^i)\mathbb 1(b^i<m_s\le b^{i+1}),\qquad
--   \hat r^\ell_{i,t}=(v_t-b^i)\Big(1-\sum_{j\ge i}\hat p^\ell_{j,t}\Big),
--   $$
--   which are (12)–(15). The candidate sets are $\mathcal B^0_t=[K]$ and, by (16), $\mathcal B^\ell_t=\{i\in\mathcal B^{\ell-1}_t:\hat r^\ell_{i,t}+w^\ell_{i,t}\ge\max_{j\in\mathcal B^{\ell-1}_t}(\hat r^\ell_{j,t}+w^\ell_{j,t})-2\cdot2^{-\ell}\}$.
--   3. **Decision at time $t>T_0$.** The bidder scans $\ell=1,\dots,L$ and stops at the first level at which some $i\in\mathcal B^{\ell-1}_t$ has $w^\ell_{i,t}>2^{-\ell}$; she bids $b_t=b^i$ for an $i$ in that set chosen by a selection rule, and $t$ is assigned to level $\ell$.
--
--   The run of the algorithm against values $v$ and HOBs $m$ then determines the level of each time, the sets $\Phi^\ell(t)$, the bid indices $i(t)$ and all the quantities above. The file also defines $r_{i,t}=R(v_t,b^i)$, $\max_{i\in[K]}r_{i,t}$, $p_j=G(b^{j+1})-G(b^j)$ and the right-hand side of (18).
--
--   **Formalization Note** Grid indices are 0-based: Lean index $i$ is the paper's $b^{i+1}=i/K$, and $b^{K+1}=1$ is `grid K K`; sums $\sum_{j\ge i}$ run over $i\le j<K$. Times inside the algorithm are the paper's times $1,\dots,T$. The quantities are defined by their formulas for every $(i,\ell,t)$, not only where the loop reaches $\ell$. Because $b_s$ is a grid point, the indicators in $\hat p^0$ and (14) are computed from the feedback $y_s=\max\{b_s,m_s\}$: when $b_s\le b^i<m_s$ the bidder lost and $y_s=m_s$, and otherwise both products vanish. The algorithm recomputes its own past decisions from the observed values and feedback, so it is a non-anticipating rule with censored feedback. "An arbitrary $i$" is a selection rule `sel t ℓ S ∈ S` that may depend on the time and the level but not on the data (slip 16). If no level breaks, which does not happen for $\gamma\ge3$ and $T\ge2$ (slip 11), the convention is level $L$ and bid $b^1=0$. A maximum over an empty candidate set, which never occurs, is read as $0$. $L$ is `Nat.clog 2 T`.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 26 (grid, b^{K+1} := 1), p. 28, Algorithm 4, eqs. (12)-(16); p. 30 (p_i)

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model

open MeasureTheory

namespace FirstPriceLearning.Adversarial

/-! ## Parameters of Algorithm 4 (p. 28) -/

/-- Number of grid points `K = ⌈√T⌉`. -/
noncomputable def numGrid (T : ℕ) : ℕ := ⌈Real.sqrt T⌉₊

/-- Number of levels `L = ⌈log₂ T⌉` (`Nat.clog 2 T` is the least `L` with `T ≤ 2 ^ L`). -/
def numLevels (T : ℕ) : ℕ := Nat.clog 2 T

/-- Length of the initialization phase `T₀ = (L + 1) · ⌈√T⌉`. -/
noncomputable def initLength (T : ℕ) : ℕ := (numLevels T + 1) * numGrid T

/-- The logarithmic factor `log(LKT)` of (13). -/
noncomputable def logFactor (T : ℕ) : ℝ :=
  Real.log ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ))

/-- Grid point with 0-based index `i`: `grid K i = i / K` is the paper's `b^{i+1} = ((i+1) - 1)/K`.
In particular `grid K K = 1` is the paper's `b^{K+1} := 1` (p. 26). -/
noncomputable def grid (K i : ℕ) : ℝ := (i : ℝ) / K

/-- The count (12): `n_{j,t} = Σ_{s ∈ Φ, s < t} 𝟙(b_s ≤ b^j)`, for a set of (paper) times `Φ` and a
bid-index sequence `idx` (the bid at time `s` is `grid K (idx s)`). -/
noncomputable def obsCount (K : ℕ) (Φ : Finset ℕ) (idx : ℕ → ℕ) (j t : ℕ) : ℕ :=
  (Φ.filter (fun s => s < t ∧ grid K (idx s) ≤ grid K j)).card

/-! ## One round of Algorithm 4, as a function of the past

`rec s = (ℓ_s, i_s)` records the level and the (0-based) bid index of each past paper time `s`;
`y s` is the feedback `max{b_s, m_s}` of paper time `s`; `v s` is the value of paper time `s`.
All quantities at paper time `t` read `rec` and `y` only at times `s ≤ t - 1`, and `v` only at `t`. -/

/-- `Φ^ℓ(t) = {s ∈ [t] : ℓ_s = ℓ}`. -/
def levelSet (rec : ℕ → ℕ × ℕ) (ℓ t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter (fun s => (rec s).1 = ℓ)

/-- `n^ℓ_{i,t}` of (12). -/
noncomputable def nObs (T : ℕ) (rec : ℕ → ℕ × ℕ) (ℓ i t : ℕ) : ℕ :=
  obsCount (numGrid T) (levelSet rec ℓ (t - 1)) (fun s => (rec s).2) i t

/-- The held-out estimate `p̂^0_j = |Φ⁰(T₀)|⁻¹ Σ_{s ∈ Φ⁰(T₀)} 𝟙(b^j < m_s ≤ b^{j+1})`, computed from the
feedback `y_s` (at these times `b_s = 0`, so `𝟙(b^j < y_s ≤ b^{j+1}) = 𝟙(b^j < m_s ≤ b^{j+1})`). -/
noncomputable def phat0 (T : ℕ) (rec : ℕ → ℕ × ℕ) (y : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((levelSet rec 0 (initLength T)).card : ℝ)⁻¹ *
    ∑ s ∈ levelSet rec 0 (initLength T),
      (if grid (numGrid T) j < y s ∧ y s ≤ grid (numGrid T) (j + 1) then (1 : ℝ) else 0)

/-- The width (13): `w^ℓ_{i,t} = γ (√(2 log(LKT) Σ_{j ≥ i} (1/n^ℓ_{j,t}) (p̂⁰_j + γ log(LKT)/⌈√T⌉))
+ log(LKT)/n^ℓ_{i,t})`, with `j` ranging over the grid indices `i ≤ j < K`. -/
noncomputable def width (T : ℕ) (γ : ℝ) (rec : ℕ → ℕ × ℕ) (y : ℕ → ℝ) (ℓ i t : ℕ) : ℝ :=
  γ * (Real.sqrt (2 * logFactor T * ∑ j ∈ Finset.Ico i (numGrid T),
          (1 / (nObs T rec ℓ j t : ℝ)) * (phat0 T rec y j + γ * logFactor T / (numGrid T : ℝ)))
        + logFactor T / (nObs T rec ℓ i t : ℝ))

/-- The empirical interval probability (14):
`p̂^ℓ_{i,t} = (1/n^ℓ_{i,t}) Σ_{s ∈ Φ^ℓ(t-1)} 𝟙(b_s ≤ b^i) 𝟙(b^i < m_s ≤ b^{i+1})`, computed from the
feedback `y_s` (when `b_s ≤ b^i < m_s` the bidder lost, so `y_s = m_s`; otherwise both indicators
products vanish). -/
noncomputable def phat (T : ℕ) (rec : ℕ → ℕ × ℕ) (y : ℕ → ℝ) (ℓ i t : ℕ) : ℝ :=
  (1 / (nObs T rec ℓ i t : ℝ)) *
    ∑ s ∈ levelSet rec ℓ (t - 1),
      (if grid (numGrid T) (rec s).2 ≤ grid (numGrid T) i then (1 : ℝ) else 0) *
      (if grid (numGrid T) i < y s ∧ y s ≤ grid (numGrid T) (i + 1) then (1 : ℝ) else 0)

/-- The reward estimate (15): `r̂^ℓ_{i,t} = (v_t - b^i)(1 - Σ_{j ≥ i} p̂^ℓ_{j,t})`. -/
noncomputable def rhat (T : ℕ) (rec : ℕ → ℕ × ℕ) (y v : ℕ → ℝ) (ℓ i t : ℕ) : ℝ :=
  (v t - grid (numGrid T) i) * (1 - ∑ j ∈ Finset.Ico i (numGrid T), phat T rec y ℓ j t)

/-- The candidate sets `ℬ^ℓ_t` of (16), defined for every level by recursion:
`ℬ⁰_t = [K]` and `ℬ^ℓ_t = {i ∈ ℬ^{ℓ-1}_t : r̂^ℓ_{i,t} + w^ℓ_{i,t} ≥ max_{j ∈ ℬ^{ℓ-1}_t}(r̂^ℓ_{j,t} + w^ℓ_{j,t}) - 2·2^{-ℓ}}`.
(The maximum over an empty set, which never occurs, is read as `0`.) -/
noncomputable def cand (T : ℕ) (γ : ℝ) (rec : ℕ → ℕ × ℕ) (y v : ℕ → ℝ) (t : ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range (numGrid T)
  | ℓ + 1 =>
    let B := cand T γ rec y v t ℓ
    let ucb := fun j => rhat T rec y v (ℓ + 1) j t + width T γ rec y (ℓ + 1) j t
    let M : ℝ := if h : B.Nonempty then B.sup' h ucb else 0
    B.filter (fun i => M - 2 * (1 / 2 : ℝ) ^ (ℓ + 1) ≤ ucb i)

/-- The indices `i ∈ ℬ^{ℓ-1}_t` with width `w^ℓ_{i,t} > 2^{-ℓ}` (the exploration test at level `ℓ`). -/
noncomputable def exploreSet (T : ℕ) (γ : ℝ) (rec : ℕ → ℕ × ℕ) (y v : ℕ → ℝ) (ℓ t : ℕ) :
    Finset ℕ :=
  (cand T γ rec y v t (ℓ - 1)).filter (fun i => (1 / 2 : ℝ) ^ ℓ < width T γ rec y ℓ i t)

/-- The levels `ℓ ∈ [L]` at which the exploration test succeeds. -/
noncomputable def breakLevels (T : ℕ) (γ : ℝ) (rec : ℕ → ℕ × ℕ) (y v : ℕ → ℝ) (t : ℕ) :
    Finset ℕ :=
  (Finset.Icc 1 (numLevels T)).filter (fun ℓ => (exploreSet T γ rec y v ℓ t).Nonempty)

/-- The decision of Algorithm 4 at a paper time `t > T₀`: the inner loop breaks at the first level
`ℓ` whose exploration test succeeds, and the bidder bids `b^i` with `i = sel t ℓ (exploreSet …)`
chosen by the selection rule `sel` ("an arbitrary `i`"). The result is the pair `(ℓ, i)`.
If no level breaks (this does not happen for `γ ≥ 3`, `T ≥ 2`) the convention is `(L, 0)`, i.e.
level `L` and bid `b^1 = 0`. -/
noncomputable def decideRound (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (rec : ℕ → ℕ × ℕ) (y v : ℕ → ℝ) (t : ℕ) : ℕ × ℕ :=
  if h : (breakLevels T γ rec y v t).Nonempty then
    ((breakLevels T γ rec y v t).min' h,
      sel t ((breakLevels T γ rec y v t).min' h)
        (exploreSet T γ rec y v ((breakLevels T γ rec y v t).min' h) t))
  else (numLevels T, 0)

/-- The record `(ℓ_t, i_t)` of Algorithm 4 at every paper time `t`, given the values `v` and the
feedback `y` (both indexed by paper time). For `1 ≤ t ≤ T₀` the bid is `b^1 = 0` and the level is
the initialization block: `t ∈ Φ^ℓ(T₀) = {ℓ⌈√T⌉ + 1, …, (ℓ+1)⌈√T⌉}`, i.e. `ℓ = (t - 1) / ⌈√T⌉`.
For `t > T₀` the round is decided by `decideRound`, which sees the record only at times `< t`. -/
noncomputable def record (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v y : ℕ → ℝ) :
    ℕ → ℕ × ℕ
  | t =>
    if t ≤ initLength T then ((t - 1) / numGrid T, 0)
    else decideRound T γ sel (fun s => if s < t then record T γ sel v y s else (0, 0)) y v t
termination_by t => t

/-- Algorithm 4 (ML-IS-UCB, p. 28) as a deterministic non-anticipating bidding rule: in round
`t : Fin T` (paper time `t + 1`) it reads the values of paper times `1, …, t + 1` and the feedback
`max{b_s, m_s}` of paper times `1, …, t`, recomputes its own past decisions from them, and bids
`b^{i}` for the index `i` of `record` at paper time `t + 1`. -/
noncomputable def mlRule (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) : BidRule T :=
  fun t vs ys =>
    grid (numGrid T)
      (record T γ sel
        (fun s => if h : 1 ≤ s ∧ s ≤ t.val + 1 then vs ⟨s - 1, by omega⟩ else 0)
        (fun s => if h : 1 ≤ s ∧ s ≤ t.val then ys ⟨s - 1, by omega⟩ else 0)
        (t.val + 1)).2

/-! ## The run of Algorithm 4 against values `v` and HOBs `m` -/

/-- The bids `b_t` of ML-IS-UCB (round `t : Fin T` is paper time `t + 1`). -/
noncomputable def mlBids (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ) :
    Fin T → ℝ :=
  runBids (mlRule T γ sel) v m

/-- The value sequence indexed by paper time `1, …, T` (`0` outside). -/
def paperSeq {T : ℕ} (x : Fin T → ℝ) : ℕ → ℝ :=
  fun s => if h : 1 ≤ s ∧ s ≤ T then x ⟨s - 1, by omega⟩ else 0

/-- The record `(ℓ_t, i_t)` of the run, indexed by paper time. -/
noncomputable def runRecord (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ) :
    ℕ → ℕ × ℕ :=
  record T γ sel (paperSeq v) (paperSeq (fun t => max (mlBids T γ sel v m t) (m t)))

/-- The feedback `max{b_s, m_s}` of the run, indexed by paper time. -/
noncomputable def runFeedback (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ) :
    ℕ → ℝ :=
  paperSeq (fun t => max (mlBids T γ sel v m t) (m t))

/-- The level `ℓ` with `t ∈ Φ^ℓ(T)`, of paper time `t` in the run. -/
noncomputable def runLevel (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ)
    (t : ℕ) : ℕ :=
  (runRecord T γ sel v m t).1

/-- The bid index `i(t)` of paper time `t` in the run (the bid is `b_t = b^{i(t)}`). -/
noncomputable def runIndex (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ)
    (t : ℕ) : ℕ :=
  (runRecord T γ sel v m t).2

/-- `Φ^ℓ(t)` of the run. -/
noncomputable def runLevelSet (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ)
    (ℓ t : ℕ) : Finset ℕ :=
  levelSet (runRecord T γ sel v m) ℓ t

/-- `n^ℓ_{i,t}` of the run. -/
noncomputable def runN (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ)
    (ℓ i t : ℕ) : ℕ :=
  nObs T (runRecord T γ sel v m) ℓ i t

/-- `w^ℓ_{i,t}` of the run. -/
noncomputable def runWidth (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ)
    (ℓ i t : ℕ) : ℝ :=
  width T γ (runRecord T γ sel v m) (runFeedback T γ sel v m) ℓ i t

/-- `r̂^ℓ_{i,t}` of the run. -/
noncomputable def runRhat (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ)
    (ℓ i t : ℕ) : ℝ :=
  rhat T (runRecord T γ sel v m) (runFeedback T γ sel v m) (paperSeq v) ℓ i t

/-- `ℬ^ℓ_t` of the run. -/
noncomputable def runCand (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ)
    (ℓ t : ℕ) : Finset ℕ :=
  cand T γ (runRecord T γ sel v m) (runFeedback T γ sel v m) (paperSeq v) t ℓ

/-- `r_{i,t} = R(v_t, b^i) = (v_t - b^i) G(b^i)`, the expected reward of grid bid `i` at paper time `t`. -/
noncomputable def gridReward {T : ℕ} (μG : Measure ℝ) (v : Fin T → ℝ) (i t : ℕ) : ℝ :=
  FirstPriceLearning.Stochastic.expReward μG (paperSeq v t) (grid (numGrid T) i)

/-- `max_{i ∈ [K]} r_{i,t}`, the reward of the best grid bid at paper time `t`. -/
noncomputable def gridOracle {T : ℕ} (μG : Measure ℝ) (v : Fin T → ℝ) (t : ℕ) : ℝ :=
  ⨆ i : Fin (numGrid T), gridReward μG v i t

/-- `p_j = P(m ∈ (b^j, b^{j+1}]) = G(b^{j+1}) - G(b^j)` (p. 30). -/
noncomputable def intervalProb (T : ℕ) (μG : Measure ℝ) (j : ℕ) : ℝ :=
  FirstPriceLearning.Stochastic.cdf μG (grid (numGrid T) (j + 1)) - FirstPriceLearning.Stochastic.cdf μG (grid (numGrid T) j)

/-- The right-hand side of (18):
`γ (√(6 log(LKT) Σ_{j ≥ i} (1/n^ℓ_{j,t}) (p_j + γ log(LKT)/⌈√T⌉)) + log(LKT)/n^ℓ_{i,t})` on the run. -/
noncomputable def widthBound (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (μG : Measure ℝ)
    (v m : Fin T → ℝ) (ℓ i t : ℕ) : ℝ :=
  γ * (Real.sqrt (6 * logFactor T * ∑ j ∈ Finset.Ico i (numGrid T),
          (1 / (runN T γ sel v m ℓ j t : ℝ)) * (intervalProb T μG j + γ * logFactor T / (numGrid T : ℝ)))
        + logFactor T / (runN T γ sel v m ℓ i t : ℝ))

/-- A selection rule ("an arbitrary `i`", slip 16): `sel t ℓ S` picks an element of every nonempty
candidate set `S`; it may depend on the time `t` and the level `ℓ`, but not on the data. -/
def IsSelectionRule (sel : ℕ → ℕ → Finset ℕ → ℕ) : Prop :=
  ∀ t ℓ (S : Finset ℕ), S.Nonempty → sel t ℓ S ∈ S

end FirstPriceLearning.Adversarial


