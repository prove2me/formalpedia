-- Prove2me | Definitions.Def_LiquidDemocracy_Upward_Urn
-- name    : LiquidDemocracy_Upward_Urn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:48.827839+00:00
-- url     : https://prove2.me/theorems/f6fc947b-c71f-4eb8-8177-5a39632e238d
-- title:
--   §3, pp. 12–13 — the infinite Pólya urn with attachment probability p, its largest bin L^p_t, the k-th bin U^(k)_t and the bin W^(k)_t born at time k
-- statement:
--   This file defines the infinite Pólya urn process of §3 (p. 12) and the single-bin process of p. 13.
--
--   1. **The urn.** A Pólya urn process with attachment probability $p$ begins at time $t=1$ with one ball in one bin. At each time $t>1$ a new ball arrives: with probability $1-p$ it opens a new bin; with probability $p$ it joins an existing bin, chosen with probability proportional to the number of balls in it. So, from time $t$ (with $t$ balls) to time $t+1$, the new ball joins bin $k$ with probability $p\,s_k/t$, where $s_k$ is the size of bin $k$. The state is the list of bin sizes in order of birth.
--   2. **Largest bin and $k$-th bin.** $L^p_t$ is the largest bin size at time $t$; $U^{(k)}_t$ is the size of the $k$-th bin to be born ($0$ before its birth), bins being numbered from $1$.
--   3. **A bin born at time $k$.** $W^{(k)}_t$ is the size at time $t$ of a bin born at time $k$: $W^{(k)}_k=1$, and for $t>k$
--   $$W^{(k)}_t=\begin{cases}W^{(k)}_{t-1}+1 & \text{with probability } \dfrac{p\,W^{(k)}_{t-1}}{t-1},\\[4pt] W^{(k)}_{t-1} & \text{with probability } 1-\dfrac{p\,W^{(k)}_{t-1}}{t-1},\end{cases}$$
--   the same recurrence as $U^{(k)}_t$; before time $k$ it is $0$.
--
--   These are the objects of Lemma 2 and of the coupling in the proof of Theorem 1.
--
--   **Formalization Note** The laws are measures built step by step with `Measure.bind`: `urnLaw p t` on lists of bin sizes (with the discrete σ-algebra, which Mathlib does not provide on `List ℕ`), `wLaw p k t` on ℕ. Time $0$ (no ball) is the empty list. Transition probabilities are `ENNReal.ofReal` of the page's expressions; they lie in $[0,1]$ whenever $p\in[0,1]$, $k\ge1$.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, p. 12 (Pólya urn process, L^p_t) and p. 13 (U^(k)_t recurrence, W^(k)_t)

import Mathlib

namespace LiquidDemocracy.Upward

/-! # The infinite Pólya urn with attachment probability `p` and the single-bin process `W^(k)`
(Berinsky et al., *Tracking Truth with Liquid Democracy*, arXiv:2107.11868v3, §3 pp. 12–13). -/

open MeasureTheory

/-- Bin-size lists (bins in order of birth) carry the discrete σ-algebra; Mathlib has none on `List ℕ`. -/
instance instMeasurableSpaceListNat : MeasurableSpace (List ℕ) := ⊤

/-- p. 12: one step of the urn, from time `t` (there are `t` balls, with bin sizes `s`) to time `t + 1`:
with probability `1 − p` the new ball opens a new bin; otherwise it joins bin `k` with probability
`p · s_k / t`, proportional to the number of balls in it. -/
noncomputable def urnStep (p : ℝ) (t : ℕ) (s : List ℕ) : Measure (List ℕ) :=
  ENNReal.ofReal (1 - p) • Measure.dirac (s ++ [1]) +
  ∑ k : Fin s.length, ENNReal.ofReal (p * s.get k / t) • Measure.dirac (s.modify k (· + 1))

/-- p. 12: the law of the bin sizes (in order of birth) at time `t`, i.e. after `t` steps: at time `1`
there is one ball in one bin; time `0` (no ball yet) is the empty list. -/
noncomputable def urnLaw (p : ℝ) : ℕ → Measure (List ℕ)
  | 0 => Measure.dirac []
  | 1 => Measure.dirac [1]
  | t + 2 => (urnLaw p (t + 1)).bind (urnStep p (t + 1))

/-- p. 12: `L^p_t`, the largest number of balls in a bin (`0` for no bin). -/
def maxBin (s : List ℕ) : ℕ := s.foldr max 0

/-- p. 12: `U^(k)_t`, the size of the `k`-th bin to be born (bins numbered from `1`); `0` if it is not
born yet. -/
def binSize (s : List ℕ) (k : ℕ) : ℕ := s.getD (k - 1) 0

/-- p. 13: one step of `W^(k)` from time `t` (current size `w`) to time `t + 1`: it grows by one with
probability `p · w / t` and stays put otherwise. -/
noncomputable def wStep (p : ℝ) (t w : ℕ) : Measure ℕ :=
  ENNReal.ofReal (p * w / t) • Measure.dirac (w + 1) +
  ENNReal.ofReal (1 - p * w / t) • Measure.dirac w

/-- `wChain p k m` is the law of `W^(k)_{k+m}`: the bin is born at time `k` with one ball. -/
noncomputable def wChain (p : ℝ) (k : ℕ) : ℕ → Measure ℕ
  | 0 => Measure.dirac 1
  | m + 1 => (wChain p k m).bind (wStep p (k + m))

/-- p. 13: the law of `W^(k)_t`, the size at time `t` of a bin born at time `k` (`0` before its birth). -/
noncomputable def wLaw (p : ℝ) (k t : ℕ) : Measure ℕ :=
  if k ≤ t then wChain p k (t - k) else Measure.dirac 0

end LiquidDemocracy.Upward


