-- Prove2me | Definitions.Def_OnlineBinCover_Alg3
-- name    : OnlineBinCover_Alg3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:06.70885+00:00
-- url     : https://prove2.me/theorems/3afdeef1-be64-406e-aba4-542438cfd2ae
-- title:
--   Algorithm 3: random-order bin covering when the input length is known
-- statement:
--   Algorithm 3 is told the input length $N$ and receives the arrivals one at a time.
--
--   1. **Stopping time (12).** $\hat t=\min\{t\in[N]:t/N\ge\mathrm{vol}(I_\sigma(t))^{-1/19}\}$, where $I_\sigma(t)$ is the set of the first $t$ arrivals.
--   2. **Sample length.** $s=\min\{2^{\lceil\log_2\hat t\rceil},N\}$, $p=s/N$, and $I_p=I_\sigma(s)$; the $s$ sample items are discarded.
--   3. $\varepsilon$ is $(p/\mathrm{vol}(I_p))^{1/24}$ rounded down to a power of two, $K=\lceil\varepsilon^{-2}\rceil$, the sample is classified as in §3 (all large if it is too small), and the blueprint is built from an LP solution on $I_p$ with fraction $p$.
--   4. The arrivals after position $s$ are assigned by the rules of the assignment phase; the value is the number of covered blueprint bins.
--
--   Inside an epoch of Algorithm 4 the arrival list may end before $N$ items; then fewer items are assigned, and nothing is covered if it ends during sampling.
--
--   **Formalization Note** Condition (12) is written $(t/N)^{19}\,\mathrm{vol}(I_\sigma(t))\ge1$, which is the same for positive volume and false at volume $0$ (where the paper's right side is $+\infty$). If no $t\le N$ satisfies it, sampling never ends ($\hat t:=N$). The LP solution and the tie-breaking priorities are arguments.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), App. D.1, pp.32–33 (PDF pp.33–34), (12) and Algorithm 3

import Mathlib
import Definitions.Def_OnlineBinCover_Blueprint

namespace OnlineBinCover

/-!
# Algorithm 3: random-order bin covering when the input length is known

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), App. D.1, pp.32–33: the stopping time (12),
the sample length `s`, Algorithm 3.

The algorithm is a procedure on an arrival list `xs` of distinct item labels, told the input length
`N` (for the whole input `xs` lists all `n` items; inside an epoch of Algorithm 4 it lists that
epoch's arrivals, possibly fewer than `N` if the input ends early).

**Formalization Note.**
* *(12).* `t̂ = min {t ∈ [N] : t/N ≥ vol(Iσ(t))^{−1/19}}` is written as `(t/N)^{19} · vol(Iσ(t)) ≥ 1`,
  the same condition for positive volume, and false at volume `0` (where the paper's right side is
  `+∞`). If no `t ∈ [N]` satisfies it (possible when the volume stays below `1`), the sampling phase
  never ends: `t̂ := N`, and nothing is covered.
* `s = min(2^{⌈log₂ t̂⌉}, N)`, written `min (2 ^ Nat.clog 2 t̂) N`; `p = s/N`; the sample is the
  first `s` arrivals; `ε` is `epsChoice p vol(Ip)`; `K = ⌈ε^{-2}⌉`.
* The blueprint is built from the LP solution `x`, an argument: statements quantify over every `x`
  meeting `LPSpec` on the sample. The remaining arrivals (after position `s`) are assigned by
  `phaseRun`; if the list ends during the sampling phase nothing is covered. The value is the number
  of covered blueprint bins.
-/

open Finset

/-- `vol(Iσ(t))` for the arrival list `xs`: the total size of its first `t` entries. -/
noncomputable def prefVol {n : ℕ} (s : Fin n → ℝ) (xs : List (Fin n)) (t : ℕ) : ℝ :=
  ((xs.take t).map s).sum

/-- The stopping time `t̂` of (12) (`N` if the condition never holds in `[N]`). -/
noncomputable def tHat {n : ℕ} (s : Fin n → ℝ) (N : ℕ) (xs : List (Fin n)) : ℕ :=
  by classical exact
    if h : ∃ t : ℕ, 1 ≤ t ∧ t ≤ N ∧ 1 ≤ ((t : ℝ) / N) ^ 19 * prefVol s xs t then Nat.find h
    else N

/-- The sample length `s = min(2^{⌈log₂ t̂⌉}, N)`. -/
noncomputable def a3Len {n : ℕ} (s : Fin n → ℝ) (N : ℕ) (xs : List (Fin n)) : ℕ :=
  min (2 ^ Nat.clog 2 (tHat s N xs)) N

/-- The sample `Ip`: the first `s` arrivals. -/
noncomputable def a3Sample {n : ℕ} (s : Fin n → ℝ) (N : ℕ) (xs : List (Fin n)) :
    Finset (Fin n) :=
  (xs.take (a3Len s N xs)).toFinset

/-- The sampling fraction `p = s/N`. -/
noncomputable def a3P {n : ℕ} (s : Fin n → ℝ) (N : ℕ) (xs : List (Fin n)) : ℝ :=
  (a3Len s N xs : ℝ) / N

/-- The accuracy `ε`, rounded from `(p/vol(Ip))^{1/24}`. -/
noncomputable def a3Eps {n : ℕ} (s : Fin n → ℝ) (N : ℕ) (xs : List (Fin n)) : ℝ :=
  epsChoice (a3P s N xs) (volOn s (a3Sample s N xs))

/-- Algorithm 3 with LP solution `x` and tie-breaking priorities: the number of covered blueprint
bins. -/
noncomputable def alg3 {n : ℕ} (s : Fin n → ℝ) (N : ℕ) (xs : List (Fin n))
    (x : (Fin (Kof (a3Eps s N xs)) → ℕ) →₀ ℝ) (prioL : LSlot (Kof (a3Eps s N xs)) → ℕ)
    (prioS : Bin (Kof (a3Eps s N xs)) → ℕ) : ℕ :=
  phaseRun s (a3Sample s N xs) (a3Eps s N xs) (a3P s N xs) x prioL prioS
    (xs.drop (a3Len s N xs))

end OnlineBinCover


