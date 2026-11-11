-- Prove2me | Definitions.Def_IllCondRegMem_Learner
-- name    : IllCondRegMem_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:43.982796+00:00
-- url     : https://prove2.me/theorems/c234d400-290a-4f3a-9474-e0567b41a77b
-- title:
--   Memory-constrained regression algorithms with $M$ bits and $T$ samples
-- statement:
--   A **regression algorithm with $M$ memory bits and $T$ samples** in dimension $d$ is given by its branching program: update rules
--   $$
--   B_t:\{0,1\}^M\times\mathbb R^{d+1}\to\{0,1\}^M,\qquad t=1,\dots,T,
--   $$
--   and an output function $\hat x:\{0,1\}^M\to\mathbb R^d$, each of which may use fresh randomness. Starting from $\mathrm{Memory}_0=0$, the algorithm updates $\mathrm{Memory}_t=B_t(\mathrm{Memory}_{t-1},(a_t,b_t))$ on receiving the sample $(a_t,b_t)\in\mathbb R^d\times\mathbb R$, and after $T$ samples predicts $\hat x(\mathrm{Memory}_T)$. Computation inside a round is unrestricted; only the state kept between rounds is limited to $M$ bits.
--
--   This is the class of learners against which Theorem 1 proves its memory/sample tradeoff.
--
--   **Formalization Note** Memory states are `Fin M → Bool`, initialized all-false. The fresh randomness of each round is one uniform seed in $[0,1]$, and the output uses its own seed; no seed is shared between rounds, so everything carried between rounds is in the $M$ bits. The update maps are required to be measurable in (sample, seed) and the output map in its seed, so that success probabilities are defined. Rounds are indexed $0,\dots,T-1$.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), §2 "Branching programs", p.5 (PDF p.6)

import Mathlib
import Definitions.Def_IllCondRegMem_projMat

open MeasureTheory

namespace IllCondRegMem

/-- The memory states `{0,1}^M` of an `M`-bit learner. -/
abbrev Mem (M : ℕ) := Fin M → Bool

/-- **Memory-constrained regression algorithm** (branching program) with `M` memory bits and
`T` samples in dimension `d`.
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), §2
"Branching programs", p.5: "a regression algorithm for M memory bits and T samples is defined by
its branching program. This is the collection of update rules B_t : {0,1}^M × ℝ^{d+1} → {0,1}^M
for t ∈ [T] and an output function x̂ : {0,1}^M → ℝ^d. Both may be potentially randomized using
fresh randomness on each round."

`upd t m (a, b) u` is the new memory state after round `t` (rounds indexed `0, …, T−1`) from
memory `m`, sample `(a, b)` and fresh seed `u`; `out m u` is the prediction from the final memory
`m` and a fresh seed `u`. The initial memory is the all-zero state.

**Formalization Note.** The fresh randomness of each round is one uniform seed in `[0,1]`
(every randomized map into the finite set `{0,1}^M`, or into `ℝ^d`, is realized from one uniform
seed); no seed is shared between rounds, so all information carried between rounds is in the
`M` bits. Measurability of the update and output maps is required so that the success
probability is defined. -/
structure Learner (d M T : ℕ) where
  /-- Update rule `B_t`, with its fresh seed. -/
  upd : Fin T → Mem M → Vec d × ℝ → unitInterval → Mem M
  /-- Output function `x̂`, with its fresh seed. -/
  out : Mem M → unitInterval → Vec d
  /-- Each update rule is measurable in (sample, seed). -/
  upd_measurable : ∀ t m, Measurable fun p : (Vec d × ℝ) × unitInterval => upd t m p.1 p.2
  /-- The output function is measurable in its seed. -/
  out_measurable : ∀ m, Measurable (out m)

end IllCondRegMem


