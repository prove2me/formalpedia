-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay
-- name    : YoungConventions_AdaptivePlay_adaptivePlay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:59:52.768399+00:00
-- url     : https://prove2.me/theorems/692a77e0-4e75-4f6a-b476-3bd8bc02b774
-- title:
--   Adaptive play $P^0$ with memory $m$ and sample size $k$, display (1) (§3, p. 62)
-- statement:
--   Let $p$ be a best-reply distribution. **Adaptive play** is the Markov chain on $H$ with transition probabilities
--   $$P^0_{hh'} = \begin{cases} \displaystyle\prod_{i} p_i(s_i \mid h) & \text{if } h' \text{ is a successor of } h \text{ whose right-most element is } s,\\[4pt] 0 & \text{if } h' \text{ is not a successor of } h. \end{cases}$$
--   Each period, every player independently chooses a strategy according to $p_i(\cdot \mid h)$; the new play is appended to the history and the oldest play is forgotten.
--
--   **Formalization Note** The page prints "If $s$ is the right-most element of $h$". The right-most element of $h$ is the old last play, and the rule only makes sense, and §4 only uses it, with $s$ the right-most element of the successor $h'$, that is, the new play. The corrected reading is formalized. The memory $m$ is assumed positive (`NeZero m`), so that the right-most position $m-1$ exists. The sample size $k$ enters only through $p$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, display (1), p. 62 (PDF p. 7)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsSuccessor

namespace YoungConventions.AdaptivePlay

open Classical in
/-- **Adaptive play `P⁰` with memory `m` and sample size `k`** (Young 1993, *The Evolution of
Conventions*, Econometrica 61:57–84, §3, display (1), p. 62, PDF p. 7): "If `s` is the right-most
element of `h′`, the probability of moving from `h` to `h′` is
`P⁰_{hh′} = ∏_{i=1,n} pᵢ(sᵢ|h)`. `P⁰_{hh′} = 0` if `h′` is not a successor of `h`. We call the
process `P⁰` *adaptive play with memory `m` and sample size `k`*."

`adaptivePlay p` is the transition matrix on the state space `H` (sequences of `m` plays): if `h′`
is a successor of `h` whose new right-most play is `s`, the entry is `∏ᵢ pᵢ(sᵢ|h)`, and otherwise
it is `0`. The players choose independently given the state.

**Formalization Note.** (1) The page prints "If `s` is the right-most element of `h`"; the
right-most element of `h` is the *old* last play, and the transition rule only makes sense (and the
proofs of §4 only use it) with `s` the right-most element of the *successor* `h′`, i.e. the new
play. This corrected reading is the one formalized. (2) The memory `m` and the sample size `k`
enter only through the distributions `p` (see `IsBestReplyDistribution`); `[NeZero m]` makes the
right-most position `m − 1` exist (the paper has `1 ≤ k ≤ m`). (3) Position `m − 1` is the most
recent play (see `History`). -/
noncomputable def adaptivePlay {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] {m : ℕ} [NeZero m] (p : ∀ i, History S m → S i → ℝ) :
    Matrix (History S m) (History S m) ℝ :=
  fun h h' =>
    if IsSuccessor h h' then
      ∏ i, p i h (h' ⟨m - 1, Nat.sub_lt (NeZero.pos m) Nat.one_pos⟩ i)
    else 0

end YoungConventions.AdaptivePlay


