-- Prove2me | Definitions.Def_MemoryRegret_IsProbVec
-- name    : MemoryRegret_IsProbVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:25.789707+00:00
-- url     : https://prove2.me/theorems/aedee3be-4d8b-4e95-b0e3-7d05565b772f
-- title:
--   Probability vectors and event weights on a finite type
-- statement:
--   A **probability vector** on a finite set $A$ is a weight function $p:A\to\mathbb R$ with $p(a)\ge 0$ for all $a$ and $\sum_{a\in A}p(a)=1$. For a weight function $w$ and an event $E\subseteq A$ we write
--   $$\mathrm{wprob}(w,E)=\sum_{a\in E}w(a),$$
--   which is $\Pr_w[E]$ when $w$ is a probability vector.
--
--   Every distribution in the paper lives on a finite set: the feature distribution $\mu$, the prior on hypotheses, the learner's randomness and the laws of label blocks. All probabilities of the mission are therefore finite sums, with no measurability or conditioning.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), §2, p.7 (Definition 1: "µ : X → [0, 1] be a probability distribution over X")

import Mathlib

namespace MemoryRegret

/-- **Probability vectors on a finite type.**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
§2, p.7: "Let µ : X → [0, 1] be a probability distribution over X" (Definition 1); every
distribution in the paper (µ, the hidden-hypothesis prior, the learner's randomness) lives on a
finite set.

`IsProbVec p` says that `p` assigns a non-negative weight to every point and that the weights
sum to `1`.

**Formalization Note.** Distributions on finite sets are real weight functions; probabilities of
events are finite sums (`wprob`), so no measurability or conditioning is involved. -/
def IsProbVec {α : Type} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

open Classical in
/-- The weight `∑_{a ∈ E} w(a)` of an event `E` under a weight function `w` on a finite type;
for a probability vector `w` this is `Pr_w[E]`. -/
noncomputable def wprob {α : Type} [Fintype α] (w : α → ℝ) (E : α → Prop) : ℝ :=
  ∑ a, if E a then w a else 0

end MemoryRegret


