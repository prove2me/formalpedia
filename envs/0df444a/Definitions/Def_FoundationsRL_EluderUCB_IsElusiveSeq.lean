-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_IsElusiveSeq
-- name    : FoundationsRL_EluderUCB_IsElusiveSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:40.450468+00:00
-- url     : https://prove2.me/theorems/67cdfb1e-7d1d-4521-a7bb-dfd7b87f5e0f
-- title:
--   Definition 6, (4.9): sequences of surprising decisions
-- statement:
--   Let $\mathcal F$ be a set of functions $\Pi\to\mathbb R$, let $f^\star:\Pi\to\mathbb R$, and let $\varepsilon\in\mathbb R$. A finite sequence of decisions $\pi^1,\dots,\pi^d\in\Pi$ satisfies condition (4.9) if for every $t\in[d]$ there is a function $f^t\in\mathcal F$ with
--
--   $$
--   |f^t(\pi^t)-f^\star(\pi^t)|>\varepsilon
--   \qquad\text{and}\qquad
--   \sum_{i<t}\bigl(f^t(\pi^i)-f^\star(\pi^i)\bigr)^2\le\varepsilon^2.
--   $$
--
--   So each new decision can surprise a learner who has estimated $f^\star$ well on all the preceding decisions. The length of the longest such sequence is the first layer of the eluder dimension.
--
--   **Formalization Note** The index $t\in[d]$ is an element of `Fin d`. The first inequality is strict and the second is not, as in the source. Decisions may repeat.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Definition 6, (4.9), p. 59

import Mathlib

namespace FoundationsRL.EluderUCB

/-- **Condition (4.9) of the eluder dimension.** Foster & Rakhlin, *Foundations of Reinforcement
Learning and Interactive Decision Making*, arXiv:2312.16730v1, Definition 6, p. 59.

The sequence of decisions `π¹, …, πᵈ` satisfies (4.9) for the class `F`, the function `f⋆` and the
scale `ε` if for every `t ∈ [d]` there is `fᵗ ∈ F` with `|fᵗ(πᵗ) - f⋆(πᵗ)| > ε` and
`∑_{i<t} (fᵗ(πⁱ) - f⋆(πⁱ))² ≤ ε²`.

**Formalization Note.** The source's index `t ∈ [d]` is `t : Fin d`, shifted down by one. The first
clause is strict and the second is not, as printed. The sequence may repeat decisions, `Act` is an
arbitrary type (the source's `Π`), and `F` is an arbitrary set of functions. -/
def IsElusiveSeq {Act : Type*} (F : Set (Act → ℝ)) (fstar : Act → ℝ) (ε : ℝ) {d : ℕ}
    (π : Fin d → Act) : Prop :=
  ∀ t : Fin d, ∃ f ∈ F, ε < |f (π t) - fstar (π t)| ∧
    ∑ i ∈ Finset.Iio t, (f (π i) - fstar (π i)) ^ 2 ≤ ε ^ 2

end FoundationsRL.EluderUCB


