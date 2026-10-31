-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_width
-- name    : FoundationsRL_EluderUCB_width
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:42.935858+00:00
-- url     : https://prove2.me/theorems/29ddbc74-ec61-4cc2-b354-178d77b7f684
-- title:
--   Lemma 12: the width $w^t(\pi)$
-- statement:
--   For a class $\mathcal F$, a function $f^\star$, a parameter $\beta$ and a sequence $\pi^1,\pi^2,\dots$,
--
--   $$
--   w^t(\pi)=\sup_{f\in\mathcal F}\Bigl\{f(\pi)-f^\star(\pi):\ \sum_{i<t}\bigl(f(\pi^i)-f^\star(\pi^i)\bigr)^2\le\beta\Bigr\}.
--   $$
--
--   It bounds the upper confidence width at round $t$ once $f^\star$ and the functions consistent with the data are known to be close on the past.
--
--   **Formalization Note** The value is an extended real, because Lemma 12 allows any class and the supremum can be $+\infty$ there. The proof of Proposition 12 uses this with parameter $4\beta$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 12, p. 61, and the proof of Proposition 12, p. 60

import Mathlib

namespace FoundationsRL.EluderUCB

/-- **The width of Lemma 12.** Foster & Rakhlin, arXiv:2312.16730v1, Lemma 12, p. 61:
`wᵗ(π) = sup_{f ∈ F} {f(π) - f⋆(π) : ∑_{i<t} (f(πⁱ) - f⋆(πⁱ))² ≤ β}`.

**Formalization Note.** The value lies in `EReal`, because Lemma 12 fixes an arbitrary class `F`,
for which the supremum can be `+∞`; a real supremum would be the junk value `0` there. The constraint
set contains `f⋆` when `f⋆ ∈ F` and `β ≥ 0`, so the supremum is then at least `0`. Rounds are indexed
from `1`; `Finset.Ico 1 t` is `{1, …, t - 1}`. In the proof of Proposition 12 the width is used with
parameter `4β`, for the set `F̄ᵗ` of p. 60. -/
noncomputable def width {Act : Type*} (F : Set (Act → ℝ)) (fstar : Act → ℝ) (β : ℝ) (π : ℕ → Act)
    (t : ℕ) (p : Act) : EReal :=
  ⨆ (f : Act → ℝ) (_ : f ∈ F ∧ ∑ i ∈ Finset.Ico 1 t, (f (π i) - fstar (π i)) ^ 2 ≤ β),
    ((f p - fstar p : ℝ) : EReal)

end FoundationsRL.EluderUCB


