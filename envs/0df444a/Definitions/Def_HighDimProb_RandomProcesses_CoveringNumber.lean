-- Prove2me | Definitions.Def_HighDimProb_RandomProcesses_CoveringNumber
-- name    : HighDimProb_RandomProcesses_CoveringNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:32:11.913925+00:00
-- url     : https://prove2.me/theorems/9523e15e-a017-49ff-8c5f-965a887fd94d
-- title:
--   The covering number $N(T,d,\varepsilon)$ of a (pseudo-)metric space
-- statement:
--   This is the **covering number** of a (pseudo-)metric space, the basic measure of metric size
--   that Sudakov's minoration inequality (Theorem 7.4.1) relates to the expected supremum of a
--   Gaussian process.
--
--   Let $(T,d)$ be a (pseudo-)metric space and $\varepsilon > 0$. A subset $N \subseteq T$ is an
--   $\varepsilon$-net of $T$ if every point of $T$ is within distance $\varepsilon$ of some point of
--   $N$, i.e. $\forall t \in T\ \exists t' \in N : d(t,t') \le \varepsilon$. The covering number
--   $N(T,d,\varepsilon)$ is the smallest possible cardinality of a (finite) $\varepsilon$-net of $T$;
--   if $T$ admits no finite $\varepsilon$-net, $N(T,d,\varepsilon) := \infty$.
--
--   **Formalization Note** The value is taken in `ℕ∞ = WithTop ℕ`: it is the infimum, over the
--   subtype of finite $\varepsilon$-nets of $T$ (subsets whose defining property is exactly the
--   inequality above), of their cardinality. Because the infimum of an empty family in a complete
--   lattice is $\top$, this reproduces the book's own convention exactly — no case split is needed
--   to set $N(T,d,\varepsilon):=\infty$ when no finite net exists.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 82, Definition 4.2.2 (K := T); used in Section 7.4, p. 170

import Mathlib

namespace HighDimProb.RandomProcesses

/-- The **covering number** `N(T, d, ε)`: the smallest cardinality of an `ε`-net of `T` in the
(pseudo)metric `d`, i.e. of a finite `N ⊆ T` such that every point of `T` is within distance `ε`
of some point of `N`. Vershynin, *High-Dimensional Probability* (2018), p. 82 (PDF p. 90),
Definition 4.2.2 (`K := T`), restated as used in Section 7.4 (p. 170, PDF p. 178). Valued in
`ℕ∞ = WithTop ℕ`: taking the infimum of `Finset.card` over the subtype of finite `ε`-nets gives
exactly the book's own convention (footnote 6, p. 170) that `N(T, d, ε) := ∞` when `T` admits no
finite `ε`-net, since the infimum of an empty family in a complete lattice is `⊤`. -/
noncomputable def coveringNumber {T : Type} (d : T → T → ℝ) (ε : ℝ) : ℕ∞ :=
  ⨅ (N : {s : Finset T // ∀ t : T, ∃ t' ∈ s, d t t' ≤ ε}), (N.1.card : ℕ∞)

end HighDimProb.RandomProcesses


