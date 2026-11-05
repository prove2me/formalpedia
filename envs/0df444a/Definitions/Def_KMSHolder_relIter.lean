-- Prove2me | Definitions.Def_KMSHolder_relIter
-- name    : KMSHolder_relIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:04.486049+00:00
-- url     : https://prove2.me/theorems/8b9933d7-62a8-4d8b-9daa-2736dcdbb7c4
-- title:
--   End points of chains through a sequence of relations
-- statement:
--   For relations $R_0, R_1, \dots$ on a set $X$, a point $x$ and $k \ge 0$, let $\mathrm{relIter}(R, k, x)$ be the set of all $y$ for which there are $v_0 = x, v_1, \dots, v_k = y$ with $(v_i, v_{i+1}) \in R_i$ for every $i < k$.
--
--   When each $R_i$ is the graph of an unbounded operator, $\mathrm{relIter}(R, k, x)$ is nonempty exactly when the iterated composition of the $k$ operators can be applied to $x$ step by step, every intermediate vector lying in the domain of the next operator, and it is then the single vector that composition produces. This is how the iterated products of (relative) modular powers in Araki's estimate (8) and in Lemma 4.1 (19) are stated.
--
--   **Formalization Note** For $k = 0$ the set is $\{x\}$. The relations are indexed by $\mathbb N$; only $R_0, \dots, R_{k-1}$ matter.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, eq. (8), p.5, and eq. (19), p.7 (iterated compositions)

import Mathlib

namespace KMSHolder

/-- The end points of `k`-step chains through a sequence of relations: `y ∈ relIter R k x` iff
there are `v₀ = x, v₁, …, v_k = y` with `(vᵢ, vᵢ₊₁) ∈ R i` for every `i < k`.

Used to state iterated compositions of unbounded operators step by step, as in Jäkel–Robl,
arXiv:1103.3608v2, eq. (8), p.5, and eq. (19), p.7: each step is the graph of one (possibly
unbounded) operator, so a chain exists exactly when every intermediate vector lies in the domain
of the next operator. For `k = 0` the set is `{x}`. -/
def relIter {α : Type*} (R : ℕ → Set (α × α)) (k : ℕ) (x : α) : Set α :=
  {y | ∃ v : ℕ → α, v 0 = x ∧ (∀ i < k, (v i, v (i + 1)) ∈ R i) ∧ v k = y}

end KMSHolder


