-- Prove2me | Definitions.Def_LinearZeroSumMG_IsEpsNet
-- name    : LinearZeroSumMG_IsEpsNet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:15.019658+00:00
-- url     : https://prove2.me/theorems/2fd799ea-9f8d-483a-853b-995a1f6b45c6
-- title:
--   $\varepsilon$-net in $\|\cdot\|_\infty$, and $\varepsilon$-nets of minimum size
-- statement:
--   A finite set $N$ of functions is an **$\varepsilon$-net** of a set $C$ of functions $\mathcal S\times\mathcal A\times\mathcal A\to\mathbb R$ if $N\subseteq C$ and every $Q\in C$ has some $Q'\in N$ with
--   $$
--   \|Q-Q'\|_\infty=\sup_{x,a,b}|Q(x,a,b)-Q'(x,a,b)|\le\varepsilon .
--   $$
--   It has **minimum size** if no $\varepsilon$-net of $C$ has fewer elements; its size is then the $\varepsilon$-covering number $\mathcal N_\varepsilon$ of $C$.
--
--   Algorithm 2 rounds the estimates into a fixed $\varepsilon$-net of the class $\mathcal Q$; the union bound of Lemma 2 runs over this net, so its size matters.
--
--   **Formalization Note** The net is internal ($N\subseteq C$), the convention of the covering bounds the paper cites (Vershynin 2012). $\|Q-Q'\|_\infty\le\varepsilon$ is written pointwise, which is equivalent.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §3.2, p.11; Lemma 2's proof, p.18

import Mathlib

namespace LinearZeroSumMG

variable {S A : Type*}

/-- **ε-net (ε-covering) in the `ℓ∞` norm.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §3.2, p.11: "Let `𝒬_ε` be a fixed
`ε`-covering of `𝒬` with respect to the `ℓ∞` norm `‖Q − Q'‖_∞ := sup_{x,a,b} |Q(x, a, b) − Q'(x, a, b)|`."

`IsEpsNet N C ε` says that the finite set `N` is contained in `C` and that every `Q ∈ C` has some
`Q' ∈ N` with `|Q(x, a, b) − Q'(x, a, b)| ≤ ε` at every point `(x, a, b)` (that is, `‖Q − Q'‖_∞ ≤ ε`).

**Formalization Note** The net is internal (`N ⊆ C`), the convention of the covering bounds the
paper cites (Vershynin 2012, Lemma 5.2). `‖Q − Q'‖_∞ ≤ ε` is written pointwise, which is equivalent
and avoids a real supremum over a possibly unbounded set. -/
def IsEpsNet (N : Finset (S → A → A → ℝ)) (C : Set (S → A → A → ℝ)) (ε : ℝ) : Prop :=
  (↑N : Set (S → A → A → ℝ)) ⊆ C ∧ ∀ Q ∈ C, ∃ Q' ∈ N, ∀ x a b, |Q x a b - Q' x a b| ≤ ε

/-- **An ε-net of minimum cardinality** (the `ε`-net `𝒬_ε` of arXiv:2002.07066v3, p.11, whose size
is the `ε`-covering number `𝒩_ε`, as used in Lemma 2's proof, p.18: "`|𝒬_ε × 𝒬_ε| = (𝒩_ε)²`").

`IsMinEpsNet N C ε` says that `N` is an `ε`-net of `C` and no `ε`-net of `C` has fewer elements. -/
def IsMinEpsNet (N : Finset (S → A → A → ℝ)) (C : Set (S → A → A → ℝ)) (ε : ℝ) : Prop :=
  IsEpsNet N C ε ∧ ∀ N' : Finset (S → A → A → ℝ), IsEpsNet N' C ε → N.card ≤ N'.card

end LinearZeroSumMG


