-- Prove2me | Definitions.Def_CircTrichotomy_BoundedDefinable
-- name    : CircTrichotomy_BoundedDefinable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:43.159375+00:00
-- url     : https://prove2.me/theorems/0bbd3fb5-e60c-4e3b-ad94-5574ff9be55b
-- title:
--   Bounded $\tau$-definable quantifiers $\mathcal B_\tau$
-- statement:
--   For $k,t\ge1$, a $k$-ary numerical Lindström quantifier $Q$ is **$t$-bounded and $\tau$-definable** if there is a quantifier-free formula $\varphi(x_0,\dots,x_{k-1})$ over $\tau$ such that for every length $n\ge1$
--   $$Q^n=\Bigl\{\textstyle\prod_{i<k}P_i : P_i\subseteq[0,n-1],\ |P_i|<t\ \text{for all } i,\ \prod_{i<k}P_i\subseteq\varphi^n\Bigr\}.$$
--   $\mathcal B_\tau$ is the class of such quantifiers. $\mathcal B_{[<,+\omega]}$ uses the vocabulary of the order and the successor relations.
--
--   Example: $\exists^{<t}x$ is $t$-bounded and definable by $\top$.
--
--   **Formalization Note** The sets $P_i$ may be empty, as in (68).
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.16, pp.27–28

import Mathlib
import Definitions.Def_CircTrichotomy_QFForm

set_option autoImplicit false

namespace CircTrichotomy

/-- **`B_τ`: bounded numerical Lindström quantifiers that are τ-definable** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.16,
pp.27–28): "Let k, t ∈ ℕ>0. A k-ary numerical Lindström quantifier Q over words is t-bounded if for
every length n ∈ ℕ>0 and every relation R ∈ Qⁿ, there exist subsets P^R_0, …, P^R_{k−1} ⊆ [0, n − 1],
satisfying R = P^R_0 × … × P^R_{k−1} and |P^R_i| < t for each i ∈ [0, k − 1]. … The t-bounded
numerical quantifier Q is τ-definable if there exists a quantifier-free formula φ(x₀, …, x_{k−1})
over the vocabulary τ such that
Qⁿ = { ∏_{i=0}^{k−1} P_i : P_i ⊆ [0, n − 1], |P_i| < t for all i ∈ [0, k − 1],
       ∏_{i=0}^{k−1} P_i ⊆ φⁿ }.   (68)
The class of bounded numerical Lindström quantifiers that are τ-definable is denoted by B_τ."

`BoundedDefinable Rs k` is the set of `k`-ary members of `B_τ` for the vocabulary `τ = Rs`: `k ≥ 1` and
for some `t ≥ 1` and quantifier-free `φ` over `Rs`, for every `n ≥ 1`, `Q n` is exactly the set of
products `P₀ × ⋯ × P_{k−1}` of subsets of `[0, n − 1]` with `|P_i| < t` all of whose tuples satisfy
`φ`. Such a `Q` is `t`-bounded.

**Formalization Note** The sets `P_i` may be empty, as in (68). The value `Q 0` is not
constrained (words are non-empty). -/
def BoundedDefinable (Rs : Set (Σ r : ℕ, (Fin r → ℕ) → Prop)) (k : ℕ) :
    Set (ℕ → Set (Set (Fin k → ℕ))) :=
  {Q | 0 < k ∧ ∃ t : ℕ, 0 < t ∧ ∃ φ : QFForm k, φ.InVocab Rs ∧ ∀ n : ℕ, 0 < n →
    Q n = {R | ∃ P : Fin k → Finset ℕ, (∀ i, (P i).card < t ∧ ∀ p ∈ P i, p < n) ∧
      (∀ a : Fin k → ℕ, (∀ i, a i ∈ P i) → φ.Sat a) ∧ R = {a | ∀ i, a i ∈ P i}}}

/-- The vocabulary `<, +ω` of the quantifiers `B_{[<,+ω]}` (Theorem 2.8 (8), p.6): the order
`x₀ < x₁` and the successor relations `x₀ + j = x₁`, `j ∈ ℕ` (§A.5, p.19). -/
def ordRels : Set (Σ r : ℕ, (Fin r → ℕ) → Prop) :=
  {⟨2, fun a => a 0 < a 1⟩} ∪ {R | ∃ j : ℕ, R = ⟨2, fun a => a 0 + j = a 1⟩}

end CircTrichotomy


