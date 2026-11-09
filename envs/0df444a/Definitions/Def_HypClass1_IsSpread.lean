-- Prove2me | Definitions.Def_HypClass1_IsSpread
-- name    : HypClass1_IsSpread
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:28:48.516195+00:00
-- url     : https://prove2.me/theorems/4b081898-15ca-4512-9404-c0f4a2aa43f8
-- title:
--   $p$-spread measure on a family
-- statement:
--   Let $p \in [0,1]$ and $\mathcal B \subseteq 2^X$. A probability measure $\nu$ on $\mathcal B$ is **$p$-spread** if a random $B \in \mathcal B$ drawn from $\nu$ satisfies
--   $$
--   \mathbb P(S \subseteq B) \le p^{|S|} \qquad \text{for every } S \subseteq X.
--   $$
--
--   **Formalization Note** $\nu$ is a probability distribution on $2^X$ whose support lies in $\mathcal B$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.43

import Mathlib

namespace HypClass1

/-- **p-spread measure** on a family `B`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.43: "We say that a probability measure
ν : B → [0, 1] is p-spread if for p ∈ [0, 1], it holds that a random B ⊆ B chosen according to ν
satisfies P(S ⊆ B) ≤ p^{|S|} for every S ⊆ X."

**Formalization Note.** `ν` is a probability distribution on subsets of `X = α` supported on `B`
(every set of positive mass is in `B`), and `ν{A : S ⊆ A} ≤ p^{|S|}` for every `S ⊆ X`. -/
def IsSpread {α : Type*} (p : ℝ) (B : Finset (Finset α)) (ν : PMF (Finset α)) : Prop :=
  (∀ A, ν A ≠ 0 → A ∈ B) ∧ ∀ S : Finset α, (ν.toOuterMeasure {A | S ⊆ A}).toReal ≤ p ^ S.card

end HypClass1


