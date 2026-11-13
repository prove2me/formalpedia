-- Prove2me | Definitions.Def_MultiThinkCoT_IsConsistentOracle
-- name    : MultiThinkCoT_IsConsistentOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:58.822375+00:00
-- url     : https://prove2.me/theorems/88f75614-7f1b-46b3-a587-b5c040b870ed
-- title:
--   Prefix–next-token pairs and the Consistent oracle (Definition 1.1)
-- statement:
--   A CoT $z=f^{\mathrm{CoT}\text{-}T}(x)$ decomposes into the **prefix–next-token pairs**
--
--   $$
--   \big([x,z_1\dots z_j],\ z_{j+1}\big),\qquad j=0,\dots,|z|-1,
--   $$
--
--   each a string together with the token the generator appends to it.
--
--   A **Consistent oracle** for a base class $\mathcal F$ is an algorithm that, given a training set $S=\{(z^{(i)},f^\star(z^{(i)}))\}_{i\in[m]}$ of sequence and next-token pairs from a single generator $f^\star\in\mathcal F$, returns some $\hat f\in\mathcal F$ with $\hat f(z^{(i)})=f^\star(z^{(i)})$ for all $i$. The predicate here says that a function $O$ from lists of pairs to generators has this property: whenever some member of $\mathcal F$ fits every pair, $O$ returns a member of $\mathcal F$ that fits every pair.
--
--   Algorithm 1 calls the oracle on the prefix–next-token pairs of each homogeneous batch of CoTs; a generator fits all pairs of a CoT exactly when it reproduces that CoT.
--
--   **Formalization Note** Nothing is required of $O$ on lists that no member of $\mathcal F$ fits (Definition 1.1 only concerns training sets from a single generator in $\mathcal F$). The oracle's running time is not part of the predicate; Algorithm 1 charges it through a cost function.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §1.1, Definition 1.1, p.3 (PDF p.3); Algorithm 1 line 6, p.24

import Mathlib
import Definitions.Def_MultiThinkCoT_e2e

namespace MultiThinkCoT

/-!
# Prefix–next-token pairs and the Consistent oracle (Definition 1.1)

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers*,
arXiv:2604.24737 (held version, sha256 e663a640…), §1.1, Definition 1.1, p.3 (PDF p.3); the
prefix–next-token pairs of a CoT, Algorithm 1 line 6, p.24.

Given a training set `S = {(z(i), f⋆(z(i)))}` of sequence and next-token pairs from a single
generator `f⋆ ∈ F`, a Consistent oracle finds some `f̂ ∈ F` with `f̂(z(i)) = f⋆(z(i))` for all
`i`. A CoT `z` of an input `x` decomposes into the pairs `([x, z[1..j]], z[j+1])`, `j < |z|`.

**Formalization Note.**
* An oracle is a function from lists of pairs (string, next token) to generators.
* `IsConsistentOracle F O` is the specification on realizable input only: whenever some `f ∈ F`
  fits every pair, `O` returns a member of `F` that fits every pair. Nothing is required on
  non-realizable input (Definition 1.1 only speaks about training sets from a single
  `f⋆ ∈ F`). The running time of the oracle is not part of this predicate; Algorithm 1 charges it
  through a separate cost function (`MultiThinkCoT.alg1`).
-/

/-- The prefix–next-token pairs of the CoT `z` on input `x`: `([x, z[1..j]], z[j+1])` for
`j = 0, …, |z| − 1`. -/
def prefixPairs (x z : List Bool) : List (List Bool × Bool) :=
  (List.range z.length).map fun j => (x ++ z.take j, z.getD j false)

/-- Definition 1.1 (Consistent oracle), as a specification of `O`: on every list of pairs
realizable by some member of `F`, `O` returns a member of `F` consistent with all of them. -/
def IsConsistentOracle (F : Set Gen) (O : List (List Bool × Bool) → Gen) : Prop :=
  ∀ ps : List (List Bool × Bool), (∃ f ∈ F, ∀ p ∈ ps, f p.1 = p.2) →
    O ps ∈ F ∧ ∀ p ∈ ps, O ps p.1 = p.2

end MultiThinkCoT


