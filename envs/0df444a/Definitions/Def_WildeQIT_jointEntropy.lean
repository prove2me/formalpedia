-- Prove2me | Definitions.Def_WildeQIT_jointEntropy
-- name    : WildeQIT_jointEntropy
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T05:15:38.40834+00:00
-- url     : https://prove2.me/theorems/3d1c6740-6f7d-4c6a-b661-6893f88aeede
-- title:
--   Joint entropy $H(X,Y)$ (Definition 10.3.1)
-- statement:
--   **Definition 10.3.1 (Joint entropy).** Let $X$ and $Y$ be discrete random variables with joint probability distribution $p_{XY}(x,y)$. The joint entropy $H(X,Y)$ is
--
--   $$
--   H(X,Y) \equiv \mathbb{E}_{XY}\{i(X,Y)\} = -\sum_{x,y} p_{XY}(x,y)\,\log\bigl(p_{XY}(x,y)\bigr),
--   $$
--
--   with the logarithm base $2$ and the convention $0\log 0=0$. In words: the joint entropy is the entropy of the pair $(X,Y)$ regarded as a single random variable on the product alphabet.
--
--   **Formalization Note.** `WildeQIT.jointEntropy p` is an abbreviation for `WildeQIT.entropy p` applied to the joint distribution `p : WildeQIT.FinDist (α × β)`; it exists so that statements can be written in the book's notation $H(X,Y)$. Being an `abbrev`, it unfolds to the entropy of the joint distribution definitionally.
-- source:
--   Wilde, Quantum Information Theory, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), Chapter 10 (Classical Information and Entropy), §Joint Entropy, Definition 10.3.1, LaTeX label eq-cie:joint-ent (book source roster-items.csv line 16481).

import Definitions.Def_WildeQIT_entropy

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 10.3.1 (Joint entropy):
`H(X,Y) ≡ -∑_{x,y} p_{XY}(x,y) log p_{XY}(x,y)`, i.e. the entropy of the joint distribution.
-/

namespace WildeQIT

/-- Definition 10.3.1. The joint entropy `H(X,Y)` of a pair with joint distribution `p` on
`α × β` is the entropy of `p` viewed as a distribution on the product alphabet:
`H(X,Y) = -∑_{x,y} p(x,y) log₂ p(x,y)`. -/
noncomputable abbrev jointEntropy {α β : Type} [Fintype α] [Fintype β] (p : FinDist (α × β)) : ℝ :=
  entropy p

end WildeQIT


