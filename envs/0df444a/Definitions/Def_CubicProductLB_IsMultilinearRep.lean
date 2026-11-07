-- Prove2me | Definitions.Def_CubicProductLB_IsMultilinearRep
-- name    : CubicProductLB_IsMultilinearRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:09.055685+00:00
-- url     : https://prove2.me/theorems/c9cd3e06-47a3-46b7-a04e-7d02325858e4
-- title:
--   The multilinear coefficients of a Boolean function over $\mathbb F_2$
-- statement:
--   The family $c = (c(S))_{S \subseteq [M]}$ of elements of $\mathbb F_2$ is the coefficient family of the **multilinear representative** of $g : \{0,1\}^M \to \mathbb F_2$ if
--   $$g(y) = \sum_{S \subseteq [M]} c(S) \prod_{j \in S} y_j \quad \text{for every } y.$$
--   The value $c([M])$ is the **full multilinear coefficient** of $g$.
--
--   **Formalization Note** The relation is stated as a predicate. Each $g$ has exactly one such $c$, which is proved in the mission's sanity checks, so statements quantifying over all $c$ with this property speak about the unique representative of the page. The full coefficient is deliberately not defined as the parity of the values of $g$, since that identity is a step of a proof.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Eqs. (260)–(261), p.31

import Mathlib

namespace CubicProductLB

/-- `c` is the coefficient family of the multilinear representative of `g` over `F_2`:
`g(y) = ∑_{S ⊆ [M]} c(S) ∏_{j ∈ S} y_j` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (260), p.31). The full multilinear coefficient
(261) is `c Finset.univ`.

**Formalization Note** Such a `c` exists and is unique (the sanity file proves `∃!`), so statements
of the form `∀ c, IsMultilinearRep g c → …` are about the page's `ĝ`. -/
def IsMultilinearRep {M : ℕ} (g : (Fin M → Bool) → ZMod 2) (c : Finset (Fin M) → ZMod 2) : Prop :=
  ∀ y, g y = ∑ S : Finset (Fin M), c S * ∏ j ∈ S, (if y j then 1 else 0)

end CubicProductLB


