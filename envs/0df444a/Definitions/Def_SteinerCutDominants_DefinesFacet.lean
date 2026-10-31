-- Prove2me | Definitions.Def_SteinerCutDominants_DefinesFacet
-- name    : SteinerCutDominants_DefinesFacet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:59.214347+00:00
-- url     : https://prove2.me/theorems/1903a089-2ce8-4882-83b0-94e766a56a6b
-- title:
--   The inequality $ax\ge b$ defines a facet of $\mathrm{CUT}_+(G,T)$
-- statement:
--   Let $a\in\mathbb R^{E(G)}$ and $b\in\mathbb R$. The inequality $ax\ge b$ **defines a facet** of $\mathrm{CUT}_+(G,T)$ if it is valid for $\mathrm{CUT}_+(G,T)$ and the face
--   $$
--   F=\{x\in\mathrm{CUT}_+(G,T) : ax=b\}
--   $$
--   is nonempty with $\dim F+1=\dim\mathrm{CUT}_+(G,T)$.
--
--   **Formalization Note** $\dim$ is the `finrank` of `vectorSpan`, compared additively, so that no natural-number subtraction occurs. Nonemptiness of $F$ is explicit because the `vectorSpan` of the empty set is $0$. The vector $a$ is not scaled here.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §2, p.4

import Mathlib
import Definitions.Def_SteinerCutDominants_cutDominant

open Matrix

namespace SteinerCutDominants

/-- The inequality `a x ≥ b` defines a facet of `CUT₊(G, T)` (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §2, p.4): it is valid, and the face
`F = {x ∈ CUT₊(G, T) : a x = b}` is nonempty of dimension one less than the dominant.

**Formalization Note** The real vector `a` is not yet scaled to minimum integer form. Dimensions
are `finrank` of `vectorSpan` compared as `dim F + 1 = dim P`, so no natural-number subtraction
occurs, and `F.Nonempty` rules out the empty set, whose `vectorSpan` is also `0`. -/
def DefinesFacet {V : Type} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (T : Finset V) (a : G.edgeSet → ℝ) (b : ℝ) : Prop :=
  (∀ y ∈ cutDominant G T, b ≤ a ⬝ᵥ y) ∧
    {x ∈ cutDominant G T | a ⬝ᵥ x = b}.Nonempty ∧
    Module.finrank ℝ (vectorSpan ℝ {x ∈ cutDominant G T | a ⬝ᵥ x = b}) + 1 =
      Module.finrank ℝ (vectorSpan ℝ (cutDominant G T))

end SteinerCutDominants


