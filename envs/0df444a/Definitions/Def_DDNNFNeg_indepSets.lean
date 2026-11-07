-- Prove2me | Definitions.Def_DDNNFNeg_indepSets
-- name    : DDNNFNeg_indepSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:05.820012+00:00
-- url     : https://prove2.me/theorems/7372dcb2-6841-4f71-a1d9-0c3200c8e5d8
-- title:
--   Indicator vectors of independent sets of $G$
-- statement:
--   $I \subseteq \{0,1\}^n$ is the set of indicator vectors of independent sets of $G$: the assignments $x$ such that no edge of $G$ has both endpoints set to $1$.
--
--   "$X$ is the indicator vector of a uniformly random independent set in $G$" is the uniform distribution on $I$.
--
--   **Formalization Note** Every probability of §5.2 is then a ratio of cardinalities, as in the proof of Theorem 5.3 ($\mathbb P[X \in R] = |R \cap I| / |I|$).
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §5.2, p.13; proof of Theorem 5.3, p.15

import Mathlib

namespace DDNNFNeg

/-- The set `I ⊆ {0,1}^n` of indicator vectors of independent sets of `G`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §5.2, pp.12–13 and proof of Theorem 5.3, p.15): the assignments `x` such that no edge
of `G` has both endpoints set to `1`.

**Formalization Note** "`X` is the indicator vector of a uniformly random independent set in
`G`" is the uniform distribution on this finite set; every probability of §5.2 is then a ratio
of cardinalities, as the paper itself writes in the proof of Theorem 5.3
(`P[X ∈ R] = |R ∩ I| / |I|`). -/
def indepSets {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => ∀ u v, G.Adj u v → ¬ (x u = true ∧ x v = true))

end DDNNFNeg


