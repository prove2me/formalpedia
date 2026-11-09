-- Prove2me | Definitions.Def_InflMaxAdapt_edgeExpInfluence
-- name    : InflMaxAdapt_edgeExpInfluence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:05.227148+00:00
-- url     : https://prove2.me/theorems/a594e033-6dd5-4e76-9695-63b94cad9eb3
-- title:
--   Expected influence in the undirected-edge representation
-- statement:
--   The expected influence $\mathbb E[\sigma(S)] = \sum_E \mathbb P(A = E)\,|C_E(S)|$ of a seed set $S$ when the live edges are drawn from independent bond percolation with edge probabilities $q$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6)

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeWeight
import Definitions.Def_InflMaxAdapt_edgeCascade

namespace InflMaxAdapt

/-- The expected influence `E[σ(S)]` of a seed set `S` in the undirected-edge representation
(Sections 1.1 and 2, printed pp.2, 5 = PDF pp.3, 6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)). -/
noncomputable def edgeExpInfluence {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ)
    (S : Finset V) : ℝ :=
  ∑ E : Finset (Sym2 V), edgeWeight q E * ((edgeCascade E S).card : ℝ)

end InflMaxAdapt


