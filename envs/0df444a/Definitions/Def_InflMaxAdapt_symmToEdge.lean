-- Prove2me | Definitions.Def_InflMaxAdapt_symmToEdge
-- name    : InflMaxAdapt_symmToEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:21.609601+00:00
-- url     : https://prove2.me/theorems/a4b501e5-ed59-40c6-ad1f-56978222fb52
-- title:
--   Edge probabilities of an undirected instance
-- statement:
--   For an undirected instance, the probability vector is indexed by unordered pairs: the pair $\{u, v\}$ receives the probability $p_{u,v} = p_{v,u}$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6)

import Mathlib
import Definitions.Def_InflMaxAdapt_IsUndirected

namespace InflMaxAdapt

/-- The probability vector of an undirected instance indexed by unordered pairs `{u, v}`
(Section 2, printed p.5 = PDF p.6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5): "We therefore index p by unordered pairs"):
`s(u, v) ↦ p_{u,v} = p_{v,u}`. -/
noncomputable def symmToEdge {V : Type} (p : V → V → ℝ) (h : IsUndirected p) : Sym2 V → ℝ :=
  Sym2.lift ⟨p, h⟩

end InflMaxAdapt


