-- Prove2me | Definitions.Def_MWCSherali_encMWC
-- name    : MWCSherali_encMWC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:24.754362+00:00
-- url     : https://prove2.me/theorems/571de107-6b5b-4eff-8361-6309e840019e
-- title:
--   Unary encoding of a Multiway Cut instance
-- statement:
--   A Multiway Cut instance is written as a string over the two-letter alphabet $\{\mathtt 1,\mathtt{sep}\}$ of the published module `OptInapprox.MaxCut`: first $n$ and $k$ in unary (each followed by a separator), then the $k$ terminal indices in unary, then both endpoints of every listed edge in unary.
--
--   The encoding is the input format of the gap problems (polynomial-time reductions output these strings). Its length is polynomial in the number of vertices and the total weight, and it is injective.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §1, p.2 (input of the Multiway Cut problem)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_MWCSherali_MWCInst

namespace MWCSherali

open OptInapprox.MaxCut

/-- **Encoding of a Multiway Cut instance.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511
(version of Nov. 3, 2026), §1, p.2 (the input of the Multiway Cut problem).

The instance is written over the two-letter alphabet `MCSym = {one, sep}` of the reused module
`OptInapprox.MaxCut`: the number of vertices `n` and `k` in unary (each terminated by a separator), then the `k`
terminal indices in unary, then both endpoints of every listed edge in unary (the edge part of
`OptInapprox.MaxCut.encMaxCut`; the terminals must precede the edge list for the string to be
decodable).

**Formalization Note.** The encoding is unary, so its length is polynomial in the number of
vertices and in the total (multigraph) weight; it is injective (checked in the verification
file). -/
def encMWC (G : MWCInst) : List MCSym :=
  MCSym.unary G.graph.n ++ MCSym.unary G.k ++
    (List.finRange G.k).flatMap (fun i => MCSym.unary (G.term i : ℕ)) ++
    G.graph.edges.flatMap fun e => MCSym.unary (e.1 : ℕ) ++ MCSym.unary (e.2 : ℕ)

end MWCSherali


