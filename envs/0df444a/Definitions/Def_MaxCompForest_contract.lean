-- Prove2me | Definitions.Def_MaxCompForest_contract
-- name    : MaxCompForest_contract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:36.08503+00:00
-- url     : https://prove2.me/theorems/b18b7702-e806-4d7e-82e9-b0dbfae6ecb7
-- title:
--   The loopless labelled quotient $G/S$
-- statement:
--   For a label set $S$, the quotient $H=G/S$ has as vertices the connected components of $(V,S)$, and as edges the original labels whose endpoints lie in distinct components. Each surviving label keeps its conductance; labels inside a component become loops and are dropped.
--
--   Parallel labels of the quotient remain distinct selectable objects, so $H$ is a loopless multigraph even when $G$ is simple. Degrees, Laplacian and normalized Laplacian of $H$ are computed in $H$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.17; p.1

import Mathlib
import Definitions.Def_MaxCompForest_spanSub
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} 

/-- The vertices of `G/S`: the components of `(V, S)`. -/
abbrev ContractV (G : WGraph V E) (S : Finset E) : Type _ := (spanSub G S).ConnectedComponent

/-- The labels of `G/S`: the original labels with endpoints in distinct components. -/
abbrev ContractE (G : WGraph V E) (S : Finset E) : Type _ :=
  {e : E // (spanSub G S).connectedComponentMk (G.head e) ≠
    (spanSub G S).connectedComponentMk (G.tail e)}

noncomputable instance [Finite V] (G : WGraph V E) (S : Finset E) : Fintype (ContractV G S) :=
  haveI : Finite (ContractV G S) := Quot.finite _
  Fintype.ofFinite _

noncomputable instance (G : WGraph V E) (S : Finset E) : DecidableEq (ContractV G S) :=
  Classical.decEq _

noncomputable instance [Finite E] (G : WGraph V E) (S : Finset E) : Fintype (ContractE G S) :=
  Fintype.ofFinite _

/-- **The quotient `H = G/S`**: contract the components of `(V, S)`, drop the resulting loops, and keep the
original label and the original conductance of every surviving edge.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.17: "contract it and drop the resulting loops, obtaining `H = G/S` while retaining the
original labels of surviving parallel edges".

**Formalization Note.** The result is a `WGraph`, loopless by construction and in general not simple.
Its degrees are the quotient's own (`deg (contract G S)`), not inherited. Every use has `S` a forest of a
connected graph. -/
def contract (G : WGraph V E) (S : Finset E) : WGraph (ContractV G S) (ContractE G S) where
  head e := (spanSub G S).connectedComponentMk (G.head e.1)
  tail e := (spanSub G S).connectedComponentMk (G.tail e.1)
  w e := G.w e.1
  head_ne_tail e := e.2
  w_pos e := G.w_pos e.1

end MaxCompForest


