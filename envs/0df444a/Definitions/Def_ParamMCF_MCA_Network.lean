-- Prove2me | Definitions.Def_ParamMCF_MCA_Network
-- name    : ParamMCF_MCA_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:44.628096+00:00
-- url     : https://prove2.me/theorems/6d65e45b-705a-439b-becc-0c2a5ba93d65
-- title:
--   §2, p. 4 — finite directed network and its standing graph assumptions
-- statement:
--   A finite **directed network** has a vertex set $V$, an edge set $E$, and a tail and head in $V$ for each edge. The network assumptions are strong connectivity, absence of self loops, and absence of parallel directed edges.
--
--   This reusable network object supplies the underlying graph for the paper's minimum cost flow problem.
-- source:
--   Joachims, Klimm & Warode, Approximate Parametric Computation of Minimum-Cost Flows with Convex Costs, arXiv:2203.13146v1, p. 4, §2

import Mathlib

namespace ParamMCF.MCA

/-- A finite directed network represented by the tail and head of each edge. -/
structure Network (V E : Type*) where
  src : E → V
  tgt : E → V

/-- The standing network assumptions of §2: strong connectivity, no loops, no parallel edges. -/
def Network.IsAdmissible {V E : Type*} (G : Network V E) : Prop :=
  (∀ v w, Relation.ReflTransGen (fun a b => ∃ e, G.src e = a ∧ G.tgt e = b) v w) ∧
  (∀ e, G.src e ≠ G.tgt e) ∧
  Function.Injective (fun e => (G.src e, G.tgt e))

end ParamMCF.MCA


