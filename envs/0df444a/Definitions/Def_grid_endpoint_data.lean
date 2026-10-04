-- Prove2me | Definitions.Def_grid_endpoint_data
-- name    : grid_endpoint_data
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T02:19:00.644045+00:00
-- url     : https://prove2.me/theorems/8ad60952-263a-4d45-be8c-fc8480a4e512
-- title:
--   Graph-owned endpoint and prism-census data
-- statement:
--   This definition packages endpoint census data attached to one strongly regular graph. Its fields connect the two-cross-triangle endpoint, the trace-defect budget, the actual counts of prism-degree 8, 9, 10, and 12 triangles, and the zero-defect vertices to graph-derived sets in that same graph. It also records the seven-triangle incidence and per-triangle ordinary-point caps used in the support bound.
-- source:
--   GridEndpoint.lean at integration commit a45708acebe3f397faccb1b646be906f24f23ee5, Conway99Formal.GridEndpoint.EndpointData; definitions trianglesOf, crossCount, prismDegree, twoCrossPairs, and twoCrossCount in the same file.

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.GridEndpoint

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def trianglesOf (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  G.cliqueFinset 3

def crossCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (T U : Finset V) : ℕ :=
  ((T ×ˢ U).filter fun p => G.Adj p.1 p.2).card

def prismDegree (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : ℕ :=
  ((trianglesOf G).filter fun U => Disjoint T U ∧ crossCount G T U = 3).card

def twoCrossPairs (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset (Finset V)) :=
  ((trianglesOf G).powersetCard 2).filter fun s =>
    ∀ T ∈ s, ∀ U ∈ s, T ≠ U → Disjoint T U ∧ crossCount G T U = 2

def twoCrossCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (twoCrossPairs G).card

structure EndpointData (G : SimpleGraph V) [DecidableRel G.Adj] where
  srg : G.IsSRGWith 99 14 1 2
  at_endpoint : twoCrossCount G = 858
  traceDefect : V → ℕ
  trace_budget : (∑ u : V, traceDefect u) = 66
  n8 : ℕ
  n9 : ℕ
  n10 : ℕ
  n12 : ℕ
  ordinary : ℕ
  n8_correct : n8 = ((trianglesOf G).filter fun T => prismDegree G T = 8).card
  n9_correct : n9 = ((trianglesOf G).filter fun T => prismDegree G T = 9).card
  n10_correct : n10 = ((trianglesOf G).filter fun T => prismDegree G T = 10).card
  n12_correct : n12 = ((trianglesOf G).filter fun T => prismDegree G T = 12).card
  ordinary_correct : ordinary = (Finset.univ.filter fun u => traceDefect u = 0).card
  triangle_count : n8 + n9 + n10 + n12 = 231
  prism_sum : 8 * n8 + 9 * n9 + 10 * n10 + 12 * n12 = 2200
  ordinary_seven : ∀ u, traceDefect u = 0 →
    ((trianglesOf G).filter fun T => u ∈ T).card = 7
  triangle_ordinary_cap : ∀ T ∈ trianglesOf G,
    (T ∩ (Finset.univ.filter fun u => traceDefect u = 0)).card ≤
      if prismDegree G T = 10 then 2 else if prismDegree G T = 12 then 3 else 0

end Conway99Formal.GridEndpoint


