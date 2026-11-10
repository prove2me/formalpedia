-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_Incompatibility
-- name    : SmoothedPlanted_FFK_Incompatibility
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:32:31.221012+00:00
-- url     : https://prove2.me/theorems/a68c6a75-6976-4fd5-8420-b6dbf53fe5d0
-- title:
--   Definition 31 — literal incompatibility graphs
-- statement:
--   The vertices are pairs $(i,a)$ of a variable and an alphabet symbol. The graph $H$ contains edges between distinct symbols of the same variable, and between different variables whose symbols violate the pair constraint. The graph $H'$ contains only the second kind. Both are simple undirected graphs. The literal set of an assignment contains $(i,\sigma_i)$ for every $i\in S$. Its spanned-edge count uses unordered graph edges, including no loops.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Definition 31 — literal incompatibility graphs, printed p. 23 (PDF p. 25), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_CSP

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

def incompatibility {V : Type} [LinearOrder V] {q : ℕ} (Y : CSP V q) :
    SimpleGraph (V × Fin q) := SimpleGraph.fromRel (fun x y =>
      (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
      (x.1 ≠ y.1 ∧ allows Y x.1 y.1 x.2 y.2 = false))
def incompatibilityPrime {V : Type} [LinearOrder V] {q : ℕ} (Y : CSP V q) :
    SimpleGraph (V × Fin q) := SimpleGraph.fromRel (fun x y =>
      x.1 ≠ y.1 ∧ allows Y x.1 y.1 x.2 y.2 = false)
def literalSet {V : Type} [Fintype V] [LinearOrder V] {q : ℕ}
    (S : Finset V) (σ : S → Fin q) : Finset (V × Fin q) := by
  classical
  exact Finset.univ.image (fun i : S => (i.val, σ i))
def spannedEdges {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) : ℕ := by
  classical
  exact (G.edgeFinset.filter (fun e => e ∈ T.sym2)).card

end SmoothedPlanted.FFK


