-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_Supplement_tseitin
-- name    : UnaryParityLifting_Exact_Supplement_tseitin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:47:41.284054+00:00
-- url     : https://prove2.me/theorems/5c16362e-da4b-4a4a-8370-da34117325df
-- title:
--   Graph Tseitin clauses and edge expansion
-- statement:
--   For a finite simple graph G, edge variables are indexed by ordered endpoint pairs u<v with G(u,v); this lists each undirected edge exactly once. At a vertex v, each assignment to its incident edges violating the parity charge χ_v contributes the clause excluding that assignment. Consequently a degree-three vertex contributes four width-three clauses.
--
--   $$\bigoplus_{e\ni v}x_e=\chi_v,\qquad \sum_v\chi_v=1\ \text{in }\mathbb F_2.$$
--
--   Cubic means every vertex has three incident edges. Expansion ε means at least ε|U| crossing edges for every nonempty vertex set with 2|U|≤|V|. Connectedness uses Mathlib's graph predicate. The CNF is renamed bijectively to Fin of its actual edge count. The definitions do not assert existence of an expander family or any proof-size bound: those are conclusions of incomparability. That theorem uses 2(n+2) vertices, an unbounded admissible even-size indexing.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), p.20, proof of Corollary 6.3

import Definitions.Def_UnaryParityLifting_Exact_Supplement_encoding

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- A finite simple undirected graph, with edge names explicitly enumerated. -/
abbrev EdgeName {v : ℕ} (G : SimpleGraph (Fin v)) :=
  {e : Fin v × Fin v // e.1 < e.2 ∧ G.Adj e.1 e.2}
def incident {v : ℕ} {G : SimpleGraph (Fin v)} (e : EdgeName G) (u : Fin v) : Prop :=
  e.val.1 = u ∨ e.val.2 = u
def incidentEdges {v : ℕ} (G : SimpleGraph (Fin v)) (u : Fin v) : Finset (EdgeName G) :=
  Finset.univ.filter (fun e => incident e u)
def cubic {v : ℕ} (G : SimpleGraph (Fin v)) : Prop :=
  ∀ u, (incidentEdges G u).card = 3
/-- Edge expansion, with one fixed positive constant across a family. -/
def Expands {v : ℕ} (G : SimpleGraph (Fin v)) (ε : ℝ) : Prop :=
  ∀ U : Finset (Fin v), U.Nonempty → 2 * U.card ≤ v →
    ε * U.card ≤ ((Finset.univ.filter (fun e : EdgeName G =>
      (e.val.1 ∈ U ∧ e.val.2 ∉ U) ∨ (e.val.2 ∈ U ∧ e.val.1 ∉ U))).card : ℝ)
/-- One clause per violating local assignment, four at a cubic vertex. -/
def tseitinRaw {v : ℕ} (G : SimpleGraph (Fin v)) (χ : Fin v → ZMod 2) :
    LiftSAParity.CNF (EdgeName G) :=
  Finset.univ.biUnion fun u : Fin v =>
    (Finset.univ.filter (fun x : EdgeName G → Bool =>
      (∑ e ∈ incidentEdges G u, fieldBit (x e)) ≠ χ u)).image
        (fun x => (incidentEdges G u).image (fun e => (e, !x e)))
def edgeCount {v : ℕ} (G : SimpleGraph (Fin v)) := Fintype.card (EdgeName G)
def tseitin {v : ℕ} (G : SimpleGraph (Fin v)) (χ : Fin v → ZMod 2) :
    LiftSAParity.CNF (Fin (edgeCount G)) :=
  (tseitinRaw G χ).image (fun C => C.image (fun l => ((Fintype.equivFin (EdgeName G)) l.1,l.2)))

end UnaryParityLifting.Exact.Supplement


