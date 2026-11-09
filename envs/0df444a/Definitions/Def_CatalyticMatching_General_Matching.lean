-- Prove2me | Definitions.Def_CatalyticMatching_General_Matching
-- name    : CatalyticMatching_General_Matching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:05.230242+00:00
-- url     : https://prove2.me/theorems/ef24720f-4103-4da1-b67e-2edb557688c7
-- title:
--   Finite ordinary matchings, maximum cardinality, and graph deficiency
-- statement:
--   Let $G$ be a finite simple undirected graph. An ordinary matching is an edge subset with at most one incident selected edge at each vertex. The maximum matching cardinality and the graph deficiency set are
--
--   $$\nu(G)=\max\{|M|:M\text{ is a matching in }G\},\qquad D(G)=\{v:\text{some maximum matching misses }v\}.$$
--
--   The finite family includes the empty matching, including for empty graphs. Perfectness uses the referenced published predicate rather than a second definition. These definitions provide the common combinatorial interface for the goal and the Tutte results.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, §2 p.8

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_Algorithm

namespace CatalyticMatching.General

/-- Ordinary matchings, §2 p.8. Edges already belong to G. -/
def IsMatching {n : ℕ} {G : SimpleGraph (Fin n)} (M : Finset G.edgeSet) : Prop :=
  ∀ v : Fin n, ∀ e ∈ M, ∀ f ∈ M,
    v ∈ (e : Sym2 (Fin n)) → v ∈ (f : Sym2 (Fin n)) → e = f

/-- The maximum over the finite family containing the empty matching. -/
noncomputable def matchingNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun M : Finset G.edgeSet => IsMatching M)).sup Finset.card

/-- Vertices missed by at least one maximum matching, §2 p.8. -/
def graphDeficiency {n : ℕ} (G : SimpleGraph (Fin n)) : Set (Fin n) :=
  {v | ∃ M : Finset G.edgeSet, IsMatching M ∧ M.card = matchingNumber G ∧
    ∀ e ∈ M, v ∉ (e : Sym2 (Fin n))}

end CatalyticMatching.General


