-- Prove2me | Definitions.Def_DistributedMIS_LocalLowerBound_FiniteBlowup
-- name    : DistributedMIS_LocalLowerBound_FiniteBlowup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:08.954045+00:00
-- url     : https://prove2.me/theorems/8cc29003-ded5-4135-8775-1a9b0a8e220c
-- title:
--   Padded random graph, legal executions and graph bad events
-- statement:
--   Given an N-vertex skeleton, form k-cliques and use the independent fair matrices for cross-clique adjacency. Adjoin n-kN isolated vertices. A legal identifier assignment is a bijection of this padded carrier to [n]. The legal repaired execution uses that assignment, its sorted ports and the independent identifier-indexed infinite tape table.
--
--   $$\gamma_{EXT}=(k+1)^D e^{-k2^{-D}},\qquad
--   \beta_{ADV}=2n e^{-k/(4D)}.$$
--
--   External domination means that one may choose at most one vertex from each neighboring clique and dominate the entire chosen clique. The degree-advice bad event is the failure of Δ≤kD≤2Δ for the actual padded graph. Its numerical bound is proof support for the information clause after Theorem 1.1; it is not asserted as an assumption of the graph model.
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Proposition 3.1, pp. 9–10; Appendix A.2–A.4, pp. 33–34; Theorem 1.1 information clause and footnote 1, p. 3 (printed = PDF); degree-advice tail calculation recorded in MODERATION_NOTES.md

import Definitions.Def_DistributedMIS_LocalLowerBound_Simulation

noncomputable section

namespace DistributedMIS.LocalLowerBound

abbrev PaddedVertices (n N k : ℕ) := (Fin N × Fin k) ⊕ Fin (n-k*N)

def finiteNeighbors {N : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N) : List (Fin N) := by
  classical
  exact (H.neighborFinset v).toList

def paddedNeighbors {n N k : ℕ} (H : SimpleGraph (Fin N)) (ω : Matrices k) :
    PaddedVertices n N k → List (PaddedVertices n N k)
  | .inl x => (cliqueNeighbors (finiteNeighbors H) Fin.val ω x).map Sum.inl
  | .inr _ => []

/-- Symmetrization makes the graph a SimpleGraph on every input.
For distinct skeleton labels its two directed tests are the same matrix bit. -/
def paddedGraph {n N k : ℕ} (H : SimpleGraph (Fin N)) (ω : Matrices k) :
    SimpleGraph (PaddedVertices n N k) where
  Adj x y := x ≠ y ∧ (y ∈ paddedNeighbors H ω x ∨ x ∈ paddedNeighbors H ω y)
  symm := ⟨by intro x y h; exact ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def legalExecution {n N k : ℕ} (P : LocalProgram) (advice T : ℕ)
    (H : SimpleGraph (Fin N)) (ω : Matrices k)
    (I : PaddedVertices n N k ≃ Fin n) (W : Fin n → PrivateTape) :
    PaddedVertices n N k → Bool :=
  localOutput P n advice T
    (sortedPorts (paddedNeighbors H ω) (fun x => (I x).val + 1))
    (fun x => (I x).val + 1) (fun x => W (I x))

def legalRepaired {n N k : ℕ} (P : LocalProgram) (advice T : ℕ)
    (H : SimpleGraph (Fin N)) (ω : Matrices k)
    (I : PaddedVertices n N k ≃ Fin n) (W : Fin n → PrivateTape)
    (x : PaddedVertices n N k) : Bool :=
  legalExecution P advice T H ω I W x &&
    (paddedNeighbors H ω x).all (fun y => !(legalExecution P advice T H ω I W y))

def ExternalDomination {N k : ℕ} (H : SimpleGraph (Fin N)) (v : Fin N)
    (ω : Matrices k) : Prop :=
  ∃ choice : Fin N → Option (Fin k), ∀ a : Fin k,
    ∃ u b, H.Adj v u ∧ choice u = some b ∧ edgeBit ω v.val u.val a b = true

def finiteOccupancy {N : ℕ} (k : ℕ) (P : LocalProgram) (n advice T : ℕ)
    (H : SimpleGraph (Fin N)) (W : Fin n → PrivateTape) (v : Fin N) : ℝ :=
  matrixProbability {ω : Matrices k | simulatedChoice P n advice T W (finiteNeighbors H) Fin.val ω v ≠ none}

/-- Exact graph-level bad event for the fixed advice kD, independent of tapes. -/
def DegreeAdviceBad {n N k : ℕ} (D : ℕ) (H : SimpleGraph (Fin N))
    (ω : Matrices k) : Prop :=
  ¬ ( (by classical exact
    (Finset.univ.image (fun x : PaddedVertices n N k => (paddedGraph H ω).degree x)).sup id) ≤ k*D ∧
    k*D ≤ 2 * (by classical exact
    (Finset.univ.image (fun x : PaddedVertices n N k => (paddedGraph H ω).degree x)).sup id))

def degreeAdviceError (n D k : ℕ) : ℝ :=
  2 * n * Real.exp (-(k : ℝ) / (4 * D))

end DistributedMIS.LocalLowerBound


