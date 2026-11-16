-- Prove2me | Definitions.Def_RelativisticZK205_ThreeCol_Supplement_Hamiltonian
-- name    : RelativisticZK205_ThreeCol_Supplement_Hamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:29:57.115833+00:00
-- url     : https://prove2.me/theorems/e3e68f9f-7639-478c-859f-2c21f6ad83ed
-- title:
--   Hamiltonian witnesses and finite Γ_LHV messages
-- statement:
--   Let $G$ be a finite simple undirected graph on $V=\{0,\ldots,n-1\}$. A cycle payload $K$ is the edge set of a spanning simple cycle, with each undirected edge represented by its smaller endpoint first. A witness $C$ additionally has every edge in $G$. Rotation and reversal carry no additional message data. Relabelling applies a vertex permutation to the edge set. Cycle masks are indexed only by the edges being opened, and serialization orders those edges lexicographically.
--
--   For a natural security parameter $k$, the protocol uses
--   $$\ell=\left\lceil\log_2\left(64\,n!\,2^{3k}\right)\right\rceil.$$
--   Words have $\ell$ Boolean coordinates. The commitment matrices use all $n^2$ ordered positions, including the diagonal. The commitment is $Y_{ij,t}=(D_{ij}\wedge X_{ij,t})\oplus A_{ij,t}$. Bob's finite reply alphabet distinguishes the full permutation/adjacency/mask unveiling from a cycle and its restricted masks. Each input and reply has a separate malformed/abort branch.
--
--   These definitions specify the graph witnesses and wire formats shared by both executions. The Hamiltonian-cycle predicate is Mathlib's genuine spanning simple cycle predicate; no independent lower bound on $n$ is imposed.
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.12, §5.2, Protocol Γ_LHV and simulators; p.13, proof of Theorem 2

import Mathlib

namespace RelativisticZK205.ThreeCol.Supplement

abbrev Vertex (n : ℕ) := Fin n
abbrev Position (n : ℕ) := Vertex n × Vertex n
abbrev EdgeSet (n : ℕ) := Finset (Position n)

/-- One representative of an undirected edge, with smaller endpoint first. -/
def canonicalEdge {n : ℕ} (e : Position n) : Position n :=
  if e.1 ≤ e.2 then e else (e.2, e.1)

/-- The edge-set encoding of a genuine spanning simple cycle. Rotations and reversal
carry no extra transmitted information. Mathlib's IsHamiltonianCycle excludes lengths 0,1,2. -/
def IsCycleSet {n : ℕ} (K : EdgeSet n) : Prop :=
  ∃ (v : Vertex n) (w : (⊤ : SimpleGraph (Vertex n)).Walk v v),
    w.IsHamiltonianCycle ∧
      K = ((w.support.zip w.support.tail).map canonicalEdge).toFinset

def IsWitness {n : ℕ} (G : SimpleGraph (Vertex n)) (C : EdgeSet n) : Prop :=
  IsCycleSet C ∧ ∀ e ∈ C, G.Adj e.1 e.2

noncomputable def allCycles (n : ℕ) : Finset (EdgeSet n) := by
  classical
  exact Finset.univ.filter IsCycleSet

noncomputable def relabelCycle {n : ℕ} (p : Equiv.Perm (Vertex n)) (C : EdgeSet n) : EdgeSet n := by
  classical
  exact C.image (fun e => canonicalEdge (p e.1, p e.2))

/-- Exact lexicographic wire order; each cycle edge and each opening occurs once. -/
noncomputable def orderedEdges {n : ℕ} (C : EdgeSet n) : List (Position n) :=
  C.toList.mergeSort (fun e f => e.1.val * n + e.2.val ≤ f.1.val * n + f.2.val)

/-- Protocol Γ_LHV, p.12: multiplication, not exponentiation of the factorial. -/
def bitLength (n k : ℕ) : ℕ := Nat.clog 2 (64 * Nat.factorial n * 2 ^ (3 * k))

/-- Additive F_(2^ℓ) coordinates in any F₂ basis. Only addition and multiplication
by a Boolean occur in this protocol, so no field multiplication is discarded. -/
abbrev Word (ℓ : ℕ) := Fin ℓ → Bool
abbrev MatrixBits (n ℓ : ℕ) := Position n → Word ℓ
abbrev BooleanMatrix (n : ℕ) := Position n → Bool
abbrev BoxIndex (n ℓ : ℕ) := Position n × Fin ℓ

noncomputable def adjacency {n : ℕ} (G : SimpleGraph (Vertex n))
    (p : Equiv.Perm (Vertex n)) : BooleanMatrix n := fun e =>
  @decide (G.Adj (p.symm e.1) (p.symm e.2)) (Classical.propDecidable _)

def commit {n ℓ : ℕ} (D : BooleanMatrix n) (X A : MatrixBits n ℓ) : MatrixBits n ℓ :=
  fun e t => xor (D e && X e t) (A e t)

inductive Opening (n ℓ : ℕ) where
  | graph : Equiv.Perm (Vertex n) → BooleanMatrix n → MatrixBits n ℓ → Opening n ℓ
  | cycle : (K : EdgeSet n) → (K → Word ℓ) → Opening n ℓ
  deriving Fintype

/-- none is a malformed input or a local abort, independently on each side. -/
abbrev AliceQuery (n ℓ : ℕ) := Option (MatrixBits n ℓ)
abbrev BobQuery := Option Bool
abbrev AliceReply (n ℓ : ℕ) := Option (MatrixBits n ℓ)
abbrev BobReply (n ℓ : ℕ) := Option (Opening n ℓ)

noncomputable def cycleOpening {n ℓ : ℕ} (C : EdgeSet n) (A : MatrixBits n ℓ) : Opening n ℓ :=
  .cycle C (fun i => A i.1)

/-- Canonical finite dependent payload serialized in lexicographic order. -/
noncomputable def cycleSerialization {n ℓ : ℕ} (C : EdgeSet n) (A : C → Word ℓ) :
    List (Position n × Word ℓ) :=
  (C.attach.toList.mergeSort (fun i j =>
    i.1.1.val * n + i.1.2.val ≤ j.1.1.val * n + j.1.2.val)).map (fun i => (i.1, A i))

end RelativisticZK205.ThreeCol.Supplement


