-- Prove2me | Definitions.Def_IncrementalER_Supplement_theorem61Spec
-- name    : IncrementalER_Supplement_theorem61Spec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:50:43.169067+00:00
-- url     : https://prove2.me/theorems/59b9b2f2-9c01-4b9a-aeb0-7341ecbe851b
-- title:
--   Dynamic vertex-sparsifier and batch-update interface (Theorem 6.1)
-- statement:
--   This definition gives the full dynamic state and output semantics of Theorem 6.1. Stable edge identifiers preserve multigraph multiplicity. Batches may insert or delete vertices and edges and insert protected terminals; every elementary change counts toward the update budget, and a protected terminal cannot be deleted.
--
--   At each completed batch the machine outputs a terminal set and a positive-capacity multigraph. The specification includes active-set connectivity, the effective-resistance-growth hypothesis, the two Loewner inequalities for the Schur complement, expected output size, output capacity ratio, high-probability correctness against an oblivious sequence, and expected total vertex/edge recourse and work including initialization.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 6.1, p.37

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem21Spec

set_option autoImplicit false

open MeasureTheory Matrix

namespace IncrementalER.Supplement

/-!
# Dynamic vertex-sparsifier interface for Theorem 6.1

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, STOC 2027 submission
(manuscript sha256 a0415fd5…), Theorem 6.1, p.37.
-/

/-- A dynamic snapshot uses stable natural edge identifiers, so parallel equal-capacity edges remain
distinct and edge deletion names one occurrence. -/
structure DynSnapshot (n : ℕ) where
  active : Finset (Fin n)
  edges : List (ℕ × IncrementalER.Edge n)
  terminals : Finset (Fin n)

/-- The five elementary updates named in Theorem 6.1. -/
inductive DynUpdate (n : ℕ) where
  | insertVertex (v : Fin n)
  | deleteVertex (v : Fin n)
  | insertEdge (id : ℕ) (e : IncrementalER.Edge n)
  | deleteEdge (id : ℕ)
  | insertTerminal (v : Fin n)

/-- Initial snapshot, with edge identifiers `0,…,m₀-1`. -/
def initialSnapshot {n : ℕ} (V₀ S : Finset (Fin n))
    (es : List (IncrementalER.Edge n)) : DynSnapshot n :=
  ⟨V₀, (List.range es.length).zip es, S⟩

/-- Legality of one elementary change: vertices and identifiers have the expected current status,
inserted edges have positive capacity and active endpoints, a deleted vertex is isolated, and no
protected terminal is deleted. -/
def LegalUpdate {n : ℕ} (s : DynSnapshot n) : DynUpdate n → Prop
  | .insertVertex v => v ∉ s.active
  | .deleteVertex v => v ∈ s.active ∧ v ∉ s.terminals ∧
      ∀ ie ∈ s.edges, ie.2.u ≠ v ∧ ie.2.v ≠ v
  | .insertEdge id e => (∀ ie ∈ s.edges, ie.1 ≠ id) ∧
      e.u ∈ s.active ∧ e.v ∈ s.active ∧ 0 < e.c
  | .deleteEdge id => ∃ ie ∈ s.edges, ie.1 = id
  | .insertTerminal v => v ∈ s.active

/-- Apply one legal or illegal update; theorem hypotheses separately require legality. -/
def applyUpdate {n : ℕ} (s : DynSnapshot n) : DynUpdate n → DynSnapshot n
  | .insertVertex v => { s with active := insert v s.active }
  | .deleteVertex v => { s with active := s.active.erase v }
  | .insertEdge id e => { s with edges := s.edges ++ [(id, e)] }
  | .deleteEdge id => { s with edges := s.edges.filter fun ie => ie.1 ≠ id }
  | .insertTerminal v => { s with terminals := insert v s.terminals }

/-- Apply a batch in its listed order. -/
def applyBatch {n : ℕ} (s : DynSnapshot n) (B : List (DynUpdate n)) : DynSnapshot n :=
  B.foldl applyUpdate s

/-- Every elementary operation of a batch is legal at the moment it is applied. -/
def LegalBatch {n : ℕ} (s : DynSnapshot n) (B : List (DynUpdate n)) : Prop :=
  ∀ j : ℕ, ∀ h : j < B.length,
    LegalUpdate (B.take j |>.foldl applyUpdate s) B[j]

/-- Snapshot after the first `t` batches. -/
def snapshotAfter {n : ℕ} (s₀ : DynSnapshot n) (batches : List (List (DynUpdate n)))
    (t : ℕ) : DynSnapshot n :=
  (batches.take t).foldl applyBatch s₀

/-- Total number of elementary changes in the batch sequence. -/
def updateCount {n : ℕ} (batches : List (List (DynUpdate n))) : ℕ :=
  (batches.map List.length).sum

/-- The current untagged multigraph. -/
def snapshotEdges {n : ℕ} (s : DynSnapshot n) : List (IncrementalER.Edge n) :=
  s.edges.map Prod.snd

/-- Positive capacities, support on the active vertices, and connectivity there. -/
def ValidActiveGraph {n : ℕ} (s : DynSnapshot n) : Prop :=
  (∀ e ∈ snapshotEdges s, 0 < e.c) ∧
    IncrementalER.IsConnectedOn (edgeCond (snapshotEdges s)) s.active

/-- A positive capacity ratio bound `U`. -/
def CapacityRatio {n : ℕ} (U : ℝ) (es : List (IncrementalER.Edge n)) : Prop :=
  1 ≤ U ∧ (∀ e ∈ es, 0 < e.c) ∧
    ∀ e ∈ es, ∀ e' ∈ es, e.c ≤ U * e'.c

/-- A legal sequence of batches, with connected final snapshots and the capacity ratio preserved. -/
def ValidBatches {n : ℕ} (U : ℝ) (s₀ : DynSnapshot n)
    (batches : List (List (DynUpdate n))) : Prop :=
  ∀ t : ℕ, ∀ h : t < batches.length,
    LegalBatch (snapshotAfter s₀ batches t) batches[t] ∧
      ValidActiveGraph (snapshotAfter s₀ batches (t + 1)) ∧
      CapacityRatio U (snapshotEdges (snapshotAfter s₀ batches (t + 1)))

/-- Fixed-width integer record for one elementary update. -/
def updateInts {n : ℕ} : DynUpdate n → List ℤ
  | .insertVertex v => [0, ((v : ℕ) : ℤ), 0, 0]
  | .deleteVertex v => [1, ((v : ℕ) : ℤ), 0, 0]
  | .insertEdge id e => [2, (id : ℤ), ((e.u : ℕ) : ℤ), ((e.v : ℕ) : ℤ)]
  | .deleteEdge id => [3, (id : ℤ), 0, 0]
  | .insertTerminal v => [4, ((v : ℕ) : ℤ), 0, 0]

/-- One real word per elementary update; only edge insertion uses it. -/
def updateReal {n : ℕ} : DynUpdate n → ℝ
  | .insertEdge _ e => e.c
  | _ => 0

/-- Machine state after initialization and the first `t` batches.  Each batch, but no later batch,
is loaded before its run. -/
noncomputable def sparsifierRun (P : PNormReg.Program) {n : ℕ}
    (N : ℕ) (V₀ S : Finset (Fin n)) (es : List (IncrementalER.Edge n)) (epsilon k : ℝ)
    (batches : List (List (DynUpdate n))) (fuel : ℕ) (omega : ℕ → Bool) (t : ℕ) :
    PNormReg.State :=
  let initWords : List ℤ := [7, (n : ℤ), (V₀.card : ℤ), (S.card : ℤ)] ++
    V₀.toList.map (fun v => ((v : ℕ) : ℤ)) ++ S.toList.map (fun v => ((v : ℕ) : ℤ))
  let init := PNormReg.run P (loadWords (graphState N es k) initWords [epsilon, k]) omega fuel
  (batches.take t).foldl (fun st B =>
    let words : List ℤ := [8, (B.length : ℤ)] ++ B.flatMap updateInts
    PNormReg.run P (loadWords st words (epsilon :: k :: B.map updateReal)) omega fuel) init

/-- Number of output edges; terminal bits are output set `2`. -/
noncomputable def outputEdgeCount (s : PNormReg.State) (n : ℕ) : ℕ :=
  (s.integerMemory (-((32 + n : ℕ) : ℤ))).toNat

/-- Decode the maintained multigraph.  Endpoint words are reduced modulo the nonempty ambient
vertex set; capacities are read from a disjoint real-memory region. -/
noncomputable def outputEdges {n : ℕ} (hn : 0 < n) (s : PNormReg.State) :
    List (IncrementalER.Edge n) :=
  List.ofFn fun i : Fin (outputEdgeCount s n) =>
    let u : Fin n := ⟨(s.integerMemory (-((34 + n + 2 * (i : ℕ) : ℕ) : ℤ))).toNat % n,
      Nat.mod_lt _ hn⟩
    let v : Fin n := ⟨(s.integerMemory (-((35 + n + 2 * (i : ℕ) : ℕ) : ℤ))).toNat % n,
      Nat.mod_lt _ hn⟩
    ⟨u, v, s.core.mem (-((200 + (i : ℕ) : ℕ) : ℤ))⟩

/-- `A ≼ B`: the symmetric matrix `B-A` is positive semidefinite. -/
def LoewnerLE {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (B - A).PosSemidef

/-- The output is supported on `T` and spectrally approximates the current Schur complement. -/
def ValidSparsifierOutput {n : ℕ} (epsilon : ℝ) (G H : List (IncrementalER.Edge n))
    (W T : Finset (Fin n)) : Prop :=
  (∀ e ∈ H, e.u ∈ T ∧ e.v ∈ T ∧ 0 < e.c) ∧
  LoewnerLE ((1 - epsilon) • IncrementalER.schurRel (IncrementalER.lap (edgeCond G)) W T)
    (IncrementalER.edgeLap H) ∧
  LoewnerLE (IncrementalER.edgeLap H)
    ((1 + epsilon) • IncrementalER.schurRel (IncrementalER.lap (edgeCond G)) W T)

open Classical in
/-- Vertex changes plus multiset edge changes of the maintained output. -/
noncomputable def outputRecourse {n : ℕ} (T T' : Finset (Fin n))
    (H H' : List (IncrementalER.Edge n)) : ℕ :=
  ((T \ T') ∪ (T' \ T)).card + (H.diff H').length + (H'.diff H).length

/-- Full specification of Theorem 6.1. -/
def theorem61Spec (P : PNormReg.Program) (C : ℝ) (r : ℕ) (c cOut : ℝ) : Prop :=
  PNormReg.Admissible P ∧ 0 < C ∧ 1 < cOut ∧
  ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ, ∀ hn : 0 < n, n ≤ N →
  ∀ V₀ S : Finset (Fin n), S ⊆ V₀ →
  ∀ es : List (IncrementalER.Edge n),
    (∀ e ∈ es, e.u ∈ V₀ ∧ e.v ∈ V₀) →
    ValidActiveGraph (initialSnapshot V₀ S es) →
  ∀ U : ℝ, CapacityRatio U es →
    U ≤ (N : ℝ) ^ (C * (1 + Real.log N) ^ r) →
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
  ∀ k : ℝ, 1 < k → k < es.length →
    (S.card : ℝ) ≤ softBound C r N (es.length / k) →
  ∀ batches : List (List (DynUpdate n)),
    ValidBatches U (initialSnapshot V₀ S es) batches →
    (updateCount batches : ℝ) ≤ es.length / (2 * k) →
    (∀ t ≤ batches.length, ∀ u v : Fin n,
      u ≠ v → u ∈ V₀ → v ∈ V₀ →
      u ∈ (snapshotAfter (initialSnapshot V₀ S es) batches t).active →
      v ∈ (snapshotAfter (initialSnapshot V₀ S es) batches t).active →
      IncrementalER.reff (edgeCond (snapshotEdges
        (snapshotAfter (initialSnapshot V₀ S es) batches t))) u v ≤
        2 * IncrementalER.reff (edgeCond es) u v) →
    let work := softBound C r N
      (es.length * ((1 + k) ^ cOut + k ^ 4 * epsilon⁻¹ ^ 4))
    let recourseBound := softBound C r N (epsilon⁻¹ ^ 2 * es.length / k)
    let fuel := ⌊work⌋₊
    let st := fun omega t => sparsifierRun P N V₀ S es epsilon k batches fuel omega t
    let T := fun omega t => outputSet (st omega t) n 2
    let H := fun omega t => outputEdges hn (st omega t)
    (∀ t ≤ batches.length,
      (∫⁻ omega, (H omega t).length ∂PNormReg.coinTape) ≤
        ENNReal.ofReal (softBound C r N (epsilon⁻¹ ^ 2 * es.length / k))) ∧
    (∫⁻ omega, ENNReal.ofReal
        ((T omega 0).card + (H omega 0).length +
          ∑ j ∈ Finset.range batches.length,
          outputRecourse (T omega j) (T omega (j + 1)) (H omega j) (H omega (j + 1)))
      ∂PNormReg.coinTape) ≤ ENNReal.ofReal recourseBound ∧
    (∫⁻ omega, ENNReal.ofReal (st omega batches.length).work ∂PNormReg.coinTape) ≤
      ENNReal.ofReal work ∧
    PNormReg.coinTape {omega |
      ¬ (∀ t ≤ batches.length,
        let snap := snapshotAfter (initialSnapshot V₀ S es) batches t
        (st omega t).halted = true ∧ snap.terminals ⊆ T omega t ∧
          T omega t ⊆ snap.active ∧
          ((T omega t).card : ℝ) ≤ softBound C r N (es.length / k) ∧
          ValidSparsifierOutput epsilon (snapshotEdges snap) (H omega t) snap.active (T omega t) ∧
          CapacityRatio (softBound C r N
            (U * epsilon⁻¹ ^ 4 * es.length ^ 3 * V₀.card ^ 2)) (H omega t))} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-c))

end IncrementalER.Supplement


