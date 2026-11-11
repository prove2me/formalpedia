-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Procedures
-- name    : SparsestCutOracle_Main_Procedures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:38.967875+00:00
-- url     : https://prove2.me/theorems/0c3bc8b4-979e-4f4f-90e4-132bdc1e37c3
-- title:
--   Charged oracle-relative programs and sparse certificate encoding
-- statement:
--   An oracle-relative program is a finite instruction list. In addition to charged scalar operations it may request a fair cut/flow pair through pointer-addressed input and output blocks, or multiply a vector by a fixed matrix $A$, charged $t_A$ per call. Neither instruction carries an arbitrary function. Every fair call is required to have an already well-formed raw edge-list encoding; the decoder cannot filter invalid endpoints or clamp negative capacities for free. Fair calls are counted in an immutable counter, and a theorem quantifies over every correct service; probabilistic theorems also require measurable finite executions. A service sees the query and call index, not the caller’s private sign or memory.
--
--   For a program $P$ and service $O$, the expected fair-call bound is
--
--   $$\int N_{P,O}(\omega)\,d\mu(\omega)\le B,$$
--
--   with almost-sure halting and integrability stated explicitly. Response matrices are pinned by a sparse path list and edge lists in output memory. This interface expresses subroutine-call bounds while preventing an existentially chosen uncharged solver from serving as a program.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 9, 19–20, 25–28, algorithmic and oracle interfaces

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_SDP

namespace SparsestCutOracle.Main

/-- Canonical edge-list decoder. Out-of-range endpoints and loops are discarded, negative
capacities are zero. These are observations of memory, not program instructions. -/
noncomputable def readGraph (n : ℕ) (I : ℕ → ℤ) (R : ℕ → ℝ) : Graph n :=
  (List.range (I 0).toNat).filterMap fun k =>
    let u := (I (1 + 2 * k)).toNat
    let v := (I (2 + 2 * k)).toNat
    if hu : u < n then
      if hv : v < n then
        if u = v then none else some ⟨⟨u, hu⟩, ⟨v, hv⟩, (R k).toNNReal⟩
      else none
    else none

structure FairRequest where
  n : ℕ
  graph : Graph n
  sources : Fin n → ℝ
  targets : Fin n → ℝ
  fairness : ℝ

structure FairAnswer (q : FairRequest) where
  side : Finset (Fin q.n)
  values : Fin q.graph.length → ℝ

noncomputable def FairAnswer.flow {q : FairRequest} (a : FairAnswer q) : Flow q.n :=
  fun u v => ∑ i : Fin q.graph.length,
    let e := q.graph[i.val]
    if e.u = u ∧ e.v = v then a.values i else
      if e.u = v ∧ e.v = u then -a.values i else 0

/-- An indexed sequence of query-only ideal fair-flow services. A service cannot inspect the
caller’s private registers, random sign, or unused random tape. Correct answers are universally
quantified; the index permits independent subroutine tapes at successive calls. -/
abbrev FairService := ℕ → (q : FairRequest) → FairAnswer q

def FairAnswersCorrect (O : FairService) : Prop :=
  ∀ k q, (∀ v, 0 ≤ q.sources v) → (∀ v, 0 ≤ q.targets v) → 1 ≤ q.fairness →
    FairPair q.graph.toWGraph q.sources q.targets q.fairness
      (O k q).side (O k q).flow

/-- Query layout: integer n,m,endpoints; real capacities,s,t,ω, at the pointed-to address. -/
noncomputable def readFair (s : State) (a : ℤ) : FairRequest :=
  let n := (s.base.integerMemory a).toNat
  let m := (s.base.integerMemory (a + 1)).toNat
  let G := readGraph n
    (fun k => s.base.integerMemory (a + 1 + k))
    (fun k => s.base.core.mem (a + k))
  ⟨n, G,
    (fun v => s.base.core.mem (a + m + v.val)),
    (fun v => s.base.core.mem (a + m + n + v.val)),
    s.base.core.mem (a + m + 2 * n)⟩

/-- A fair query is already a well-formed edge list. The contract never permits the
mathematical decoder to do uncharged filtering, clamping, or sparse compaction for a program. -/
def FairEncodingValid (s : State) (a : ℤ) : Prop :=
  let ni := s.base.integerMemory a
  let mi := s.base.integerMemory (a + 1)
  let n := ni.toNat
  let m := mi.toNat
  0 ≤ ni ∧ 0 ≤ mi ∧
  (∀ k : Fin m,
    let u := s.base.integerMemory (a + 2 + 2 * (k.val : ℤ))
    let v := s.base.integerMemory (a + 3 + 2 * (k.val : ℤ))
    0 ≤ u ∧ u < ni ∧ 0 ≤ v ∧ v < ni ∧ u ≠ v ∧
      0 ≤ s.base.core.mem (a + k.val)) ∧
  (∀ v : Fin n, 0 ≤ s.base.core.mem (a + m + v.val) ∧
    0 ≤ s.base.core.mem (a + m + n + v.val)) ∧
  1 ≤ s.base.core.mem (a + m + 2 * n)

/-- Query instructions have only register arguments, and no function-valued payload. -/
inductive ProcInstr where
  | base (op : Instr)
  | fair (queryPointer answerPointer : ℕ)
  | matvec (inputPointer outputPointer : ℕ)

abbrev Procedure := List ProcInstr

def scalarProgram (P : Procedure) : Program := P.map fun op => match op with
  | .base i => i
  | _ => .base (.core (.const 0 0))

def ProcAdmissible (P : Procedure) : Prop := Admissible (scalarProgram P)

structure ProcState where
  machine : State
  fairCalls : ℕ
  matvecCalls : ℕ

/-- The only matrix-vector oracle available to a Gram sketch is multiplication by this fixed A;
its per-call charge is tA. No matrix exponential oracle is available. -/
structure MatvecContext where
  n : ℕ
  A : Mat n
  charge : ℕ

noncomputable def procStep (P : Procedure) (O : FairService) (V : MatvecContext)
    (ω : Tape) (s : ProcState) : ProcState := by
  classical
  exact if s.machine.base.halted then s else
    match P[s.machine.base.core.pc]? with
    | some (.fair q r) =>
      let request := readFair s.machine (s.machine.base.core.ptrs q)
      let answer := O s.fairCalls request
      let b := s.machine.base.core.ptrs r
      { s with
        fairCalls := s.fairCalls + 1
        machine := { s.machine with base := { s.machine.base with
          work := s.machine.base.work + 1
          integerMemory := fun z =>
            if h : b ≤ z ∧ z < b + request.n then
              if (⟨(z - b).toNat, by omega⟩ : Fin request.n) ∈ answer.side then 1 else 0
            else s.machine.base.integerMemory z
          core := { s.machine.base.core with
            pc := s.machine.base.core.pc + 1
            mem := fun z => if h : b ≤ z ∧ z < b + request.graph.length then
              answer.values ⟨(z - b).toNat, by omega⟩
              else s.machine.base.core.mem z } } } }
    | some (.matvec q r) =>
      let a := s.machine.base.core.ptrs q
      let b := s.machine.base.core.ptrs r
      let u : Fin V.n → ℝ := fun i => s.machine.base.core.mem (a + i.val)
      { s with
        matvecCalls := s.matvecCalls + 1
        machine := { s.machine with base := { s.machine.base with
          work := s.machine.base.work + V.charge
          core := { s.machine.base.core with
            pc := s.machine.base.core.pc + 1
            mem := fun z => if h : b ≤ z ∧ z < b + V.n then
              ∑ j, V.A ⟨(z-b).toNat, by omega⟩ j * u j
              else s.machine.base.core.mem z } } } }
    | _ => { s with machine := step (scalarProgram P) ω s.machine }

noncomputable def procRun (P : Procedure) (O : FairService) (V : MatvecContext)
    (s : State) (ω : Tape) (t : ℕ) : ProcState :=
  (procStep P O V ω)^[t] ⟨s, 0, 0⟩

/-- Finite executions of an oracle algorithm have measurable observable coordinates.
This is the usual measurability convention for a randomized subroutine, and rules out
nonmeasurable choice functions masquerading as algorithms. -/
def FairServiceMeasurable (O : FairService) : Prop :=
  ∀ (P : Procedure) (V : MatvecContext) (s : State) (t k : ℕ) (z : ℤ),
    Measurable (fun ω => (procRun P O V s ω t).machine.base.core.regs k) ∧
    Measurable (fun ω => (procRun P O V s ω t).machine.base.core.ptrs k) ∧
    Measurable (fun ω => (procRun P O V s ω t).machine.base.core.mem z) ∧
    Measurable (fun ω => (procRun P O V s ω t).machine.base.integerMemory z) ∧
    Measurable (fun ω => (procRun P O V s ω t).machine.base.halted) ∧
    Measurable (fun ω => (procRun P O V s ω t).fairCalls)

def ValidFairService (O : FairService) : Prop := FairAnswersCorrect O ∧ FairServiceMeasurable O

def ProcHalts (P : Procedure) (O : FairService) (V : MatvecContext) (s : State) (ω : Tape) : Prop :=
  ∃ t, (procRun P O V s ω t).machine.base.halted = true

noncomputable def procFinal (P : Procedure) (O : FairService) (V : MatvecContext)
    (s : State) (ω : Tape) : ProcState := by
  classical
  exact if h : ProcHalts P O V s ω then procRun P O V s ω (Nat.find h) else ⟨s, 0, 0⟩

noncomputable def noMatvec : MatvecContext := ⟨0, 0, 1⟩

def NoMatvec (P : Procedure) : Prop := ∀ op ∈ P, ∀ a b, op ≠ .matvec a b

def NoFair (P : Procedure) : Prop := ∀ op ∈ P, ∀ a b, op ≠ .fair a b

/-- Expected fair-call count and a.s. termination, uniformly in every valid ideal service. -/
def ExpectedCalls (P : Procedure) (O : FairService) (s : State) (bound : ℝ) : Prop :=
  (∀ᵐ ω ∂tapeLaw, ProcHalts P O noMatvec s ω) ∧
  MeasureTheory.Integrable (fun ω => ((procFinal P O noMatvec s ω).fairCalls : ℝ)) tapeLaw ∧
  (∫ ω, ((procFinal P O noMatvec s ω).fairCalls : ℝ) ∂tapeLaw) ≤ bound

def ProcHighProbability (n a : ℕ) (P : Procedure) (O : FairService) (V : MatvecContext)
    (s : State) (Q : ProcState → Prop) : Prop :=
  ∃ E : Set Tape, MeasurableSet E ∧
    ENNReal.ofReal (1 - (n : ℝ) ^ (-(a : ℤ))) ≤ tapeLaw E ∧
    ∀ ω ∈ E, ProcHalts P O V s ω ∧ Q (procFinal P O V s ω)

/-- Sparse output encoding. Negative integer cells 0,1 are a tag and number of path terms.
Each path term uses a fixed integer block of 1+cP*n cells (length then vertices).
Its real coefficient is in cell 1+k. Duplicated paths are combined by summation. -/
def outInt (s : State) (k : ℕ) : ℤ := s.base.integerMemory (-1 - (k : ℤ))
def outReal (s : State) (k : ℕ) : ℝ := s.base.core.mem (-1 - (k : ℤ))

noncomputable def readPath (n cP : ℕ) (s : State) (k : ℕ) : List (Fin n) :=
  let b := 4 + k * (1 + cP * n)
  (List.range (min (outInt s b).toNat (cP * n))).filterMap fun j =>
    let v := (outInt s (b + 1 + j)).toNat
    if h : v < n then some ⟨v, h⟩ else none

def EncodedPaths {n cP : ℕ} (s : State) (F : PathFlow n cP) : Prop :=
  ∀ p, F.coeff p = ∑ k ∈ Finset.range (outInt s 1).toNat,
    if readPath n cP s k = p then outReal s (1 + k) else 0

noncomputable def outputGraph (n b : ℕ) (s : State) : Graph n :=
  readGraph n (fun k => outInt s (b + k)) (fun k => outReal s (b + k))

/-- F and the added graph are encoded as sparse edge lists at offsets supplied in cells 2 and 3.
Every component is pinned by the output memory; no arbitrary matrix is silently supplied. -/
def EncodedResponse {n cP : ℕ} (s : State) (r : Response n cP) : Prop :=
  outInt s 0 = 1 ∧ r.z = outReal s 0 ∧ EncodedPaths s r.paths ∧
  r.F = laplacian (outputGraph n (outInt s 2).toNat s).toWGraph ∧
  r.augmented = (outputGraph n (outInt s 3).toNat s).toWGraph

/-- Cut outputs use real cells 1+v for 0/1 membership, independently of the response tag. -/
noncomputable def procCut (n : ℕ) (s : State) : Finset (Fin n) :=
  Finset.univ.filter fun v => outReal s (1 + v.val) ≠ 0

/-- Sparse graph inputs plus an explicit matrix X, scalars, and a membership vector for A. -/
noncomputable def oracleInput {n : ℕ} (G : Graph n) (π : Fin n → ℝ) (X : Mat n)
    (params : List ℝ) (A : Finset (Fin n) := Finset.univ) : State :=
  init (graphInts G)
    (graphReals G π (params ++
      ((List.finRange n).flatMap fun i => (List.finRange n).map (X i)) ++
      ((List.finRange n).map fun v => if v ∈ A then 1 else 0)))

/-- Every fair query made on a run has the prescribed fairness and graph-size bounds. -/
def QuerySizes (P : Procedure) (O : FairService) (s : State)
    (loN hiN loM hiM : ℝ) : Prop :=
  ∀ (ω : Tape) (t : ℕ) (a b : ℕ),
    let st := procRun P O noMatvec s ω t
    st.machine.base.halted = false →
    P[st.machine.base.core.pc]? = some (.fair a b) →
    let q := readFair st.machine (st.machine.base.core.ptrs a)
    FairEncodingValid st.machine (st.machine.base.core.ptrs a) ∧
    q.fairness = 2 ∧ (∀ v, 0 ≤ q.sources v) ∧ (∀ v, 0 ≤ q.targets v) ∧
    loN ≤ q.n ∧ (q.n : ℝ) ≤ hiN ∧
    loM ≤ q.graph.length ∧ (q.graph.length : ℝ) ≤ hiM

end SparsestCutOracle.Main


