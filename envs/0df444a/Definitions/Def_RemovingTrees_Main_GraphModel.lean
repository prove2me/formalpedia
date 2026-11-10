-- Prove2me | Definitions.Def_RemovingTrees_Main_GraphModel
-- name    : RemovingTrees_Main_GraphModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:20:30.915294+00:00
-- url     : https://prove2.me/theorems/efeec8bc-3870-4da9-959a-b85d0c13128c
-- title:
--   Labeled multigraph tree-removal model and charged computation interface
-- statement:
--   Let the vertices be $V=\{0,\ldots,n-1\}$ and the independently labeled edges be $E=\{0,\ldots,m-1\}$. Each edge has two endpoints; loops and parallel edges are permitted. For active edges $F\subseteq E$ and a shore $S\subseteq V$, define
--   $$
--   \delta_F(S)=\{e\in F:\text{exactly one endpoint of }e\text{ belongs to }S\},\qquad
--   \lambda(F)=\min_{\varnothing\ne S\subsetneq V}|\delta_F(S)|.
--   $$
--   Every theorem assumes $n\ge2$. Connectivity means every nontrivial cut is nonempty; a spanning tree is a connected spanning edge set minimal under deletion of any edge. A packing is a list of pairwise edge-disjoint spanning trees, and its union is an actual edge subset. A packing lower bound is an integer inequality, so negative lower bounds allow the empty packing.
--
--   The spanning-tree polytope is the convex hull of all tree incidence vectors in $\mathbb R^E$. Four-region crossing is defined separately from the referenced laminarity predicate. Rooted deficient families include every shore avoiding the root whose cut is strictly below the given real threshold, including the empty shore when appropriate.
--
--   An $(\eta,r,C)$-subgraph $H$ is a union of $r$ packed trees with
--   $$
--   \lambda(G-H)\ge(1-\eta)k-88C,\qquad
--   G-H\text{ contains at least }\lfloor k/2\rfloor-44C\text{ packed trees}.
--   $$
--   The ambient $k$ is positive and even in the improvement lemma. The module also defines $\alpha(\eta)=44^{\lfloor4\eta^{-2}\rfloor}$, the crossing graph, and the exact-union laminar cover predicate with bound $13\epsilon^{-2}$. These interfaces keep edge multiplicities, residual subgraphs, and source definitions consistent across all seven statements.
--
--   **Formalization Note** The published endpoint carrier is reused after forgetting orientation; no directed cut or flow predicate is used. The minimum has a zero fallback only for $n<2$, excluded by every theorem. Real lower bounds use cut inequalities rather than truncated natural subtraction. The goal uses $h(k)=\sqrt{\max(1,\ln k)}$ and $A=2\sqrt{20\ln44}+89$; these conventions do not redefine the source's connectivity.
--
--   A graph input explicitly lists its vertex and edge counts and both endpoints of every edge. Natural numbers use the published framed binary code. Sets are encoded by sorted lists of original identifiers, lists by a length followed by their encoded members, and rational numbers by sign, numerator magnitude, and positive denominator.
--
--   A bit computation uses the referenced finite Boolean-stack machine. A real computation uses a finite control table, finitely many Boolean stacks and real stacks, and only rational constants, copying, addition, subtraction, multiplication, division, and sign comparisons. The real input is a supplied list of coordinates or parameters, not a rounding or optimization oracle. Each transition is charged one operation; the finite number of operations within a transition is fixed by the machine.
--
--   For coefficient $a>0$ and degree $d\in\mathbb N$, the output relation requires the actual machine to have halted by
--   $$
--   a(L+1)^d\quad\text{bit steps},\qquad
--    a(L+s+1)^d\quad\text{exact-real transitions},
--   $$
--   where $L$ is encoded bit length and $s$ is the number of supplied real entries. Its actual output bits must encode the promised tree, packing witnesses, or explicitly enumerated laminar families. Tree lists have distinct edge identifiers. Cover output contains every required shore, and its number of families is compared in $\mathbb R$.
--
--   These definitions make the constructive clauses mathematical claims about a fixed finite program and its output. No correctness, rounding result, or polynomial algorithm is assumed inside the definitions. Invalid graph encodings have no correctness promise.
--
--   **Formalization Note** Lemma 3.3 uses input $C=0$ as the request for its single-tree clause; positive $C$ requests the general clause. The improvement interface accepts the two packing witnesses already supplied by Definition 3.6 and returns explicit witnesses as well. Its rational bit implementation charges the entire signed rational encoding. Division and empty-stack access are totalized; they supply no graph oracle.
-- source:
--   Nathan Klein, Neil Olver, Zi Song Yeoh, STOC 2027 submission #1092 (October 2026), §2, pp.3–4; Eq.(1), p.5; Definition 3.6 and Lemma 3.7, p.6; Eq.(2), p.7; Lemma 3.8, p.8; computational conventions for the constructive clauses, pp.4–8

import Mathlib
import Definitions.Def_SteinerCutDominants_IsLaminar
import Definitions.Def_CombOpt_MinCostFlow_Digraph
import Definitions.Def_AlgorithmicThinTrees

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace RemovingTrees.Main

/-- Use the published unconstrained endpoint carrier, forgetting its orientation.
Every cut below is symmetric in tail and head; no directed cut/flow notion is reused. -/
abbrev MultiGraph (n m : ℕ) := CombOpt.MinCostFlow.Digraph (Fin n) (Fin m)

abbrev MultiGraph.left {n m : ℕ} (G : MultiGraph n m) := G.tail
abbrev MultiGraph.right {n m : ℕ} (G : MultiGraph n m) := G.head

def cut {n m : ℕ} (G : MultiGraph n m) (F : Finset (Fin m))
    (S : Finset (Fin n)) : Finset (Fin m) :=
  F.filter fun e => (G.left e ∈ S ∧ G.right e ∉ S) ∨
    (G.right e ∈ S ∧ G.left e ∉ S)

def NontrivialShore {n : ℕ} (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ S ≠ Finset.univ

def Connected {n m : ℕ} (G : MultiGraph n m) (F : Finset (Fin m)) : Prop :=
  ∀ S, NontrivialShore S → (cut G F S).Nonempty

def Tree {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m)) : Prop :=
  Connected G T ∧ ∀ e ∈ T, ¬ Connected G (T.erase e)

def cutCounts {n m : ℕ} (G : MultiGraph n m) (F : Finset (Fin m)) : Finset ℕ :=
  ((Finset.univ : Finset (Fin n)).powerset.filter NontrivialShore).image
    (fun S => (cut G F S).card)

/-- Minimum over all nonempty proper shores. The fallback is used only for n < 2. -/
def connectivity {n m : ℕ} (G : MultiGraph n m) (F : Finset (Fin m)) : ℕ :=
  if h : (cutCounts G F).Nonempty then (cutCounts G F).min' h else 0

/-- Real lower bounds avoid truncated subtraction. -/
def CutLower {n m : ℕ} (G : MultiGraph n m) (F : Finset (Fin m)) (b : ℝ) : Prop :=
  ∀ S, NontrivialShore S → b ≤ ((cut G F S).card : ℝ)

def Packing {n m : ℕ} (G : MultiGraph n m) (F : Finset (Fin m))
    (ts : List (Finset (Fin m))) : Prop :=
  (∀ T ∈ ts, T ⊆ F ∧ Tree G T) ∧ ts.Pairwise Disjoint

def treeUnion {m : ℕ} (ts : List (Finset (Fin m))) : Finset (Fin m) :=
  ts.foldl (fun H T => H ∪ T) ∅

def PackedUnion {n m : ℕ} (G : MultiGraph n m) (F : Finset (Fin m))
    (r : ℕ) (H : Finset (Fin m)) : Prop :=
  ∃ ts, ts.length = r ∧ Packing G F ts ∧ treeUnion ts = H

/-- Negative integer lower bounds have their literal meaning, including the empty packing. -/
def HasPackingAtLeast {n m : ℕ} (G : MultiGraph n m) (F : Finset (Fin m)) (z : ℤ) : Prop :=
  ∃ ts, Packing G F ts ∧ z ≤ (ts.length : ℤ)

def Cross {n : ℕ} (A B : Finset (Fin n)) : Prop :=
  (A \ B).Nonempty ∧ (B \ A).Nonempty ∧ (A ∩ B).Nonempty ∧
    ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).Nonempty

def rootedLowCuts {n m : ℕ} (G : MultiGraph n m) (F : Finset (Fin m))
    (root : Fin n) (b : ℝ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter
    (fun S => root ∉ S ∧ ((cut G F S).card : ℝ) < b)

def treeVector {m : ℕ} (T : Finset (Fin m)) : Fin m → ℝ :=
  fun e => if e ∈ T then 1 else 0

def spanningTreePolytope {n m : ℕ} (G : MultiGraph n m) (F : Finset (Fin m)) :
    Set (Fin m → ℝ) :=
  convexHull ℝ {x | ∃ T, T ⊆ F ∧ Tree G T ∧ x = treeVector T}

def ThinOn {n m : ℕ} (G : MultiGraph n m) (F T : Finset (Fin m))
    (x : Fin m → ℝ) (L : Finset (Finset (Fin n))) : Prop :=
  T ⊆ F ∧ Tree G T ∧ ∀ S ∈ L, ((cut G T S).card : ℝ) ≤ 22 * ∑ e ∈ cut G F S, x e

/-- Definition 3.6, with k an ambient positive even connectivity lower bound. -/
def GoodSubgraph {n m : ℕ} (G : MultiGraph n m) (k : ℕ) (η : ℝ)
    (r C : ℕ) (H : Finset (Fin m)) : Prop :=
  PackedUnion G Finset.univ r H ∧
  CutLower G (Finset.univ \ H) ((1 - η) * k - 88 * C) ∧
  HasPackingAtLeast G (Finset.univ \ H) (((k / 2 : ℕ) : ℤ) - (44 : ℤ) * C)

def alpha (η : ℝ) : ℕ := 44 ^ ⌊4 * (η⁻¹)^2⌋₊

def lossScale (k : ℕ) : ℝ := Real.sqrt (max 1 (Real.log k))

def lossConstant : ℝ := 2 * Real.sqrt (20 * Real.log 44) + 89

def coverUnion {n : ℕ} (ls : List (Finset (Finset (Fin n)))) : Finset (Finset (Fin n)) :=
  ls.foldl (fun H L => H ∪ L) ∅

def LaminarCover {n : ℕ} (N : Finset (Finset (Fin n))) (ε : ℝ)
    (ls : List (Finset (Finset (Fin n)))) : Prop :=
  coverUnion ls = N ∧ (∀ L ∈ ls, SteinerCutDominants.IsLaminar L) ∧
  (ls.length : ℝ) ≤ 13 * (ε⁻¹)^2

/-- Auxiliary crossing graph; inputs to the removal theorem remain arbitrary multigraphs. -/
def crossGraph {n : ℕ} (N : Finset (Finset (Fin n))) : SimpleGraph {S // S ∈ N} where
  Adj A B := Cross A.val B.val
  symm := ⟨by
    intro A B h
    exact ⟨h.2.1, h.1, by simpa [Finset.inter_comm] using h.2.2.1,
      by simpa [Finset.union_comm] using h.2.2.2⟩⟩
  loopless := ⟨by
    intro A h
    simpa using h.1⟩

/-! Encoded algorithmic problem interface for the graph notions above. -/


abbrev Bits := List Bool
abbrev encNat := OAI.CurrentKS.encodeNat

def encList {α : Type} (f : α → Bits) (xs : List α) : Bits :=
  encNat xs.length ++ xs.flatMap f

def encSet {s : ℕ} (F : Finset (Fin s)) : Bits :=
  encList (fun e => encNat e.val) (F.sort (· ≤ ·))

def encGraph {n m : ℕ} (G : MultiGraph n m) : Bits :=
  encNat n ++ encNat m ++ (List.ofFn fun e =>
    encNat (G.left e).val ++ encNat (G.right e).val).flatten

def encRat (x : ℚ) : Bits :=
  [decide (x.num < 0)] ++ encNat x.num.natAbs ++ encNat x.den

def encEdges {m : ℕ} (es : List (Fin m)) : Bits := encList (fun e => encNat e.val) es

def TreeOutput {n m : ℕ} (G : MultiGraph n m) (P : Finset (Fin m) → Prop)
    (bits : Bits) : Prop :=
  ∃ es : List (Fin m), es.Nodup ∧ bits = encEdges es ∧ Tree G es.toFinset ∧ P es.toFinset

/-- The published Boolean-stack machine must halt and its actual output must satisfy P. -/
def BitResult (M : OAI.CurrentKS.Machine) (a d : ℕ) (input : Bits) (P : Bits → Prop) : Prop :=
  let c := M.run input (a * (input.length + 1)^d)
  c.state = none ∧ P (c.stacks M.outputStack)

/-- Unit-cost exact real stack operations: no graph, optimization, or rounding oracle. -/
inductive RealAction (r : ℕ) where
  | stay
  | pop
  | constant (x : ℚ)
  | copy (i : Fin r)
  | add (i j : Fin r)
  | sub (i j : Fin r)
  | mul (i j : Fin r)
  | div (i j : Fin r)

def realTop (xs : List ℝ) : ℝ := xs.headD 0

def RealAction.apply {r : ℕ} (op : RealAction r) (s : Fin r → List ℝ) (target : Fin r) : List ℝ :=
  match op with
  | .stay => s target
  | .pop => (s target).tail
  | .constant x => (x : ℝ) :: s target
  | .copy i => realTop (s i) :: s target
  | .add i j => (realTop (s i) + realTop (s j)) :: s target
  | .sub i j => (realTop (s i) - realTop (s j)) :: s target
  | .mul i j => (realTop (s i) * realTop (s j)) :: s target
  | .div i j => (realTop (s i) / realTop (s j)) :: s target

def signCode (x : ℝ) : ℕ := if x < 0 then 0 else if x = 0 then 1 else 2

def realHeadsCode : (r : ℕ) → (Fin r → List ℝ) → ℕ
  | 0, _ => 0
  | r+1, s => signCode (realTop (s 0)) + 3 * realHeadsCode r (fun i => s i.succ)

structure RealInstruction (b r q : ℕ) where
  control : OAI.CurrentKS.Instruction b q
  arithmetic : Fin r → RealAction r

structure RealMachine where
  boolCount : ℕ
  realCount : ℕ
  states : ℕ
  initial : Fin states
  bitInput : Fin boolCount
  bitOutput : Fin boolCount
  realInput : Fin realCount
  table : List (RealInstruction boolCount realCount states)

structure RealConfig (b r q : ℕ) where
  control : OAI.CurrentKS.Config b q
  registers : Fin r → List ℝ

def RealMachine.step (M : RealMachine) (c : RealConfig M.boolCount M.realCount M.states) :
    RealConfig M.boolCount M.realCount M.states :=
  match c.control.state with
  | none => c
  | some q =>
    let idx := (3 ^ (M.boolCount + M.realCount)) * q.val +
      OAI.CurrentKS.headsCode M.boolCount c.control.stacks +
      3 ^ M.boolCount * realHeadsCode M.realCount c.registers
    let ins := M.table.getD idx ⟨OAI.CurrentKS.Instruction.halt _ _, fun _ => .stay⟩
    ⟨⟨ins.control.next, fun j => (ins.control.actions j).apply (c.control.stacks j)⟩,
      fun j => (ins.arithmetic j).apply c.registers j⟩

def RealMachine.init (M : RealMachine) (bits : Bits) (xs : List ℝ) :
    RealConfig M.boolCount M.realCount M.states :=
  ⟨⟨some M.initial, fun j => if j = M.bitInput then bits else []⟩,
    fun j => if j = M.realInput then xs else []⟩

def RealMachine.run (M : RealMachine) (bits : Bits) (xs : List ℝ) (fuel : ℕ) :
    RealConfig M.boolCount M.realCount M.states :=
  (M.step^[fuel]) (M.init bits xs)

def RealResult (M : RealMachine) (a d : ℕ) (bits : Bits) (xs : List ℝ) (P : Bits → Prop) : Prop :=
  let c := M.run bits xs (a * (bits.length + xs.length + 1)^d)
  c.control.state = none ∧ P (c.control.stacks M.bitOutput)

/-- Output both the removed packing and an explicit residual packing witness. -/
def WarmupOutput {n m : ℕ} (G : MultiGraph n m) (k C : ℕ) (bits : Bits) : Prop :=
  if C = 0 then
    TreeOutput G (fun T => CutLower G (Finset.univ \ T) ((3:ℝ)/4*k - 67)) bits
  else ∃ ts us : List (Finset (Fin m)),
    bits = encList encSet ts ++ encList encSet us ∧
    ts.length = C ∧ Packing G Finset.univ ts ∧
    Packing G (Finset.univ \ treeUnion ts) us ∧
    ((k/2 : ℕ) : ℤ) - 44*C ≤ (us.length : ℤ) ∧
    CutLower G (Finset.univ \ treeUnion ts) ((3:ℝ)/4*k - 67*C)

def ImprovementInput {n m : ℕ} (G : MultiGraph n m) (k r C : ℕ)
    (H : Finset (Fin m)) (ts us : List (Finset (Fin m))) : Bits :=
  encGraph G ++ encNat k ++ encNat r ++ encNat C ++ encSet H ++ encList encSet ts ++ encList encSet us

/-- The supplied packings witness Definition 3.6; no desired output is an input. -/
def ImprovementWitness {n m : ℕ} (G : MultiGraph n m) (k r C : ℕ)
    (H : Finset (Fin m)) (ts us : List (Finset (Fin m))) : Prop :=
  ts.length = r ∧ Packing G Finset.univ ts ∧ treeUnion ts = H ∧
  Packing G (Finset.univ \ H) us ∧ ((k/2 : ℕ) : ℤ) - 44*C ≤ (us.length : ℤ)

def ImprovementOutput {n m : ℕ} (G : MultiGraph n m) (k r C : ℕ)
    (η : ℝ) (H : Finset (Fin m)) (bits : Bits) : Prop :=
  ∃ ts us : List (Finset (Fin m)),
    bits = encList encSet ts ++ encList encSet us ∧
    ts.length = r / alpha η ∧ Packing G H ts ∧
    Packing G (Finset.univ \ treeUnion ts) us ∧
    ((k/2 : ℕ) : ℤ) - 44*C ≤ (us.length : ℤ) ∧
    GoodSubgraph G k ((3:ℝ)/4*η) (r / alpha η) C (treeUnion ts)

def CoverOutput {n : ℕ} (N : Finset (Finset (Fin n))) (ε : ℝ) (bits : Bits) : Prop :=
  ∃ ls : List (List (Finset (Fin n))),
    (∀ L ∈ ls, L.Nodup) ∧
    bits = encList (encList encSet) ls ∧ LaminarCover N ε (ls.map List.toFinset)

end RemovingTrees.Main


