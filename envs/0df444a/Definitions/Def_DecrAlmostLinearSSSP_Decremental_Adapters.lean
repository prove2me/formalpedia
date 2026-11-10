-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_Adapters
-- name    : DecrAlmostLinearSSSP_Decremental_Adapters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:54:38.534485+00:00
-- url     : https://prove2.me/theorems/898d491b-5215-4bc2-8594-fe0be3585489
-- title:
--   Full-domain reachability, weight scaling and stable-write adapters
-- statement:
--   Preprocessing restricts to initially source-reachable vertices and removes incoming source edges, with maps for both original deletion identifiers and output vertices. Discarded vertices read as $\infty$. The general-domain wrapper uses a constant zero source array when $n=1$, and exact Dijkstra select-minimum and outgoing-relaxation semantics when $\epsilon\le1/m$ on larger graphs.
--
--   Otherwise the dyadic scales are $L=2^j$ through the first $L\ge nW$. At scale $L$, retain edges with $w_e\le2L$ and use
--
--   $$\Delta_L=\frac{\epsilon L}{128n},\quad w'_e=\left\lceil\frac{w_e}{\Delta_L}\right\rceil,\quad W'=\left\lceil\frac{256n}{\epsilon}\right\rceil,\quad\rho=\epsilon/16,\quad\widehat m=64m.$$
--
--   These are explicit formalization choices implementing the unnumbered p.4 scaling reduction, not constants attributed to a numbered paper result. Stable scale writes update per-vertex historical maxima $b_L$. Each vertex keeps an advancing pointer to the first scale with $\Delta_Lb_L(v)\le2L$; the answer is that value or $\infty$ if no scale qualifies, with source answer zero. Only active-scale changes test a pointer. The public array is committed at completed external boundaries.
--
--   The wrapper observes actual scalar stores from the scale-program instruction trace and consumes their final completed values, rather than scanning every vertex or scale for each write. Fuel parameters denote finite proof prefixes of instruction execution; completion means genuine halt without fault. They neither certify accuracy nor supply a runtime bound. The main goal requires a single charged RAM realization, including all wrapper, rounding, preprocessing and output work.
--
--   These definitions retain arbitrary $W$, real accuracy, initial disconnection, source-incoming edges and empty streams. **Formalization Note** The mathematical minimum in the Dijkstra specification and finite set descriptions do not receive a free evaluation rule. Implementing a priority queue, bounded integer rounding and all implicit representations is part of the outstanding theorem proofs.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 4, Preliminaries and footnote 1 (unnumbered general-domain reduction); pp. 6–17, internal Theorem 3.1; pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Algorithm

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Reachability reduction is an internal transformation, never an input condition of the goal.
Its set description has the same meaning as a charged graph search in a realizing RAM. -/
def ReachVertex (i : Input) := {v : Fin i.n // Reachable i.graph Finset.univ i.source v}

noncomputable instance (i : Input) : Fintype (ReachVertex i) := by
  classical
  unfold ReachVertex
  infer_instance

noncomputable def reachableSource (i : Input) : ReachVertex i :=
  ⟨i.source, ⟨[], Walk.nil i.source⟩⟩

def RetainedEdge (i : Input) := {e : Fin i.k //
  Reachable i.graph Finset.univ i.source (i.graph.tail e) ∧
  Reachable i.graph Finset.univ i.source (i.graph.head e) ∧ i.graph.head e ≠ i.source}

noncomputable instance (i : Input) : Fintype (RetainedEdge i) := by
  classical
  unfold RetainedEdge
  infer_instance

noncomputable def preprocess (i : Input) : Input :=
  let V := Fintype.equivFin (ReachVertex i)
  let E := Fintype.equivFin (RetainedEdge i)
  { n := Fintype.card (ReachVertex i)
    k := Fintype.card (RetainedEdge i)
    graph := ⟨fun e => V ⟨i.graph.tail (E.symm e).val, (E.symm e).property.1⟩,
      fun e => V ⟨i.graph.head (E.symm e).val, (E.symm e).property.2.1⟩⟩
    source := V (reachableSource i)
    weight := fun e => i.weight (E.symm e).val
    W := i.W
    accuracy := i.accuracy
    size := i.size }

/-- Every discarded vertex is mapped back to infinity; the retained source maps to zero. -/
noncomputable def liftOutput (i : Input) (d : Fin (preprocess i).n → ℝ≥0∞)
    (v : Fin i.n) : ℝ≥0∞ := by
  classical
  exact if h : Reachable i.graph Finset.univ i.source v then
    d ((Fintype.equivFin (ReachVertex i)) ⟨v,h⟩) else ⊤

/-- A discarded deletion makes no change to the internal instance but is still charged
as an external update. IDs remain distinguishable across the reduction. -/
noncomputable def mapDeletion (i : Input) (e : Fin i.k) : Option (Fin (preprocess i).k) := by
  classical
  exact if h : Reachable i.graph Finset.univ i.source (i.graph.tail e) ∧
      Reachable i.graph Finset.univ i.source (i.graph.head e) ∧ i.graph.head e ≠ i.source then
    some ((Fintype.equivFin (RetainedEdge i)) ⟨e,h⟩) else none

noncomputable def scaleCount (i : Input) : ℕ := ⌈logarithm2 (i.n * i.W)⌉₊ + 1
noncomputable def scale (j : ℕ) : ℝ := 2 ^ j
noncomputable def delta (i : Input) (j : ℕ) : ℝ := i.accuracy * scale j / (128 * i.n)

def ScaleEdge (i : Input) (j : ℕ) := {e : Fin i.k // (i.weight e : ℝ) ≤ 2 * scale j}

noncomputable instance (i : Input) (j : ℕ) : Fintype (ScaleEdge i j) := by
  classical
  unfold ScaleEdge
  infer_instance

/-- Full-domain weight scaling. Ceilings specify a bounded integer found by comparisons
in an implementation; they are not RAM primitives. -/
noncomputable def roundedInput (i : Input) (j : ℕ) : Input :=
  let E := Fintype.equivFin (ScaleEdge i j)
  { n := i.n
    k := Fintype.card (ScaleEdge i j)
    graph := ⟨fun e => i.graph.tail (E.symm e).val, fun e => i.graph.head (E.symm e).val⟩
    source := i.source
    weight := fun e => ⌈(i.weight (E.symm e).val : ℝ) / delta i j⌉₊
    W := ⌈256 * (i.n : ℝ) / i.accuracy⌉₊
    accuracy := i.accuracy / 16
    size := 64 * i.size }

structure AdapterState (i : Input) where
  maxima : Fin (scaleCount i) → Fin i.n → ℝ≥0∞
  pointer : Fin i.n → ℕ
  dirty : Finset (Fin i.n)
  output : Fin i.n → ℝ≥0∞

noncomputable def eligible (i : Input) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (v : Fin i.n) (j : ℕ) : Bool :=
  if h : j < scaleCount i then decide (ENNReal.ofReal (delta i j) * b ⟨j,h⟩ v ≤
    ENNReal.ofReal (2 * scale j)) else false

/-- Advance only, testing each newly crossed scale once. The fuel is exactly the number
of remaining scales, not a truncation of a possibly nonterminating repair. -/
noncomputable def advance (i : Input) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (v : Fin i.n) : ℕ → ℕ → ℕ
  | 0, j => j
  | fuel + 1, j => if eligible i b v j then j else advance i b v fuel (j+1)

noncomputable def selected (i : Input) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (p : Fin i.n → ℕ) (v : Fin i.n) : ℝ≥0∞ :=
  if v = i.source then 0 else if h : p v < scaleCount i then
    ENNReal.ofReal (delta i (p v)) * b ⟨p v,h⟩ v else ⊤

/-- Initialize from the actual completed initialization outputs of all scaled instances.
Their accuracy is not a hypothesis built into this function. -/
noncomputable def adapterInitialize (i : Input)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) : AdapterState i :=
  let p := fun v => advance i b v (scaleCount i) 0
  ⟨b, p, ∅, selected i b p⟩

/-- Consume one deduplicated final stable scale write. Only an active pointer is tested;
other scales do not trigger a scan. A transient write during repair is not consumed here. -/
noncomputable def adapterWrite (i : Input) (s : AdapterState i)
    (j : Fin (scaleCount i)) (v : Fin i.n) (value : ℝ≥0∞) : AdapterState i := by
  classical
  let b := Function.update s.maxima j (Function.update (s.maxima j) v (max (s.maxima j v) value))
  let p := if s.pointer v = j.val then
    Function.update s.pointer v (advance i b v (scaleCount i - s.pointer v) (s.pointer v)) else s.pointer
  exact { s with
    maxima := b
    pointer := p
    dirty := if s.pointer v = j.val then insert v s.dirty else s.dirty }

/-- Only completed external update boundaries commit public output. -/
noncomputable def adapterCommit (i : Input) (s : AdapterState i) : AdapterState i := by
  classical
  exact { s with
    output := fun v => if v ∈ s.dirty then selected i s.maxima s.pointer v else s.output v
    dirty := ∅ }



/-- An output write observation is derived from an executed scalar store instruction.
It is not an arbitrary set supplied with an alleged successful run. -/
def writtenVertex (i : Input) (p : Program) (c : Machine) : Option (Fin i.n) :=
  if c.halted then none else match p.code[c.pc]? with
  | some (.store a _) | some (.storeN a _) =>
    if h : c.natReg a < i.n then some ⟨c.natReg a,h⟩ else none
  | _ => none

noncomputable def observedWrites (i : Input) (p : Program) (c : Machine) : ℕ → List (Fin i.n)
  | 0 => []
  | t+1 => (writtenVertex i p c).toList ++ observedWrites i p (step p c) t

structure ScaledState (i : Input) where
  machines : Fin (scaleCount i) → Machine
  adapter : AdapterState i

/-- Full initialization semantics for the normal-accuracy branch. A fuel vector records
finite instruction prefixes; successful completion is checked separately, never assumed
as input accuracy or a cost certificate. -/
noncomputable def scaledInitialize (i : Input) (p : Program)
    (fuel : Fin (scaleCount i) → ℕ) : ScaledState i :=
  let c := fun j => execute p (initialMachine p (roundedInput i j.val)) (fuel j)
  ⟨c, adapterInitialize i (fun j v => stored (c j) v.val)⟩

/-- Scale-local mapping retains original edge identities through the cutoff. -/
noncomputable def scaleDeletion (i : Input) (j : ℕ) (e : Fin i.k) : Option (Fin (roundedInput i j).k) := by
  classical
  exact if h : (i.weight e : ℝ) ≤ 2 * scale j then
    some ((Fintype.equivFin (ScaleEdge i j)) ⟨e,h⟩) else none

/-- Each scale is repaired completely before its final observed values enter the maxima.
At the external boundary, only the collected dirty entries are written to the public array.
This denotational wrapper supplies no primitive for executing a whole scale at unit cost. -/
noncomputable def scaledDelete (i : Input) (p : Program) (s : ScaledState i)
    (e : Fin i.k) (fuel : Fin (scaleCount i) → ℕ) : ScaledState i :=
  let result := (List.finRange (scaleCount i)).foldl (fun (acc : ScaledState i) j =>
    match scaleDeletion i j.val e with
    | none => acc
    | some edge =>
      let begin := deletionMachine p (acc.machines j) edge.val
      let finish := execute p begin (fuel j)
      let writes := observedWrites i p begin (fuel j)
      let adapter := writes.foldl (fun a v => adapterWrite i a j v (stored finish v.val)) acc.adapter
      { machines := Function.update acc.machines j finish, adapter := adapter }) s
  {result with adapter := adapterCommit i result.adapter}

/-- Completed means the finite instruction prefixes actually halted without fault.
No correctness or runtime condition is hidden in this boundary predicate. -/
def ScalesCompleted (i : Input) (s : ScaledState i) : Prop :=
  ∀ j, (s.machines j).halted = true ∧ (s.machines j).fault = false

/-- Exact SSSP branch: Dijkstra's select-minimum and outgoing-edge relaxation semantics.
The minimum is a mathematical specification, not a unit-cost RAM primitive. The goal
requires a charged implementation (e.g. a priority queue) of this branch. -/
noncomputable def exactRecompute (i : Input) (deleted : List (Fin i.k)) : Fin i.n → ℝ≥0∞ := by
  classical
  let initial : Fin i.n → ℝ≥0∞ := fun v => if v = i.source then 0 else ⊤
  let round := fun (state : Finset (Fin i.n) × (Fin i.n → ℝ≥0∞)) =>
    let remaining := Finset.univ \ state.1
    if h : remaining.Nonempty then
      let keys := remaining.image state.2
      let key := keys.min' (h.image state.2)
      let v := ((remaining.toList).find? (fun v => state.2 v = key)).getD i.source
      let out := (live deleted).toList.filter (fun e => i.graph.tail e = v)
      let d := out.foldl (fun a e => Function.update a (i.graph.head e)
        (min (a (i.graph.head e)) (state.2 v + (i.weight e : ℝ≥0∞)))) state.2
      (insert v state.1, d)
    else state
  exact ((round^[i.n]) (∅, initial)).2

/-- General-domain wrapper state. The exact branch keeps a deletion history; the scale
branch keeps the actual scaled machines. Neither carries a correctness/cost certificate. -/
structure FullState (i : Input) where
  deleted : List (Fin i.k)
  scaled : Option (ScaledState i)
  output : Fin i.n → ℝ≥0∞

noncomputable def fullInitialize (i : Input) (p : Program)
    (fuel : Fin (scaleCount i) → ℕ) : FullState i :=
  if i.n = 1 then ⟨[], none, fun _ => 0⟩
  else if i.accuracy ≤ 1 / (i.size : ℝ) then
    ⟨[], none, exactRecompute i []⟩
  else
    let s := scaledInitialize i p fuel
    ⟨[], some s, s.adapter.output⟩

noncomputable def fullDelete (i : Input) (p : Program) (s : FullState i)
    (e : Fin i.k) (fuel : Fin (scaleCount i) → ℕ) : FullState i :=
  let deleted := s.deleted ++ [e]
  if i.n = 1 then ⟨deleted, none, fun _ => 0⟩ else match s.scaled with
  | none => ⟨deleted, none, exactRecompute i deleted⟩
  | some old =>
    let result := scaledDelete i p old e fuel
    ⟨deleted, some result, result.adapter.output⟩

end DecrAlmostLinearSSSP.Decremental


