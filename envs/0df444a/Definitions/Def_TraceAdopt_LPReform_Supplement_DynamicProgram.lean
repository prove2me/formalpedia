-- Prove2me | Definitions.Def_TraceAdopt_LPReform_Supplement_DynamicProgram
-- name    : TraceAdopt_LPReform_Supplement_DynamicProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:51:53.908197+00:00
-- url     : https://prove2.me/theorems/d97b6926-2eee-4ce2-8f15-a20f5f1b443b
-- title:
--   Appendix D, Algorithm 2 — residual-demand table evaluation, backpointers and charged RAM realization
-- statement:
--   This is a residual-demand implementation of the weighted diffusion dynamic program of Appendix D on the published auxiliary graph $G'$ and a nice decomposition of width $q$.
--
--   A bag state records unmet incoming thresholds $d_v\in\{0,\ldots,\vartheta_{\max}\}$, distinct activation ranks in $\{0,\ldots,q+1\}$, and a firm-seed mask. Residual demand is the actual threshold minus incoming weight from earlier vertices in the subtree, truncated at zero. Only firms may be seeds. Entries store a real cost and two child-state indices; an absent entry means infeasibility. Finite left-to-right folds choose the first cheapest candidate.
--
--   Leaves enumerate firm seeds and orders. Replacement checks the forgotten vertex's demand, minimizes over compatible child states, introduces the new vertex and updates directed incoming contributions to later common vertices. Joins require matching boundary seeds and orders, add child costs and subtract the boundary seed cost once. For actual threshold $\tau_v$ and incoming weight $b_v$ from earlier boundary vertices, the residual update is
--
--   $$d_v=\max\{d_v^0+d_v^1+\min(b_v,\tau_v)-\tau_v,0\}.$$
--
--   Root states require zero remaining demand at every nonseed. Reconstruction follows stored backpointers and marks firm output bits. Tables never copy global seed sets.
--
--   `RealizesDiffusionDP` requires actual configurations of one fixed oracle-free RAM program on the original instance: preparation writes the encoded nice decomposition, postorder checkpoints write every entry of the recursively evaluated tables, and the halted configuration retains the tables and reconstructed seed set. All steps, including preparation and reconstruction, belong to the same charged run. No decomposition, advice or optimum is supplied as input.
--
--   **Formalization Note** This is an implementation of the existential Theorem 3, not a claim about every literal convention of printed Algorithm 2. The seed mask preserves signed costs; strict ranks refine simultaneous activations; explicit absence replaces its all-firm infeasibility sentinel. Actual thresholds are fixed throughout, so the root test uses zero residual demand. Index and finite-control operations are executable; abstract real comparisons use the exact-comparison primitive of the imported RAM. No real supremum, arbitrary global seed-set minimum or free table operation is used.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, pp. 42–47, Appendix D, Algorithm 2 (p. 44), proof of Lemma 2 (pp. 43–46), proof of Lemma 3 (pp. 46–47)

import Mathlib
import Definitions.Def_TraceAdopt_LPReform_Supplement_NiceDecomposition
import Definitions.Def_TraceAdopt_LPReform_Supplement_RAMIO

set_option autoImplicit false

namespace TraceAdopt.LPReform.Supplement

/-! A residual-demand implementation of the weighted diffusion DP of Appendix D.
Tables store costs and two child-state indices, never global seed sets. A state records
an order, a firm-seed mask and the unmet incoming demand after earlier vertices in the
subtree have contributed. Boundary vertices may still receive help from outside.
The seed mask makes joins valid also for signed costs. All choices are finite folds;
`none` means infeasible and ties retain the first enumerated candidate. -/

abbrev DPVertex (I : Instance) := Fin I.n ⊕ Fin I.m

def dpThreshold (I : Instance) : DPVertex I → ℕ :=
  Sum.elim I.c (fun j => I.θ j - 1)

/-- Directed weight from `u` to `v`, not the reverse. -/
def dpWeight (I : Instance) (u v : DPVertex I) : ℕ :=
  match u, v with
  | .inl i, .inr j => if i ∈ I.e j then 1 else 0
  | .inr j, .inl i => if i ∈ I.e j then I.r j i else 0
  | _, _ => 0

def dpFirm (I : Instance) : DPVertex I → Bool :=
  Sum.elim (fun _ => true) (fun _ => false)

def dpSeedCost (I : Instance) (w : Fin I.n → ℝ) : DPVertex I → ℝ :=
  Sum.elim w (fun _ => 0)

def dpVertexOfCode (I : Instance) (v : ℕ) : Option (DPVertex I) :=
  if h : v < I.n then some (.inl ⟨v, h⟩)
  else if h' : v - I.n < I.m then some (.inr ⟨v - I.n, h'⟩) else none

def dpBag {I : Instance} (D : NiceDecomposition I) (z : Fin D.N) : List (DPVertex I) :=
  (((D.bag z).image dpVertexCode).sort (· ≤ ·)).filterMap (dpVertexOfCode I)

/-- Fixed-length words in lexicographic order; not an enumeration of global seed sets. -/
def dpWords (base : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | b + 1 => (List.range base).flatMap fun a => (dpWords base b).map (a :: ·)

structure DPState where
  residual : List ℕ
  rank : List ℕ
  seed : List ℕ
  deriving DecidableEq, Inhabited

def dpAt {I : Instance} (D : NiceDecomposition I) (z : Fin D.N)
    (xs : List ℕ) (v : DPVertex I) : ℕ := xs.getD ((dpBag D z).idxOf v) 0

/-- Residuals 0..ϑmax, ranks 0..ω′+1, and one extra bit per boundary vertex.
Only firm vertices may be seeds, residuals cannot exceed actual thresholds, and ranks
are distinct. Distinct ranks suffice: simultaneous noninteracting activations can always
be refined into a total order. The added mask changes the state count by at most 2^(ω′+1). -/
def dpStates {I : Instance} (D : NiceDecomposition I) (z : Fin D.N) (q : ℕ) : List DPState :=
  let b := (dpBag D z).length
  (dpWords (varthetaMax I + 1) b).flatMap fun r =>
    (dpWords (q + 2) b).flatMap fun a =>
      (dpWords 2 b).filterMap fun s =>
        if a.Nodup ∧ (dpBag D z).all (fun v =>
            decide (dpAt D z r v ≤ dpThreshold I v) &&
              (dpFirm I v || decide (dpAt D z s v = 0))) then
          some ⟨r, a, s⟩ else none

/-- Contributions from earlier boundary vertices, with the incoming arc orientation. -/
def dpRed {I : Instance} (D : NiceDecomposition I) (z : Fin D.N)
    (s : DPState) (v : DPVertex I) : ℕ :=
  ((dpBag D z).map fun u =>
    if dpAt D z s.rank u < dpAt D z s.rank v then dpWeight I u v else 0).sum

noncomputable def dpBoundaryCost {I : Instance} (D : NiceDecomposition I)
    (w : Fin I.n → ℝ) (z : Fin D.N) (s : DPState) : ℝ :=
  ((dpBag D z).map fun v =>
    if dpAt D z s.seed v = 1 then dpSeedCost I w v else 0).sum

/-- Compare relative orders on the common boundary; numerical ranks need not be equal
when the forgotten vertex is replaced. -/
def dpOrderAgrees {I : Instance} (D : NiceDecomposition I)
    (z c : Fin D.N) (s t : DPState) : Bool :=
  (dpBag D z).all fun u => (dpBag D z).all fun v =>
    if u ∈ D.bag c ∧ v ∈ D.bag c then
      decide ((dpAt D z s.rank u < dpAt D z s.rank v) ↔
        (dpAt D c t.rank u < dpAt D c t.rank v)) else true

structure DPEntry where
  cost : ℝ
  left : ℕ
  right : ℕ

abbrev DPTable := Array (Option DPEntry)
abbrev DPForest := Array DPTable

/-- A strict comparison retains the first minimizer on ties. No empty-minimum default. -/
noncomputable def dpBetter (x y : Option DPEntry) : Option DPEntry :=
  match x, y with
  | none, y => y
  | x, none => x
  | some x, some y => if y.cost < x.cost then some y else some x

noncomputable def dpBest (xs : List (Option DPEntry)) : Option DPEntry :=
  xs.foldl dpBetter none

def dpLookup (F : DPForest) (z i : ℕ) : Option DPEntry :=
  (F[z]?.getD #[])[i]?.getD none

/-- Leaves enumerate boundary firm seeds and orders. Residual demand is actual threshold
minus earlier incoming boundary weights. Boundary feasibility is tested only when a
vertex is forgotten or at the root, since outside contributions are still possible. -/
noncomputable def dpLeaf {I : Instance} (D : NiceDecomposition I)
    (w : Fin I.n → ℝ) (z : Fin D.N) (s : DPState) : Option DPEntry :=
  if (dpBag D z).all (fun v => decide
      (dpAt D z s.residual v = dpThreshold I v - dpRed D z s v)) then
    some ⟨dpBoundaryCost D w z s, 0, 0⟩ else none

/-- At replacement, forgotten `v` has no future neighbours, so its demand must already
be zero unless it is a firm seed. Introduced `u` has no neighbours in the child interior.
Its incoming contribution updates every common vertex that follows it. The contribution
of `v` remains in the residuals after forgetting it. -/
def dpReplaceCompatible {I : Instance} (D : NiceDecomposition I)
    (z : Fin D.N) (u v : DPVertex I) (s t : DPState) : Bool :=
  let c := D.child1 z
  dpOrderAgrees D z c s t &&
    decide (dpAt D c t.seed v = 1 ∨ dpAt D c t.residual v = 0) &&
    (dpBag D z).all (fun x =>
      if x = u then decide (dpAt D z s.residual x = dpThreshold I x - dpRed D z s x)
      else decide (dpAt D z s.seed x = dpAt D c t.seed x ∧
        dpAt D z s.residual x = dpAt D c t.residual x -
          (if dpAt D z s.rank u < dpAt D z s.rank x then dpWeight I u x else 0)))

noncomputable def dpReplace {I : Instance} (D : NiceDecomposition I)
    (w : Fin I.n → ℝ) (q : ℕ) (F : DPForest) (z : Fin D.N)
    (u v : DPVertex I) (s : DPState) : Option DPEntry :=
  dpBest (((dpStates D (D.child1 z) q).zipIdx).map fun (t, j) =>
    if dpReplaceCompatible D z u v s t then
      (dpLookup F (D.child1 z).val j).map fun e =>
        ⟨e.cost + (if dpAt D z s.seed u = 1 then dpSeedCost I w u else 0), j, 0⟩
    else none)

/-- Join residuals combine after correcting the double-counted incoming boundary weight:
`r = max(r₀+r₁+min(red,threshold)−threshold,0)`. Saturation at threshold is essential:
raw `red` can exceed threshold for weighted arcs. Matching seed masks makes the union
cost equal to the sum of child costs minus the boundary seed cost, including negative costs. -/
def dpJoinCompatible {I : Instance} (D : NiceDecomposition I) (z : Fin D.N)
    (s a b : DPState) : Bool :=
  dpOrderAgrees D z (D.child1 z) s a && dpOrderAgrees D z (D.child2 z) s b &&
    (dpBag D z).all (fun v => decide
      (dpAt D z s.seed v = dpAt D (D.child1 z) a.seed v ∧
       dpAt D z s.seed v = dpAt D (D.child2 z) b.seed v ∧
       dpAt D z s.residual v =
         dpAt D (D.child1 z) a.residual v + dpAt D (D.child2 z) b.residual v +
           min (dpRed D z s v) (dpThreshold I v) - dpThreshold I v))

noncomputable def dpJoin {I : Instance} (D : NiceDecomposition I)
    (w : Fin I.n → ℝ) (q : ℕ) (F : DPForest) (z : Fin D.N) (s : DPState) : Option DPEntry :=
  dpBest (((dpStates D (D.child1 z) q).zipIdx).flatMap fun (a, i) =>
    ((dpStates D (D.child2 z) q).zipIdx).map fun (b, j) =>
      if dpJoinCompatible D z s a b then
        match dpLookup F (D.child1 z).val i, dpLookup F (D.child2 z).val j with
        | some x, some y => some ⟨x.cost + y.cost - dpBoundaryCost D w z s, i, j⟩
        | _, _ => none
      else none)

noncomputable def dpNodeTable {I : Instance} (D : NiceDecomposition I)
    (w : Fin I.n → ℝ) (q : ℕ) (F : DPForest) (z : Fin D.N) : DPTable :=
  ((dpStates D z q).map fun s =>
    match D.kind z with
    | .leaf => dpLeaf D w z s
    | .replace u v => dpReplace D w q F z u v s
    | .join => dpJoin D w q F z s).toArray

/-- Actual postorder table evaluation; a later table is computed from the stored earlier
ones. Every table row is an explicit finite fold over local candidates. -/
noncomputable def dpEvaluate {I : Instance} (D : NiceDecomposition I)
    (w : Fin I.n → ℝ) (q : ℕ) : DPForest :=
  (List.finRange D.N).foldl (fun F z => F.push (dpNodeTable D w q F z)) #[]

/-- At actual thresholds the remaining demand must be zero at each nonseed root vertex.
The result stores the chosen root-state index in `left`. -/
noncomputable def dpRoot {I : Instance} (D : NiceDecomposition I)
    (q : ℕ) (F : DPForest) : Option DPEntry :=
  dpBest (((dpStates D D.root q).zipIdx).map fun (s, i) =>
    if (dpBag D D.root).all (fun v => decide
        (dpAt D D.root s.seed v = 1 ∨ dpAt D D.root s.residual v = 0)) then
      (dpLookup F D.root.val i).map (fun e => ⟨e.cost, i, 0⟩) else none)

/-- Reconstruction semantics for backpointers. The RAM implements this by visiting nodes
and marking output bits; list concatenation here specifies the marks, not a free machine
instruction. No global seed sets are copied by table transitions. -/
def dpMarks {I : Instance} (D : NiceDecomposition I) (q : ℕ) (F : DPForest) :
    ℕ → Fin D.N → ℕ → List (DPVertex I)
  | 0, _, _ => []
  | fuel + 1, z, i =>
    match (dpStates D z q)[i]?, dpLookup F z.val i with
    | some s, some e =>
      match D.kind z with
      | .leaf => (dpBag D z).filter (fun v => dpAt D z s.seed v = 1)
      | .replace u _ => dpMarks D q F fuel (D.child1 z) e.left ++
          (if dpAt D z s.seed u = 1 then [u] else [])
      | .join => dpMarks D q F fuel (D.child1 z) e.left ++
          dpMarks D q F fuel (D.child2 z) e.right
    | _, _ => []

def dpReconstruct {I : Instance} (D : NiceDecomposition I) (q : ℕ)
    (F : DPForest) (rootState : ℕ) : Finset (Fin I.n) :=
  ((dpMarks D q F D.N D.root rootState).filterMap fun v =>
    match v with | .inl i => some i | .inr _ => none).toFinset

/-! Memory realization by one fixed, oracle-free program. The decomposition is written by
that program during preparation; it is never supplied with the input. Each table entry
has an infeasibility flag, two backpointers, and one real cost. Tables occupy disjoint
blocks after the input/decomposition. Snapshots certify all rows, not just the root.
The total executed RAM steps include preparation, table evaluation and reconstruction. -/

open MeanCertificates1424.Hardness.Supplement

def dpDecompOffset (I : Instance) : ℕ := I.n + (ramInts I).length + 1

def dpTableStart {I : Instance} (D : NiceDecomposition I) (q : ℕ) : ℕ :=
  dpDecompOffset I + (niceDecompositionInts D q).length

def dpRowAddress {I : Instance} (D : NiceDecomposition I) (q : ℕ)
    (z : Fin D.N) (i : ℕ) : ℕ :=
  dpTableStart D q +
    (((List.finRange D.N).take z.val).map (fun t => 3 * (dpStates D t q).length)).sum + 3 * i

def DPEntryStored (c : Cfg) (addr : ℕ) : Option DPEntry → Prop
  | none => c.imem addr = 0
  | some e => c.imem addr = 1 ∧ c.imem (addr + 1) = e.left ∧
      c.imem (addr + 2) = e.right ∧ c.rmem addr = e.cost

def DPTableStored {I : Instance} (D : NiceDecomposition I) (q : ℕ)
    (F : DPForest) (z : Fin D.N) (c : Cfg) : Prop :=
  ∀ i < (dpStates D z q).length, DPEntryStored c (dpRowAddress D q z i) (dpLookup F z.val i)

/-- Trace-level implementation of the above finite recurrence. `t₀` follows decomposition
preparation, `times z` follows writing table z, and `t₁` follows backpointer reconstruction.
Every configuration is an actual iterate of the same fixed RAM program on the original
instance input. Width, decomposition and all tables are produced inside the charged run. -/
def RealizesDiffusionDP (P : Program) (I : Instance) (w : Fin I.n → ℝ)
    (D : NiceDecomposition I) (q T : ℕ) (fin : Cfg) : Prop :=
  let atTime := fun t => (MeanCertificates1424.Hardness.Supplement.step P (fun _ _ => 0))^[t]
    (initCfg (ramInts I) (ramReals I w))
  let F := dpEvaluate D w q
  ∃ (t₀ t₁ : ℕ) (times : Fin D.N → ℕ) (root : DPEntry),
    t₀ ≤ t₁ ∧ t₁ ≤ T ∧ atTime t₁ = fin ∧ Halted P fin ∧
    (∀ j < (niceDecompositionInts D q).length,
      (atTime t₀).imem (dpDecompOffset I + j) = (niceDecompositionInts D q).getD j 0) ∧
    (∀ z, t₀ ≤ times z ∧ times z ≤ t₁ ∧ DPTableStored D q F z (atTime (times z))) ∧
    (∀ a b, a.val < b.val → times a < times b) ∧
    (∀ z, DPTableStored D q F z fin) ∧
    dpRoot D q F = some root ∧
    outSeeds I.n fin = dpReconstruct D q F root.left ∧
    fin.rmem (dpDecompOffset I - 1) = root.cost

end TraceAdopt.LPReform.Supplement


