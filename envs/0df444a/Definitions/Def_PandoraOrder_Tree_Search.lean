-- Prove2me | Definitions.Def_PandoraOrder_Tree_Search
-- name    : PandoraOrder_Tree_Search
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:00:04.310043+00:00
-- url     : https://prove2.me/theorems/cff00b52-18f0-45da-99f2-941f3448109b
-- title:
--   Stable head merge, bottom-up tree preprocessing and strict threshold search
-- statement:
--   Merge compares the accessible heads of two annotated lists, takes the larger threshold, and repeats. Smaller labels win equal-threshold ties. It preserves each list's internal order, even when a child's threshold is larger than its parent's. It never globally sorts all vertices.
--
--   Tree preprocessing repeatedly selects the smallest unprocessed vertex whose children have all been processed. It merges its completed child lists in increasing child-label order, computes the threshold of the current vertex prefixed to that merge, and stores that prefixed list with its descendants' existing annotations. There are $n$ such steps; failure to find a ready vertex is explicit. This ready-vertex scan implements the source's bottom-up queue schedule with its scan cost included. The printed assignment $[b_j]+L$ in Algorithm 2 is read as $[b_\ell]+L$, prefixing the vertex just processed; the printed index is undefined on a leaf.
--
--   The line and union-of-lines preprocessors run the same line program. Actual search begins at the specified incumbent and selects the legal unopened box with largest threshold. It opens precisely when the incumbent is strictly below that threshold, updates the incumbent by the revealed reward, and otherwise stops. Thus the operational rule stops at equality, as in Algorithm 1, despite Theorem 1's different prose. Empty accessible sets stop. The auxiliary continuation ties of Claims 2–3 do not change this rule.
--
--   The module gives both the uncosted mathematical rollout and its costed implementation with explicit finite availability checks and table scans. Its reward-independent greedy order is separate from the realized stopping prefix. No feasibility or optimality assertion is an input field. An absent annotation returns zero only as a total fallback; the theorem contracts require complete annotations.
-- source:
--   Boodaghians et al., arXiv:2002.06968v2, Algorithm 1, p. 6; §3.2, p. 9; §3.3 and Algorithm 2, pp. 11–12 (PDF pp. 6, 9, 11–12); https://arxiv.org/abs/2002.06968v2

import Definitions.Def_PandoraOrder_Tree_LineAlgorithm

namespace PandoraOrder.Tree

/-- Larger thresholds have priority; at equality smaller input labels win. -/
noncomputable def before {n : ℕ} (a b : Fin n × ℝ) : Calc Bool := do
  let za ← readCell a.2
  let zb ← readCell b.2
  if ← less zb za then pure true
  else if ← less za zb then pure false
  else do charge 1 1; pure (decide (a.1.val ≤ b.1.val))

/-- Head merge, preserving the internal order of both lines. Fuel is their total
length, never a bound dependent on the numerical size of rewards. -/
noncomputable def mergeFuel {n : ℕ} : ℕ → Annotated n → Annotated n → Calc (Annotated n)
  | 0, _, _ => pure []
  | t + 1, A, B => do
      charge 1 16
      match A, B with
      | [], _ => pure B
      | _, [] => pure A
      | a :: as, b :: bs =>
          if ← before a b then
            let out ← mergeFuel t as B
            consCell 2 a out
          else
            let out ← mergeFuel t A bs
            consCell 2 b out

noncomputable def mergeLines {n : ℕ} (A B : Annotated n) : Calc (Annotated n) := do
  charge (A.length + B.length + 1) 0
  mergeFuel (A.length + B.length) A B

/-- Association-list lookup, with every traversed cell charged. -/
def lookupLine {n : ℕ} (b : Fin n) : List (Fin n × Annotated n) → Calc (Annotated n)
  | [] => pure []
  | (a, L) :: rest => do
      charge 2 1
      if a = b then pure L else lookupLine b rest

def children {n : ℕ} (T : HarelTarjan.Compressed.RootedTree (Fin n)) (b : Fin n) :
    Calc (List (Fin n)) := do
  let vertices ← finCells n
  let rev ← foldCells (fun cs a => do
    let p ← readCell (T.parent a)
    charge 2 2
    if a ≠ T.root ∧ p = b then consCell 1 a cs else pure cs) [] vertices
  reverseCells 1 rev

def readyVertex {n : ℕ} (T : HarelTarjan.Compressed.RootedTree (Fin n))
    (done : List (Fin n)) (b : Fin n) : Calc Bool := do
  if ← memberCell b done then pure false else
    let cs ← children T b
    foldCells (fun ok c => do
      let yes ← memberCell c done
      charge 1 1
      pure (ok && yes)) true cs

def firstReady {n : ℕ} (T : HarelTarjan.Compressed.RootedTree (Fin n))
    (done : List (Fin n)) : List (Fin n) → Calc (Option (Fin n))
  | [] => pure none
  | b :: bs => do
      charge 1 16
      if ← readyVertex T done b then pure (some b) else firstReady T done bs

/-- A bottom-up implementation of Algorithm 2. The deterministic ready-vertex scan
replaces its queue; children are merged in increasing label order. The prefix is
[b_l], the unambiguous intended reading of the printed [b_j]. -/
noncomputable def treeSteps {n : ℕ} (I : Instance n)
    (T : HarelTarjan.Compressed.RootedTree (Fin n)) :
    ℕ → List (Fin n) → List (Fin n × Annotated n) → Calc (List (Fin n × Annotated n))
  | 0, _, table => pure table
  | t + 1, done, table => do
      charge 1 16
      let vertices ← finCells n
      let next ← firstReady T done vertices
      match next with
      | none => failure
      | some b =>
          let cs ← children T b
          let merged ← foldCells (fun L c => do
            let child ← lookupLine c table
            mergeLines L child) [] cs
          let labels ← mapCells 1 (fun bz => readCell bz.1) merged
          let z ← computeThreshold I b labels
          let new ← consCell 2 (b, z) merged
          let table' ← consCell 2 (b, new) table
          let done' ← consCell 1 b done
          treeSteps I T t done' table'

noncomputable def treeProgram {n : ℕ} (I : Instance n)
    (T : HarelTarjan.Compressed.RootedTree (Fin n)) : Calc (Annotated n) := do
  charge (inputSize I + 3 * n + 1) (2 * inputSize I + 2 * n + 1)
  let table ← treeSteps I T n [] []
  lookupLine T.root table

noncomputable def unionProgram {n : ℕ} (I : Instance n)
    (Ls : List (List (Fin n))) : Calc (Annotated n) := do
  charge (inputSize I + Ls.length + 1) (2 * inputSize I + Ls.length + 1)
  foldCells (fun A L => do
    let (_, B) ← lineProgram I L
    mergeLines A B) [] Ls

noncomputable def linePreprocess {n : ℕ} (I : Instance n)
    (L : List (Fin n)) : Calc (Annotated n) := do
  charge (inputSize I + L.length + 1) (2 * inputSize I + L.length + 1)
  let (_, ann) ← lineProgram I L
  pure ann

/-- The threshold attached to a box; absence is totalized by zero. Correctness
contracts below require exactly one occurrence of every relevant box. -/
def annotation {n : ℕ} (A : Annotated n) (b : Fin n) : ℝ :=
  ((A.find? (fun bz => bz.1 = b)).map Prod.snd).getD 0

/-- Pure, uncosted priority selection for the behavioral policy specification. -/
noncomputable def bestAvailable {n : ℕ} (F : Constraint n) (z : Fin n → ℝ)
    (opened : List (Fin n)) : Option (Fin n) := by
  classical
  exact (List.finRange n).foldl (fun best b =>
    if b ∉ opened ∧ F opened b then
      match best with
      | none => some b
      | some a => if z a < z b then some b else some a
    else best) none

/-- Algorithm 1 uses the strict test, hence stops at equality, including at zero. -/
noncomputable def thresholdPolicy {n : ℕ} (F : Constraint n) (z : Fin n → ℝ)
    (x : ℝ := 0) : Policy n := by
  classical
  exact fun h =>
    let incumbent := h.foldl (fun y br => max y br.2) x
    pureAction (match bestAvailable F z (h.map Prod.fst) with
      | none => none
      | some b => if incumbent < z b then some b else none)

/-- Reward-independent greedy order. Stopping the policy truncates this list. -/
noncomputable def greedyOrder {n : ℕ} (F : Constraint n) (z : Fin n → ℝ) :
    ℕ → List (Fin n) → List (Fin n)
  | 0, opened => opened
  | t + 1, opened => match bestAvailable F z opened with
      | none => opened
      | some b => greedyOrder F z t (opened ++ [b])

/-- Actual deterministic execution on a realized reward vector. -/
noncomputable def rollout {n : ℕ} (F : Constraint n) (z : Fin n → ℝ)
    (rewards : Fin n → ℝ) : ℕ → List (Fin n) → ℝ → List (Fin n)
  | 0, opened, _ => opened
  | t + 1, opened, x => match bestAvailable F z opened with
      | none => opened
      | some b => if x < z b then
          rollout F z rewards t (opened ++ [b]) (max x (rewards b)) else opened

/-- Finite checks for the three source constraints; no feasibility oracle. -/
def treeAvailable {n : ℕ} (T : HarelTarjan.Compressed.RootedTree (Fin n))
    (opened : List (Fin n)) (b : Fin n) : Calc Bool := do
  if ← memberCell b opened then pure false else
    let p ← readCell (T.parent b)
    charge 1 1
    if b = T.root then pure true else memberCell p opened

def lineAvailable {n : ℕ} (L : List (Fin n)) (opened : List (Fin n))
    (b : Fin n) : Calc Bool := do
  charge (L.length + opened.length + 2) 1
  pure (decide (L[opened.length]? = some b))

def unionAvailable {n : ℕ} (Ls : List (List (Fin n)))
    (opened : List (Fin n)) (b : Fin n) : Calc Bool := do
  if ← memberCell b opened then pure false else
    foldCells (fun found L => do
      let (_, yes) ← foldCells (fun (st : Bool × Bool) a => do
        let seen ← memberCell a opened
        charge 3 3
        pure (st.1 && seen, st.2 || (st.1 && decide (a = b)))) (true, false) L
      charge 1 1
      pure (found || yes)) false Ls

def lookupThreshold {n : ℕ} (A : Annotated n) (b : Fin n) : Calc ℝ := do
  let out ← foldCells (fun (v : Option ℝ) bz => do
    charge 2 1
    if v.isSome then pure v else if bz.1 = b then pure (some bz.2) else pure none) none A
  pure (out.getD 0)

noncomputable def bestProgram {n : ℕ} (available : List (Fin n) → Fin n → Calc Bool)
    (A : Annotated n) (opened : List (Fin n)) : Calc (Option (Fin n × ℝ)) := do
  let bs ← finCells n
  foldCells (fun best b => do
    if ← available opened b then
      let z ← lookupThreshold A b
      match best with
      | none => pure (some (b, z))
      | some a => if ← before (b, z) a then pure (some (b, z)) else pure best
    else pure best) none bs

noncomputable def runProgram {n : ℕ}
    (available : List (Fin n) → Fin n → Calc Bool)
    (A : Annotated n) (rewards : Fin n → ℝ) :
    ℕ → List (Fin n) → ℝ → Calc (List (Fin n))
  | 0, opened, _ => pure opened
  | t + 1, opened, x => do
      charge 1 16
      let next ← bestProgram available A opened
      match next with
      | none => pure opened
      | some (b, z) =>
          if ← less x z then
            let r ← readCell (rewards b)
            let y ← maximum x r
            let singleton ← consCell 1 b []
            let opened' ← appendCells 1 opened singleton
            runProgram available A rewards t opened' y
          else pure opened

end PandoraOrder.Tree


