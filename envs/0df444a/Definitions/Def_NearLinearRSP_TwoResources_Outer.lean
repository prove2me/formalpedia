-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Outer
-- name    : NearLinearRSP_TwoResources_Outer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:00.028121+00:00
-- url     : https://prove2.me/theorems/5d6b1874-607b-494a-81c4-fc58da2d5333
-- title:
--   Boundary shortest-path trees, normalized guesses and compact all-target answers
-- statement:
--   For a full RSP input and $0<\varepsilon<1$, use inner accuracy $\delta=\varepsilon/4$. Ordinary queue-based Dijkstra computations are defined on the zero-length subgraph with cost weights and on the zero-cost subgraph with length weights. Their parents are recorded before witness paths are read. The first tree handles every target admitting a zero-length path within budget. When $C=0$, the second tree gives exact shortest paths on zero-cost edges.
--
--   If a positive length exists, write $a$ and $b$ for the smallest and largest positive edge lengths. The normalized grid is
--   $$
--   L_r=a(1+\delta)^r,\qquad 0\le r\le\min\{k:n b\le a(1+\delta)^k\}.
--   $$
--   No positive-length grid is formed when all lengths are zero. Positive-budget inner calls use the specified queue-built tables. Each remaining target selects its least accepted grid index and retains that table. Its reported upper distance is $(1+\delta)L_r$, and its path is the deterministic retrieval from the same table. Zero-length answers report zero; zero-budget answers report the exact shortest-tree distance. An absent answer is explicit.
--
--   This is a compact all-target specification, including the source and isolated targets, rather than simultaneous materialization of every path. Tree and table correctness remain mathematical claims to prove; the definitions also permit explicit failure of path retrieval on bad inputs. Stable queue ties use the fixed input ordering of active vertices; equal tick choices use length.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), pp.3–4 and 6, outer framework; p.9, Proof of Theorem 1; p.3 zero-weight extension; pp.10–12 deterministic retrieval

import Definitions.Def_NearLinearRSP_TwoResources_Retrieval

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

attribute [local instance] Classical.propDecidable

structure TreeCell where
  distance : Option ℝ
  parent : Option ℕ
  rank : ℕ

abbrev ShortestTree := ℕ → TreeCell

/-- None is positive infinity in a shortest-path queue. -/
noncomputable def distanceLess (x y : Option ℝ) : Bool :=
  match x, y with
  | some a, some b => decide (a < b)
  | some _, none => true
  | _, _ => false

structure TreeQueue where
  tree : ShortestTree
  queue : List ℕ
  rank : ℕ

noncomputable def treeRelax (_I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ) : TreeQueue :=
  if e.1 = u ∧ e.1 ≠ e.2 ∧ e.2 ∈ S.queue ∧ allow e.1 e.2 then
    match (S.tree u).distance with
    | none => S
    | some d =>
      let candidate := some (d + w e.1 e.2)
      if distanceLess candidate (S.tree e.2).distance then
        { S with tree := Function.update S.tree e.2 ⟨candidate, some u, 0⟩ }
      else S
  else S

noncomputable def treePop (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) : TreeQueue :=
  match S.queue with
  | [] => S
  | v :: _ =>
    let u := S.queue.foldl (fun x y =>
      if distanceLess (S.tree y).distance (S.tree x).distance then y else x) v
    let S' : TreeQueue := {
      tree := Function.update S.tree u { S.tree u with rank := S.rank }
      queue := S.queue.erase u
      rank := S.rank + 1 }
    I.graph.edges.foldl (treeRelax I allow w u) S'

/-- Ordinary Dijkstra with fixed ties; no correctness or complexity is built into this definition. -/
noncomputable def shortestTree (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) : ShortestTree :=
  ((List.range (activeVertices I).length).foldl (fun S _ => treePop I allow w S)
    { tree := fun v => ⟨if v = I.source then some 0 else none, none, 0⟩
      queue := activeVertices I
      rank := 0 }).tree

noncomputable def zeroLengthTree (I : Instance) : ShortestTree :=
  shortestTree I (fun u v => decide (I.length u v = 0)) (fun u v => I.cost u v)
noncomputable def zeroBudgetTree (I : Instance) : ShortestTree :=
  shortestTree I (fun u v => decide (I.cost u v = 0)) (fun u v => I.length u v)

noncomputable def treePath (I : Instance) (T : ShortestTree) : ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, v, P => if v = I.source then some P else none
  | k + 1, v, P => if v = I.source then some P else
      (T v).parent.bind (fun u => treePath I T k u (u :: P))

noncomputable def readTreePath (I : Instance) (T : ShortestTree) (t : ℕ) : Option (List ℕ) :=
  match (T t).distance with
  | none => none
  | some _ => treePath I T (activeVertices I).length t [t]

/-- Counted-loop mathematical specification; no real-to-natural conversion instruction is used. -/
noncomputable def firstCrossing (a r top : ℝ) : ℕ :=
  if h : ∃ k : ℕ, top ≤ a * r ^ k then Nat.find h else 0

noncomputable def geometricGuesses (I : Instance) (ε : ℝ) : List ℝ :=
  if (positiveLengths I).isEmpty then [] else
    (List.range (firstCrossing (firstPositiveLength I) (1 + ε / 4)
      (I.graph.n * largestLength I) + 1)).map
        (fun r => firstPositiveLength I * (1 + ε / 4) ^ r)

/-- Only normalized positive-threshold inner calls are made. Zero cases are separate trees. -/
noncomputable def outerInputs (I : Instance) (ε : ℝ) : List InnerInput :=
  if h : 0 < ε ∧ ε < 1 ∧ 0 < (I.budget : ℝ) then
    (geometricGuesses I ε).filterMap (fun L =>
      if hL : 0 < L then some
        { I := I
          δ := ε / 4
          accuracy_pos := by linarith [h.1]
          accuracy_lt_one := by linarith [h.2.1]
          L := L
          length_pos := hL
          budget_pos := h.2.2 }
      else none)
  else []

inductive AnswerBranch where
  | absent
  | zeroLength
  | zeroBudget
  | inner (r : ℕ)
  deriving DecidableEq

noncomputable def answerBranch (I : Instance) (ε : ℝ) (t : ℕ) : AnswerBranch :=
  if t = I.source then .zeroLength else
  match (zeroLengthTree I t).distance with
  | some d => if d ≤ I.budget then .zeroLength else
      if I.budget = 0 then
        if (zeroBudgetTree I t).distance.isSome then .zeroBudget else .absent
      else
        match ((List.range (outerInputs I ε).length).find?
          (fun r => ((outerInputs I ε)[r]?).any (fun A => decide (accepted A t)))) with
        | some r => .inner r
        | none => .absent
  | none =>
      if I.budget = 0 then
        if (zeroBudgetTree I t).distance.isSome then .zeroBudget else .absent
      else
        match ((List.range (outerInputs I ε).length).find?
          (fun r => ((outerInputs I ε)[r]?).any (fun A => decide (accepted A t)))) with
        | some r => .inner r
        | none => .absent

noncomputable def answerDistance (I : Instance) (ε : ℝ) (t : ℕ) : Option ℝ :=
  match answerBranch I ε t with
  | .absent => none
  | .zeroLength => some 0
  | .zeroBudget => (zeroBudgetTree I t).distance
  | .inner r => ((outerInputs I ε)[r]?).map (fun A => (1 + A.δ) * A.L)

noncomputable def answerPath (I : Instance) (ε : ℝ) (t : ℕ) : Option (List ℕ) :=
  match answerBranch I ε t with
  | .absent => none
  | .zeroLength => readTreePath I (zeroLengthTree I) t
  | .zeroBudget => readTreePath I (zeroBudgetTree I) t
  | .inner r => ((outerInputs I ε)[r]?).bind (fun A => (retrieve A t).map (·.path))

end NearLinearRSP.TwoResources


