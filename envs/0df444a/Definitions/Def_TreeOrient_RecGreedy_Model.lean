-- Prove2me | Definitions.Def_TreeOrient_RecGreedy_Model
-- name    : TreeOrient_RecGreedy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:48.589239+00:00
-- url     : https://prove2.me/theorems/1601dee4-23b0-4396-a745-20228293f89c
-- title:
--   §1.3 and §2 — submodular tree orienteering and corrected recursive greedy algorithms
-- statement:
--   A submodular tree orienteering instance consists of a finite directed graph on $n$ vertices, a root $r^*$, nonnegative integral edge costs $c$, a budget $B$, and an integer-valued vertex-set reward $f$. A rooted arborescence selects reachable vertices while spending at most $B$. The marginal reward over an existing set $X$ is
--
--   $$f_X(T)=f(V(T)\cup X)-f(X).$$
--
--   This module defines arborescences, cost, compatibility with responsibilities $Y$, the corrected recursive greedy algorithm $RG(r,Y,B,X,i)$, its grouped $s$-level version, binary search over budgets, and a step count that includes recursive calls, evaluated candidates, and grouped-base enumeration. The model supplies the common objects used in the approximation and running-time statements.
--
--   **Formalization Note** Vertices are `Fin n`; edge sets may have zero-cost arcs. $V(T)$ includes the root. The oracle is natural-valued, and marginal rewards are computed in the reals. Budget guesses include zero; an unsatisfied responsibility gives an infeasible result rather than an empty tree. Grouped depth one searches every feasible arborescence with at most $(3/2)^s$ non-root vertices, and its step count charges each enumerated edge tuple. The output is an `Option` edge set and a step count. The original page's metric closure is not required for these statements.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, pp. 4–9 (PDF 5–10), §1.3, §2.1–2.3, Algorithms 1–2

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace TreeOrient.RecGreedy

abbrev Edges (n : ℕ) := Finset (Fin n × Fin n)

structure Inst (n : ℕ) where
  root : Fin n
  c : Fin n → Fin n → ℕ
  B : ℕ
  f : Finset (Fin n) → ℕ

def IsMonotone {n : ℕ} (f : Finset (Fin n) → ℕ) : Prop :=
  ∀ S T, S ⊆ T → f S ≤ f T

def verts {n : ℕ} (r : Fin n) (T : Edges n) : Finset (Fin n) :=
  insert r (T.image Prod.fst ∪ T.image Prod.snd)

def cost {n : ℕ} (c : Fin n → Fin n → ℕ) (T : Edges n) : ℕ :=
  ∑ e ∈ T, c e.1 e.2

def fX {n : ℕ} (f : Finset (Fin n) → ℕ) (X : Finset (Fin n))
    (r : Fin n) (T : Edges n) : ℝ :=
  (f (verts r T ∪ X) : ℝ) - (f X : ℝ)

def Reaches {n : ℕ} (T : Edges n) (r w : Fin n) : Prop :=
  Relation.ReflTransGen (fun a b => (a, b) ∈ T) r w

def IsArbo {n : ℕ} (r : Fin n) (A : Edges n) : Prop :=
  (∀ e ∈ A, e.2 ≠ r) ∧
  (∀ e ∈ A, ∀ e' ∈ A, e.2 = e'.2 → e = e') ∧
  ∀ w ∈ verts r A, Reaches A r w

def Feasible {n : ℕ} (c : Fin n → Fin n → ℕ) (r : Fin n)
    (Y : Finset (Fin n)) (B : ℕ) (T : Edges n) : Prop :=
  (∀ w ∈ verts r T, Reaches T r w) ∧ cost c T ≤ B ∧ Y ⊆ verts r T

def Compatible {n : ℕ} (c : Fin n → Fin n → ℕ) (r : Fin n)
    (Y : Finset (Fin n)) (B : ℕ) (cap : ℝ) (A : Edges n) : Prop :=
  IsArbo r A ∧ Y ⊆ verts r A ∧ (A.card : ℝ) ≤ cap ∧ cost c A ≤ B

noncomputable def capImp (s i : ℕ) : ℝ := (3 / 2 : ℝ) ^ (s * i)

inductive Mode
  | enum
  | bsearch (U : ℕ)
  deriving DecidableEq

noncomputable def leafPlans {n : ℕ} : ℕ → Fin n → Finset (Fin n) →
    List (List (Fin n × Finset (Fin n)))
  | 0, r, Y => [[(r, Y)]]
  | s + 1, r, Y =>
      (List.finRange n).flatMap fun v =>
        Y.powerset.toList.flatMap fun S =>
          (leafPlans s r ((S ∪ {v}) \ {r})).flatMap fun L =>
            (leafPlans s v (Y \ (S ∪ {v}))).map fun R => L ++ R

/-- Least successful budget on an interval, assuming the probe is monotone. The second
component counts all recursive probe calls. -/
def bsearchAux (probe : ℕ → Bool × ℕ) : ℕ → ℕ → ℕ → Option ℕ × ℕ
  | 0, _, _ => (none, 0)
  | fuel + 1, lo, hi =>
      if hi < lo then (none, 0)
      else
        let mid := lo + (hi - lo) / 2
        let (ok, t) := probe mid
        if ok then
          if mid = lo then (some mid, t)
          else
            let (b, t') := bsearchAux probe fuel lo (mid - 1)
            (b.orElse (fun _ => some mid), t + t')
        else
          let (b, t') := bsearchAux probe fuel (mid + 1) hi
          (b, t + t')

def bsearch (probe : ℕ → Bool × ℕ) (lo hi : ℕ) : Option ℕ × ℕ :=
  bsearchAux probe (hi + 1 - lo) lo hi

/-- Solve the leaves of one structural guess in order. An earlier leaf receives an explicitly
guessed budget; the final leaf receives all remaining budget. -/
noncomputable def runPlan {n : ℕ} (I : Inst n) (mode : Mode)
    (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ) :
    List (Fin n × Finset (Fin n)) → Finset (Fin n) → ℕ → Edges n → List (Edges n) × ℕ
  | [], _, _, _ => ([], 0)
  | [(r, Y)], X, Brem, acc =>
      let (o, t) := sub r Y Brem X
      (o.toList.map (fun T => acc ∪ T), t)
  | (r, Y) :: tail, X, Brem, acc =>
      match mode with
      | .enum =>
          (List.range (Brem + 1)).foldl (fun (cands, steps) b =>
            let (o, t) := sub r Y b X
            match o with
            | none => (cands, steps + t)
            | some T =>
                let (more, t') := runPlan I mode sub tail (X ∪ verts r T)
                  (Brem - b) (acc ∪ T)
                (cands ++ more, steps + t + t')) ([], 0)
      | .bsearch U =>
          (List.range (U + 1)).foldl (fun (cands, steps) u =>
            let probe := fun b =>
              let (o, t) := sub r Y b X
              match o with
              | none => (false, t)
              | some T => (decide ((u : ℝ) ≤ fX I.f X r T), t + 1)
            let (ob, probes) := bsearch probe 0 Brem
            match ob with
            | none => (cands, steps + probes)
            | some b =>
                let (o, t) := sub r Y b X
                match o with
                | none => (cands, steps + probes + t)
                | some T =>
                    let (more, t') := runPlan I mode sub tail (X ∪ verts r T)
                      (Brem - b) (acc ∪ T)
                    (cands ++ more, steps + probes + t + t')) ([], 0)

noncomputable def chooseBest {n : ℕ} (f : Finset (Fin n) → ℕ) (X : Finset (Fin n))
    (r : Fin n) (initial : Option (Edges n)) (candidates : List (Edges n)) :
    Option (Edges n) × ℕ :=
  candidates.foldl (fun (incumbent, steps) T =>
    let next := match incumbent with
      | none => some T
      | some old => if fX f X r old < fX f X r T then some T else incumbent
    (next, steps + 1)) (initial, 0)

/-- The one-level recursion used at the leaves of a grouped call. -/
noncomputable def rgBasic {n : ℕ} (I : Inst n) (mode : Mode) :
    ℕ → Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ
  | 0, _, _, _, _ => (none, 1)
  | i + 1, r, Y₀, B, X =>
      let Y := Y₀.erase r
      if capImp 1 (i + 1) < (Y.card : ℝ) then (none, 1)
      else if i = 0 then
        if Y = ∅ then
          let candidates := (List.finRange n).filterMap fun v =>
            if v = r || B < I.c r v then none else some ({(r, v)} : Edges n)
          let (o, _) := chooseBest I.f X r (some ∅) candidates
          (o, 1 + n)
        else
          let o := match Y.toList with
            | [v] => if I.c r v ≤ B then some ({(r, v)} : Edges n) else none
            | _ => none
          (o, 1 + n)
      else
        let initial : Option (Edges n) := if Y = ∅ then some ∅ else none
        let (best, steps) := (leafPlans 1 r Y).foldl (fun (best, steps) plan =>
          let (candidates, t) := runPlan I mode (rgBasic I mode i) plan X B ∅
          let (best', evals) := chooseBest I.f X r best candidates
          (best', steps + t + evals)) (initial, 1)
        (best, steps)
  termination_by i => i

/-- Enumerate every edge set with at most q edges by enumerating ordered edge tuples.
The list also records duplicates, since every tuple is a separate candidate considered. -/
noncomputable def edgeCandidates (n q : ℕ) : List (Edges n) :=
  (List.range (q + 1)).flatMap fun m =>
    ((Finset.univ : Finset (Fin m → Fin n × Fin n)).toList).map fun g =>
      (Finset.univ : Finset (Fin m)).image g

/-- Group s levels of recursive guesses. At grouped depth one, expand s - 1 levels and
choose the best feasible arborescence of the source's base-level size cap. -/
noncomputable def rg {n : ℕ} (I : Inst n) (s : ℕ) (mode : Mode) :
    ℕ → Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ
  | 0, _, _, _, _ => (none, 1)
  | i + 1, r, Y₀, B, X =>
      let Y := Y₀.erase r
      if capImp s (i + 1) < (Y.card : ℝ) then (none, 1)
      else if i = 0 then
        if s = 1 then rgBasic I mode 1 r Y B X
        else
          let candidates := edgeCandidates n (Nat.floor (capImp s 1))
          let initial : Option (Edges n) := if Y = ∅ then some ∅ else none
          let (best, steps) := candidates.foldl (fun (best, steps) T => by
            classical
            exact if IsArbo r T ∧ Y ⊆ verts r T ∧ cost I.c T ≤ B then
              let (best', _) := chooseBest I.f X r best [T]
              (best', steps + 1)
            else (best, steps + 1)) (initial, 1)
          (best, steps)
      else
        let initial : Option (Edges n) := if Y = ∅ then some ∅ else none
        let (best, steps) := (leafPlans s r Y).foldl (fun (best, steps) plan =>
          let (candidates, t) := runPlan I mode (rg I s mode i) plan X B ∅
          let (best', evals) := chooseBest I.f X r best candidates
          (best', steps + t + evals)) (initial, 1)
        (best, steps)
  termination_by i => i

def dOf (k : ℕ) : ℕ := 2 * Nat.clog 2 k

noncomputable def sOf (ε : ℝ) (k : ℕ) : ℕ :=
  max 1 ⌈ε * Real.logb 2 (Real.logb 2 k)⌉₊

def depthOf (s d : ℕ) : ℕ := (d + s - 1) / s

noncomputable def stoAlg {n : ℕ} (I : Inst n) (a : ℕ) (ε : ℝ) (k : ℕ) :
    Option (Edges n) × ℕ :=
  let s := sOf ε k
  rg I s (.bsearch (n ^ a)) (depthOf s (dOf k)) I.root ∅ I.B ∅

end TreeOrient.RecGreedy


