-- Prove2me | Definitions.Def_ProportionalTSP_Exact_DP
-- name    : ProportionalTSP_Exact_DP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:50.334501+00:00
-- url     : https://prove2.me/theorems/ed290953-0e97-44c3-b46f-e5fcecfdb906
-- title:
--   Restricted Held–Karp recurrence with predecessor paths
-- statement:
--   Stored states are $(U,v)$ with $U\in\mathcal C(w)$, $s\in U$, $v\in U\setminus\{s\}$, together with the exceptional initial state $(\{s\},s)$. Entries are optional predecessor paths. Initially only $[s]$ is reachable.
--
--   In increasing set size, the finite recurrence considers every simple available-edge extension $(u,x_1,\ldots,x_t)$ with $1\le t\le3$ and all appended vertices outside $U$, then performs
--   $$DP(U\cup\{x_1,\ldots,x_t\},x_t)\gets\min(DP(\cdot),DP(U,u)+w(P)).$$
--   The final answer closes a full path by an original edge to $s$ and retains its edge set. This recurrence is independent of the optimization target: it never tests whether a tour is globally optimal. A separate uniform implementation specification charges a finite program with output equal to this recurrence.
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), §4, equation (4.1), and Proposition 4.1, PDF p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Programs

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

def words {X : Type} (xs : List X) : ℕ → List (List X)
  | 0 => [[]]
  | t+1 => xs.flatMap (fun x => (words xs t).map (x :: ·))

def pathCost {V : Type} (w : Sym2 V → ℝ) (xs : List V) : ℝ :=
  ((xs.zip (xs.drop 1)).map (fun e => w s(e.1,e.2))).sum

def AvailablePath {V : Type} (G : SimpleGraph V) (xs : List V) : Prop :=
  ∀ e ∈ xs.zip (xs.drop 1), G.Adj e.1 e.2

def Stored {V : Type} [DecidableEq V] (family : Finset (Finset V))
    (s : V) (U : Finset V) (v : V) : Prop :=
  (U = {s} ∧ v = s) ∨ (U ∈ family ∧ s ∈ U ∧ v ∈ U ∧ v ≠ s)

abbrev DPTable (V : Type) := Finset V → V → Option (List V)

def dpInitial {V : Type} [DecidableEq V] (s : V) : DPTable V :=
  fun U v => if U = {s} ∧ v = s then some [s] else none

/-- One instance of (4.1); stored paths carry the predecessor information. -/
def dpUpdate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (family : Finset (Finset V))
    (s : V) (U : Finset V) (u : V) (xs : List V) (D : DPTable V) : DPTable V :=
  match D U u, xs.getLast? with
  | some priorPath, some v =>
    let U' := U ∪ xs.toFinset
    if 1 ≤ xs.length ∧ xs.length ≤ 3 ∧ xs.Nodup ∧
        (∀ x ∈ xs, x ∉ U) ∧ AvailablePath G (u :: xs) ∧ Stored family s U' v then
      let candidate := priorPath ++ xs
      let best := match D U' v with
        | none => candidate
        | some old => if pathCost w old ≤ pathCost w candidate then old else candidate
      fun W z => if W = U' ∧ z = v then some best else D W z
    else D
  | _, _ => D

/-- Every stored set, sorted by cardinality, plus the exceptional start set. -/
def dpSetOrder {V : Type} [Fintype V] [DecidableEq V]
    (vertices : List V) (family : Finset (Finset V)) (s : V) : List (Finset V) :=
  (insert {s} family).toList.mergeSort (fun U W => decide
    (U.card < W.card ∨ (U.card = W.card ∧
      (∑ v ∈ U, 2 ^ vertices.idxOf v) ≤ (∑ v ∈ W, 2 ^ vertices.idxOf v))))

def restrictedDP {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (vertices : List V)
    (family : Finset (Finset V)) (s : V) :
    Option (Finset (Sym2 V)) :=
  let extensions := [1,2,3].flatMap (words vertices)
  let D := (dpSetOrder vertices family s).foldl (fun D U =>
    vertices.foldl (fun D u => if Stored family s U u then
      extensions.foldl (fun D xs => dpUpdate G w family s U u xs D) D else D) D) (dpInitial s)
  let finals := vertices.filterMap (fun v =>
    if G.Adj v s then (D Finset.univ v).map cycleEdges else none)
  argminList (· ≤ ·) (tourCost w) finals

def vertexList (m k : ℕ) : List (Vertex m k) :=
  (List.finRange m).map Sum.inl ++ (List.finRange k).map Sum.inr

/-- Supplied-R input reindexes the sum type by listing L before R, without changing edges. -/
def sectionInput {m k : ℕ} (G : SimpleGraph (Vertex m k))
    (w : Sym2 (Vertex m k) → ℝ) (s : Fin k) : RAM.Input ℝ where
  naturals := [m,k,s.val] ++
    (vertexList m k).flatMap (fun x =>
      (vertexList m k).map (fun y => if G.Adj x y then 1 else 0))
  values := (vertexList m k).flatMap (fun x =>
    (vertexList m k).map (fun y => w s(x,y)))

/-- Output edge sets are encoded by the same ordered L-then-R matrix convention. -/
def sectionTourCode {m k : ℕ} (H : Finset (Sym2 (Vertex m k))) : List ℕ :=
  (vertexList m k).flatMap (fun x =>
    (vertexList m k).map (fun y => if s(x,y) ∈ H then 1 else 0))

def dpAnswerCode {m k : ℕ} (ans : Option (Finset (Sym2 (Vertex m k)))) : List ℕ :=
  match ans with
  | none => [0]
  | some H => 1 :: sectionTourCode H

/-- Efficient implementation of this recurrence, rather than an arbitrary TSP solver. -/
def EfficientRestrictedDP : Prop :=
  ∃ P : RAM.Program, ∃ C : ℝ, 0 < C ∧ ∃ q : ℕ,
    ∀ (m k : ℕ) [NeZero m] [NeZero k], k ≤ m → 3 ≤ m+k →
    ∀ (G : SimpleGraph (Vertex m k)), SectionGraph G →
    ∀ (w : Sym2 (Vertex m k) → ℝ), Generic (cross w) → ∀ s : Fin k,
      ∃ t : ℕ, RAM.Halts P (sectionInput G w s) t ∧
        (t : ℝ) ≤ C * (m+k+1)^q * outputCount m k ∧
        (RAM.run P (sectionInput G w s) t).out.reverse =
          dpAnswerCode (restrictedDP G w (vertexList m k) (compatibleFamily (cross w)) (.inr s))

end ProportionalTSP.Exact


