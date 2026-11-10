-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_RoundOrCut
-- name    : EdgeSublinearMWIS_Main_RoundOrCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:42:14.820835+00:00
-- url     : https://prove2.me/theorems/dab22d7c-9a25-4984-9266-402269c3a379
-- title:
--   Operational semantics of Algorithms 1–2
-- statement:
--   The operational tasks are Solve, the descending target loop, ellipsoid dialogue, RoundOrCut, and component processing. Raw finite programs supply separator and exact feasibility subroutines; their record has no correctness, termination or complexity fields. Source constraints are generated as rational inequalities, with both directions for equalities. Conditioning enumerates sets and tests the exact quadratic inequality.
--
--   $$\lambda=h(n),\quad\delta=\varepsilon/\lambda,\quad p=p(n,\delta),\quad r=2p\lambda.$$
--   For $n\le1$ the direct edgeless handler uses inert parameters. Each recursive call keeps the same global parameters. The execution relation includes every target rejection, every actual subprogram execution and every recursive child. It neither postulates a successful answer nor assigns an optimum. Component and coordinate order are fixed by the ascending original labels. Every ellipsoid query, including a feasible one, is passed to RoundOrCut; an independent-set result stops the dialogue.
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), §5.2, Algorithms 1–2, Eq. (22), p.17 (PDF p.17), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Paths
import Definitions.Def_EdgeSublinearMWIS_Main_Relaxation

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

/-- Deterministic enumeration of the true coordinates. -/
def coordinateList {n : ℕ} (W : Finset (Fin n)) (r : ℕ) : List (Finset (Fin n)) :=
  (((W.sort (· ≤ ·)).sublists).map List.toFinset).filter (fun A => A.card ≤ r + 2)

/-- A sparse rational inequality, with repeated terms collected when serialized. -/
structure Cut (n : ℕ) where
  terms : List (Finset (Fin n) × ℚ)
  rhs : ℚ

def Cut.eval {n : ℕ} (c : Cut n) (y : Finset (Fin n) → ℚ) : ℚ :=
  (c.terms.map (fun e => e.2 * y e.1)).sum

def Cut.evalReal {n : ℕ} (c : Cut n) (y : Finset (Fin n) → ℝ) : ℝ :=
  (c.terms.map (fun e => (e.2 : ℝ) * y e.1)).sum

def Cut.neg {n : ℕ} (c : Cut n) : Cut n :=
  ⟨c.terms.map (fun e => (e.1, -e.2)), -c.rhs⟩

def equalityCuts {n : ℕ} (c : Cut n) : List (Cut n) := [c, c.neg]

noncomputable def relaxationRows {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (r k : ℕ) : List (Cut n) := by
  classical
  let all := coordinateList W r
  let small := all.filter (fun A => A.card ≤ r + 1)
  exact equalityCuts ⟨[(∅, 1)], 1⟩ ++
    all.flatMap (fun A => [⟨[(A, -1)], 0⟩, ⟨[(A, 1)], 1⟩]) ++
    small.flatMap (fun A => (W.sort (· ≤ ·)).map
      (fun v => ⟨[(insert v A, 1), (A, -1)], 0⟩)) ++
    (all.filter (fun (A : Finset (Fin n)) => ¬ G.IsIndepSet (A : Set (Fin n)))).map
      (fun A => ⟨[(A, 1)], 0⟩) ++
    small.flatMap (fun A => equalityCuts
      ⟨((W.sort (· ≤ ·)).map (fun v => (insert v A, 1))) ++ [(A, -(k : ℚ))], 0⟩)

noncomputable def conditioningChoice {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (r k p : ℕ) (y : Finset (Fin n) → ℚ) :
    Option (Finset (Fin n)) := by
  classical
  let edges := ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => e.1 ∈ W ∧ e.2 ∈ W ∧ e.1 < e.2 ∧ G.Adj e.1 e.2))
  exact (coordinateList W r).find? (fun A =>
    A.card ≤ r ∧ 0 < y A ∧
    (p : ℚ) * (∑ e ∈ edges, y (insert e.1 A) * y (insert e.2 A)) ≤
      (k : ℚ) ^ 2 * y A ^ 2)

def queryCosts {n : ℕ} (y : Finset (Fin n) → ℚ) (A : Finset (Fin n)) : Fin n → ℚ :=
  fun v => y (insert v A) / y A

noncomputable def separatorInput {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (δ : ℚ) (x : Fin n → ℚ) : List Bool :=
  graphBits G ++ mask W ++ encodeRat δ ++
    ((W.sort (· ≤ ·)).flatMap (fun v => encodeRat (x v)))

noncomputable def encodeCut {n : ℕ} (W : Finset (Fin n)) (r : ℕ) (c : Cut n) : List Bool :=
  (coordinateList W r).flatMap (fun A => encodeRat
    (((c.terms.filter (fun e => e.1 = A)).map Prod.snd).sum)) ++ encodeRat c.rhs

noncomputable def ellipsoidInput {n : ℕ} (W : Finset (Fin n)) (r : ℕ)
    (bound : Polynomial ℕ) (cuts : List (Cut n)) : List Bool :=
  encodeNat (Coordinates W r).card ++ encodeNat (bound.eval ((Coordinates W r).card + 1)) ++
    encodeNat cuts.length ++ cuts.flatMap (encodeCut W r)

/-- Raw finite programs only. Correctness, termination and resources are not fields. -/
structure Routines where
  separator : Program
  ellipsoid : Program
  descriptionBound : Polynomial ℕ

structure Parameters where
  lambda : ℕ
  delta : ℚ
  p : ℕ
  r : ℕ

def parameters (B a n : ℕ) (ε : ℚ) : Parameters :=
  if n ≤ 1 then ⟨0, 0, 1, 0⟩ else
  let l := height n
  let δ := ε / (l : ℚ)
  let p := threshold B a n δ
  ⟨l, δ, p, 2 * p * l⟩

inductive Task (n : ℕ) where
  | solve (W : Finset (Fin n))
  | target (W : Finset (Fin n)) (k : ℕ)
  | ellipsoid (W : Finset (Fin n)) (k : ℕ) (history : List (Cut n))
  | round (W : Finset (Fin n)) (k : ℕ) (y : Finset (Fin n) → ℚ)
  | children (W : Finset (Fin n)) (k : ℕ) (y : Finset (Fin n) → ℚ)
      (A : Finset (Fin n)) (todo : List (Finset (Fin n))) (acc : Finset (Fin n))

inductive Answer (n : ℕ) where
  | solved (I : Finset (Fin n)) (u : ℕ)
  | independent (I : Finset (Fin n))
  | inequality (c : Cut n)
  | empty

noncomputable def exactCandidate {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (k : ℕ) : Option (Finset (Fin n)) := by
  classical
  exact (((W.sort (· ≤ ·)).sublists).map List.toFinset).find?
    (fun I => I.card = k ∧ G.IsIndepSet (I : Set (Fin n)))

noncomputable def componentList {n : ℕ} (G : SimpleGraph (Fin n))
    (W S : Finset (Fin n)) : List (Finset (Fin n)) :=
  (((W \ S).sort (· ≤ ·)).map
    (TreewidthApprox.Pushed.avoidComp G (S ∪ (Finset.univ \ W)))).dedup

/-- Big-step operational semantics of Algorithms 1 and 2. It has no constructor
asserting termination, independence, optimality, valid cuts or lightness. All calls
of the two raw subprograms must really halt on their serialized input. -/
inductive Execute {n : ℕ} (G : SimpleGraph (Fin n)) (P : Parameters) (M : Routines) :
    Task n → Answer n → Prop where
  | edgeless (W) (h : ∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v) :
      Execute G P M (.solve W) (.solved W W.card)
  | start (W I u) (h : ∃ v ∈ W, ∃ w ∈ W, G.Adj v w)
      (next : Execute G P M (.target W W.card) (.solved I u)) :
      Execute G P M (.solve W) (.solved I u)
  | exact (W k I) (hk : 0 < k) (hp : k ≤ P.p)
      (found : exactCandidate G W k = some I) :
      Execute G P M (.target W k) (.solved I k)
  | exactReject (W k I u) (hk : 0 < k) (hp : k ≤ P.p)
      (absent : exactCandidate G W k = none)
      (next : Execute G P M (.target W (k - 1)) (.solved I u)) :
      Execute G P M (.target W k) (.solved I u)
  | approx (W k I) (hp : P.p < k)
      (next : Execute G P M (.ellipsoid W k []) (.independent I)) :
      Execute G P M (.target W k) (.solved I k)
  | approxReject (W k I u) (hp : P.p < k)
      (empty : Execute G P M (.ellipsoid W k []) .empty)
      (next : Execute G P M (.target W (k - 1)) (.solved I u)) :
      Execute G P M (.target W k) (.solved I u)
  | ellipsoidEmpty (W k cuts)
      (run : Evaluates M.ellipsoid (ellipsoidInput W P.r M.descriptionBound cuts) [false]) :
      Execute G P M (.ellipsoid W k cuts) .empty
  | ellipsoidAccept (W k cuts y I)
      (run : Evaluates M.ellipsoid (ellipsoidInput W P.r M.descriptionBound cuts)
        (true :: encodePoint W P.r y))
      (next : Execute G P M (.round W k y) (.independent I)) :
      Execute G P M (.ellipsoid W k cuts) (.independent I)
  | ellipsoidCut (W k cuts y c ans)
      (run : Evaluates M.ellipsoid (ellipsoidInput W P.r M.descriptionBound cuts)
        (true :: encodePoint W P.r y))
      (cut : Execute G P M (.round W k y) (.inequality c))
      (next : Execute G P M (.ellipsoid W k (cuts ++ [c])) ans) :
      Execute G P M (.ellipsoid W k cuts) ans
  | violatedRow (W k y c)
      (row : ((relaxationRows G W P.r k).find? (fun c => decide (c.rhs < c.eval y))) = some c) :
      Execute G P M (.round W k y) (.inequality c)
  | roundFeasible (W k y A S ans)
      (rows : ((relaxationRows G W P.r k).find? (fun c => decide (c.rhs < c.eval y))) = none)
      (conditioned : conditioningChoice G W P.r k P.p y = some A)
      (run : Evaluates M.separator (separatorInput G W P.delta (queryCosts y A)) (mask S))
      (next : Execute G P M (.children W k y A (componentList G W S) ∅) ans) :
      Execute G P M (.round W k y) ans
  | childrenDone (W k y A I) :
      Execute G P M (.children W k y A [] I) (.independent I)
  | componentCut (W k y A D todo I J u)
      (child : Execute G P M (.solve D) (.solved J u))
      (violated : (u : ℚ) < ∑ v ∈ D, queryCosts y A v) :
      Execute G P M (.children W k y A (D :: todo) I)
        (.inequality ⟨((D.sort (· ≤ ·)).map (fun v => (insert v A, 1))) ++ [(A, -(u : ℚ))], 0⟩)
  | componentKeep (W k y A D todo I J u ans)
      (child : Execute G P M (.solve D) (.solved J u))
      (keep : (∑ v ∈ D, queryCosts y A v) ≤ (u : ℚ))
      (next : Execute G P M (.children W k y A todo (I ∪ J)) ans) :
      Execute G P M (.children W k y A (D :: todo) I) ans

end EdgeSublinearMWIS.Main


