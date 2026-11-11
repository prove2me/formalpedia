-- Prove2me | Definitions.Def_WeakStrongMSR_Rounding
-- name    : WeakStrongMSR_Rounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:27:45.793982+00:00
-- url     : https://prove2.me/theorems/56641349-f689-4ef7-85b9-75c3955cd322
-- title:
--   The rounding step (§3.2.1, Algorithm 2): primal–dual growth, pruning, selection, components
-- statement:
--   Rounding starts from the final strong set $S$ and family $\mathcal C$ of sampling.
--
--   1. **Growth.** Starting from $y=0$, raise all unfrozen variables at the same rate. When a candidate constraint becomes tight, add the candidate to $Z$ and freeze its points. When the variables reach the cap $\lambda/h$, freeze them and put them into $L$ unless they were frozen through a candidate.
--   2. Abort if $|L|>ckh$; otherwise strongly query $L$.
--   3. **Prune** $Z$ to the largest radius at each centre.
--   4. **Select.** Scan in nonincreasing order of radius. Select a candidate unless $d(s,s')\le R+R'$ for an already selected $(s',R')$; otherwise assign it to such a candidate. Abort if more than $ck$ candidates are selected. Write $Z'=\{(s_i,R_i)\}_{i\le m}$.
--   5. **Merge.** Join $i,j$ when $d(s_i,s_j)\le 7(R_i+R_j)$. Each component $J$ gets a root $c_J$ and the radius $R_J=14\sum_{i\in J}R_i$. Its list $X_J$ holds the unqueried points frozen through a candidate whose selected representative lies in $J$. The union $B'_J=\bigcup_{i\in J}B(s_i,5R_i)$ is Eq. (10).
--
--   **Formalization Note** Growth is a finite event recursion. The next event time is the least of the cap slack and, over not-yet-tight candidates with an unfrozen point, (slack)/(number of unfrozen points). Simultaneous events are processed together, in the order of $\mathcal C$. Ties are fixed as follows: pruning keeps the earliest of equal radii, the scan is stable, a discarded candidate goes to the first conflicting selected one, and the root is the selected candidate of least index. An abort records the strong queries made so far.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), §3.2.1, pp.14–15 (PDF 15–16), Algorithm 2, p.16 (PDF 17); Eq. (10), p.18 (PDF 19)

import Mathlib
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_LP

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-!
# The rounding step (§3.2.1, Algorithm 2)

Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), §3.2.1, pp.14–15 and Algorithm 2, p.16: "Starting from
y = 0, increase every unfrozen variable at the same rate until either a candidate constraint becomes
tight or a variable reaches its cap λ/h. In the first case, add the candidate to Z and freeze all its
points; in the second, freeze the point and put it into a set L of singletons. Resolve simultaneous
events consistently, processing all newly tight constraints." Line 6: "if |L| > ckh then abort";
line 7: query `L`; line 8: prune `Z` (largest radius per centre); lines 9–11: in nonincreasing order
of `R`, select a candidate unless `d(s, s′) ≤ R + R′` for a selected `(s′, R′)`, else assign it to
such a selected candidate; line 12: "if |Z′| > ck then abort"; lines 13–16: the graph with edges
`d(s_i, s_j) ≤ 7(R_i + R_j)`, a root `c_J` and `R_J = 14 ∑_{i ∈ J} R_i` per component, and the
lists `X_J` of the points frozen through a candidate, by their selected representative.

This module bundles the growth process, selection and merging of one algorithm.

**Formalization Note.**
* The growth is a finite event recursion (BRIEF pitfall 10): all unfrozen variables share one value
  `t`; the next event time is the least of the cap slack `λ/h − t` and, over the not-yet-tight
  candidates with an unfrozen point, `(R + λ − y(A)) / #(unfrozen points of A)`. All candidates
  attaining it become tight at once, processed in their order in `C`; a point is frozen through the
  first of them containing it. If the cap is reached, all remaining unfrozen points enter `L`. Each
  event freezes a point, so `|X ∖ S| + 1` iterations suffice.
* Ties (R12): pruning keeps, at each centre, the largest radius, the earliest in `Z` among equal
  radii; the scan is a stable sort by nonincreasing radius (ties by position in `Z`); a discarded
  candidate is assigned to the first conflicting selected candidate; the root of a component is its
  selected candidate of least index. A pruned-away candidate inherits the assignment of the
  retained candidate at its centre.
* A rounding outcome is an abort (with the strong queries it made: `0` at line 6, `|L|` at line 12)
  or the data passed to repair. Components are named by their roots. -/

/-- The state of the growth process for the candidates `cs : Fin m → Cand n`. -/
structure GrowState (n m : ℕ) where
  /-- The frozen variables. -/
  frozen : Finset (Fin n)
  /-- The value of each frozen variable. -/
  val : Fin n → ℝ
  /-- The common value of the unfrozen variables. -/
  t : ℝ
  /-- The tight candidates. -/
  tight : Finset (Fin m)
  /-- The tight candidates, in the order in which they became tight (`Z`). -/
  Z : List (Fin m)
  /-- The candidate through which a point was frozen, if any. -/
  via : Fin n → Option (Fin m)
  /-- The singletons `L`. -/
  L : Finset (Fin n)

/-- The current LP vector of a growth state on the variables `V`. -/
noncomputable def GrowState.y {n m : ℕ} (g : GrowState n m) (V : Finset (Fin n)) (x : Fin n) :
    ℝ :=
  if x ∈ g.frozen then g.val x else if x ∈ V then g.t else 0

/-- One event of the growth process on the variables `V`. -/
noncomputable def growStep {n m : ℕ} (V : Finset (Fin n)) (cs : Fin m → Cand n) (lam : ℝ) (h : ℕ)
    (g : GrowState n m) : GrowState n m :=
  if (V \ g.frozen) = ∅ then g else
    let U := V \ g.frozen
    let active := Finset.univ.filter (fun i => i ∉ g.tight ∧ ((cs i).A ∩ U).Nonempty)
    let time : Fin m → ℝ := fun i =>
      ((cs i).R + lam - ∑ x ∈ (cs i).A, g.y V x) / (((cs i).A ∩ U).card : ℝ)
    let capT := lam / h - g.t
    let Δ := active.fold min capT time
    let t' := g.t + Δ
    let newT := (active.filter (fun i => time i = Δ)).sort (· ≤ ·)
    let g1 := newT.foldl (fun g' i =>
      let newly := (cs i).A ∩ (V \ g'.frozen)
      { g' with
        frozen := g'.frozen ∪ newly
        val := fun x => if x ∈ newly then t' else g'.val x
        via := fun x => if x ∈ newly then some i else g'.via x
        tight := insert i g'.tight
        Z := g'.Z ++ [i] }) { g with t := t' }
    if Δ = capT then
      let rest := V \ g1.frozen
      { g1 with
        frozen := g1.frozen ∪ rest
        val := fun x => if x ∈ rest then t' else g1.val x
        L := g1.L ∪ rest }
    else g1

/-- The result of the growth process from `y = 0` on the variables `X ∖ S`. -/
noncomputable def growth {n : ℕ} (S : Finset (Fin n)) (cands : List (Cand n)) (lam : ℝ) (h : ℕ) :
    GrowState n cands.length :=
  let V := Finset.univ.filter (fun x => x ∉ S)
  (growStep V cands.get lam h)^[V.card + 1]
    ⟨∅, fun _ => 0, 0, ∅, [], fun _ => none, ∅⟩

/-- Pruning (line 8): the candidates of `Z` that have the largest radius at their centre (the
earliest in `Z` among equal radii), in the order of `Z`. -/
noncomputable def pruned {n m : ℕ} (cs : Fin m → Cand n) (Z : List (Fin m)) : List (Fin m) :=
  Z.filter (fun i => ∀ j ∈ Z, (cs j).s = (cs i).s →
    (cs j).R < (cs i).R ∨ ((cs j).R = (cs i).R ∧ Z.idxOf i ≤ Z.idxOf j))

/-- Selection (lines 9–11): scan the pruned candidates in nonincreasing order of radius (stable),
select a candidate unless its centre is within the sum of the radii of a selected centre; return
the selected candidates in order and, for each scanned candidate, its selected representative. -/
noncomputable def selection {n m : ℕ} (d : Fin n → Fin n → ℝ) (cs : Fin m → Cand n)
    (Z : List (Fin m)) : List (Fin m) × (Fin m → Fin m) :=
  ((pruned cs Z).mergeSort (fun a b => decide ((cs b).R ≤ (cs a).R))).foldl
    (fun (acc : List (Fin m) × (Fin m → Fin m)) i =>
      match acc.1.find? (fun j => decide (d (cs i).s (cs j).s ≤ (cs i).R + (cs j).R)) with
      | some j => (acc.1, Function.update acc.2 i j)
      | none => (acc.1 ++ [i], Function.update acc.2 i i))
    ([], id)

/-- The selected family `Z′` of the candidates `cands` with strong set `S` and guess `λ`. -/
noncomputable def selectedFamily {n : ℕ} (d : Fin n → Fin n → ℝ) (S : Finset (Fin n))
    (cands : List (Cand n)) (lam : ℝ) (h : ℕ) : List (Cand n) :=
  (selection d cands.get (growth S cands lam h).Z).1.map cands.get

/-- The data that rounding passes to repair. Selected candidates are indexed by `Fin m`. -/
structure RoundOut (n : ℕ) where
  /-- The strong set after querying `L`. -/
  S : Finset (Fin n)
  /-- The number `m` of selected candidates. -/
  m : ℕ
  /-- The centre `s_i`. -/
  ctr : Fin m → Fin n
  /-- The radius `R_i`. -/
  R : Fin m → ℝ
  /-- The witness set `W_{s_i}` from sampling. -/
  W : Fin m → Finset (Fin n)
  /-- The root (least index) of the component of `i`; components are named by their roots. -/
  root : Fin m → Fin m
  /-- The selected representative of each point (meaningful for unqueried points). -/
  rep : Fin n → Option (Fin m)
  /-- The strong queries of rounding (`|L|`). -/
  queries : ℕ

/-- The outcome of rounding. -/
inductive RoundResult (n : ℕ) : Type
  /-- Rounding aborted after making `queries` strong queries. -/
  | abort (queries : ℕ)
  /-- Rounding finished. -/
  | ok (r : RoundOut n)

/-- The rounding step (Algorithm 2) with parameters `c, k, h`, guess `λ`, on the strong set `S` and
the candidate family `cands` at the end of sampling. -/
noncomputable def round {n : ℕ} (c k h : ℕ) (lam : ℝ) (d : Fin n → Fin n → ℝ)
    (S : Finset (Fin n)) (cands : List (Cand n)) : RoundResult n :=
  let cs := cands.get
  let g := growth S cands lam h
  if c * k * h < g.L.card then .abort 0 else
    let sl := selection d cs g.Z
    let sel := sl.1
    if c * k < sel.length then .abort g.L.card else
      let ctr : Fin sel.length → Fin n := fun i => (cs (sel.get i)).s
      let R : Fin sel.length → ℝ := fun i => (cs (sel.get i)).R
      let G : SimpleGraph (Fin sel.length) :=
        SimpleGraph.fromRel (fun i j => d (ctr i) (ctr j) ≤ 7 * (R i + R j))
      .ok
        { S := S ∪ g.L
          m := sel.length
          ctr := ctr
          R := R
          W := fun i => (cs (sel.get i)).W
          root := fun i => (Finset.univ.filter (G.Reachable i)).min'
            ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl i⟩⟩
          rep := fun x =>
            match g.via x with
            | none => none
            | some i =>
                let p := ((pruned cs g.Z).find? (fun j => decide ((cs j).s = (cs i).s))).getD i
                let a := sl.2 p
                if hlt : sel.idxOf a < sel.length then some ⟨sel.idxOf a, hlt⟩ else none
          queries := g.L.card }

/-- The roots of the components. -/
noncomputable def RoundOut.roots {n : ℕ} (r : RoundOut n) : Finset (Fin r.m) :=
  Finset.univ.filter (fun j => r.root j = j)

/-- The members `J` of the component with root `j`. -/
noncomputable def RoundOut.comp {n : ℕ} (r : RoundOut n) (j : Fin r.m) : Finset (Fin r.m) :=
  Finset.univ.filter (fun i => r.root i = j)

/-- `R_J = 14 ∑_{i ∈ J} R_i` for the component with root `j`. -/
noncomputable def RoundOut.radiusJ {n : ℕ} (r : RoundOut n) (j : Fin r.m) : ℝ :=
  14 * ∑ i ∈ r.comp j, r.R i

/-- The list `X_J` of the component with root `j`: the unqueried points whose selected
representative lies in the component. -/
noncomputable def RoundOut.list {n : ℕ} (r : RoundOut n) (j : Fin r.m) : Finset (Fin n) :=
  Finset.univ.filter (fun x => x ∉ r.S ∧ (r.rep x).map r.root = some j)

/-- `B′_J = ⋃_{i ∈ J} B(s_i, 5R_i)` (Eq. (10)) for the component with root `j`. -/
noncomputable def RoundOut.inflated {n : ℕ} (d : Fin n → Fin n → ℝ) (r : RoundOut n)
    (j : Fin r.m) : Finset (Fin n) :=
  Finset.univ.filter (fun x => ∃ i, r.root i = j ∧ d (r.ctr i) x ≤ 5 * r.R i)

end WeakStrongMSR


