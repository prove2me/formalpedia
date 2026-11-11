-- Prove2me | Definitions.Def_OptimalLCA_Matching_DegreeHalving
-- name    : OptimalLCA_Matching_DegreeHalving
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:04.200373+00:00
-- url     : https://prove2.me/theorems/d3b76e37-efa7-42f5-9100-5b825b1b9edd
-- title:
--   §9.1 — local degree halving on B(H): pairing, link graph, marks, deletion rule, larger colour class
-- statement:
--   A **kept-proposal multigraph** $H$ on $\mathrm{Fin}\,n$: each proposal ID $(u,j)$, $j\in[K]$, is absent or a copy of an edge $uv$, $v\ne u$; parallel copies are distinct. $H_0=B(H)$: each copy $(u,j)\mapsto v$ has two lifts with IDs $(u,j,s)$: side index $0$ joins $(u,0),(v,1)$, side index $1$ joins $(v,0),(u,1)$. IDs are ordered lexicographically.
--
--   **One halving step** on the current copies $H_i$ with level-$i$ marks (one bit per original ID, shared by its two lifts) and radius $R$: at each vertex sort the incident copies of $H_i$ by ID and pair consecutive ones (positions $2k,2k+1$; one unpaired if the degree is odd). The **link graph** $P_i$ joins two copies paired at a common endpoint. $B_R(e)$ is the set of copies within $P_i$-distance $R$ of $e$. Delete $e$ if it is marked, or if $|B_R(e)|\ge R$ and $B_R(e)$ contains no mark. On each component of the surviving link graph, the proper 2-colouring is the parity of the distance from the component's smallest ID; keep the larger class, and on a tie the class containing the smallest ID. The kept copies form $H_{i+1}$.
--
--   Parameters (9.1): $p=\xi/(2J)$, $R=\lceil 2\log(1/p)/p\rceil$. `expectedFinal H J ξ` is $\mathbb E|E(H_J)|$ for i.i.d. $\mathrm{Bern}(p)$ marks per original ID and level $0,\dots,J-1$ (a finite sum).
--
--   **Cost model of Proposition 9.3.** The machine's list oracle at an $H_0$-vertex returns its incident copies sorted by ID, each as (ID, other endpoint); its mark oracle returns the level-$i$ mark of an ID. `HaltsWithinListCost P env m A B`: the run halts and (instructions other than list calls) $+\,A\cdot$(list calls) $\le B$. A mate answer $(w,s')$ is coded $2w+s'$, $\perp$ as $-1$.
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), pp. 43–44, §9.1, (9.1), Proposition 9.3

import Mathlib
import Definitions.Def_OptimalLCA_Matching_Machine

/-!
# Local degree halving (Cohen–Roghani, §9.1)

* A kept-proposal multigraph `H` on `Fin n` (§7.2): each proposal ID `(u, j)`
  (`u : Fin n`, `j : Fin K`, the paper's `j = 1, …, K`) is either absent (`none`) or a
  copy of the edge `uv` (`some v`, `v ≠ u`). Copies are distinct even when parallel.
* `H₀ = B(H)`: each copy `(u, j) ↦ v` has two lifts, with IDs `(u, j, s)`, `s : Fin 2`:
  side index `0` joins `(u, 0)` and `(v, 1)`, side index `1` joins `(v, 0)` and `(u, 1)`
  (the paper's sides `1, 2` are `0, 1`). IDs are ordered lexicographically through
  `rank (u, j, s) = (u K + j) 2 + s`.
* One halving step on the current set `Hi` of lifted copies with marks `mk` (one bit per
  original ID, shared by both lifts) and radius `R`: at each vertex the incident copies of
  `Hi`, sorted by ID, are paired consecutively (positions `2k, 2k+1`; `posAt`); the link
  graph `P_i` joins two copies paired at a common endpoint; a copy `e` is deleted if it is
  marked, or if its radius-`R` ball `B_R(e)` in `P_i` has at least `R` copies and no mark;
  on each component of the link graph restricted to the survivors, the proper 2-colouring
  is the parity of the distance from the component's smallest ID, and the larger class is
  kept (on a tie, the class of the smallest ID).
* `halvingSeq H marks R i = H_i` with `marks i` the marks of level `i`.
* `pParam ξ J = ξ/(2J)`, `rParam ξ J = ⌈2 log(1/p)/p⌉` (9.1).
* `expectedFinal H J ξ = E |E(H_J)|` for i.i.d. `Bern(p)` marks over the levels
  `0, …, J-1` and all IDs (a finite sum).
* `halvingEnv H marks`: the machine environment of Proposition 9.3. Its list oracle at the
  `H₀`-vertex `(v, side)` returns the incident lifted copies of `H₀` sorted by ID, each as
  `(u, j, s, w, s')` (the ID and the other endpoint `(w, s')`); its mark oracle at
  `(i, u, j)` is the level-`i` mark of `(u, j)`. A mate answer `(w, s')` is coded as
  `2w + s'`, and `⊥` as `-1`.
-/

namespace OptimalLCA.Matching

open Finset

/-- A kept-proposal multigraph: proposal `(u, j)` is absent or a copy of `uv`, `v ≠ u`. -/
structure KeptMultigraph (n K : ℕ) where
  kept : Fin n × Fin K → Option (Fin n)
  noLoop : ∀ c, kept c ≠ some c.1

namespace KeptMultigraph

variable {n K : ℕ}

/-- Maximum degree at most `D`: kept outgoing plus kept incoming copies at every vertex. -/
def MaxDegLE (H : KeptMultigraph n K) (D : ℕ) : Prop :=
  ∀ x : Fin n,
    (univ.filter (fun c : Fin n × Fin K => c.1 = x ∧ (H.kept c).isSome)).card +
      (univ.filter (fun c : Fin n × Fin K => H.kept c = some x)).card ≤ D

end KeptMultigraph

/-- IDs of lifted copies `(u, j, s)`. -/
abbrev LiftId (n K : ℕ) := Fin n × Fin K × Fin 2

variable {n K : ℕ}

/-- The lexicographic rank of a lifted ID. -/
def rank (c : LiftId n K) : ℕ := (c.1.val * K + c.2.1.val) * 2 + c.2.2.val

/-- The endpoints of a lifted copy in `B(H)` (empty if the proposal is not kept). -/
def liftEnds (H : KeptMultigraph n K) (c : LiftId n K) : Finset (Fin n × Fin 2) :=
  match H.kept (c.1, c.2.1) with
  | none => ∅
  | some v => if c.2.2 = 0 then {(c.1, 0), (v, 1)} else {(v, 0), (c.1, 1)}

/-- `H₀ = B(H)`: the lifted copies of all kept proposals. -/
def liftAll (H : KeptMultigraph n K) : Finset (LiftId n K) :=
  univ.filter (fun c => (H.kept (c.1, c.2.1)).isSome)

/-- The position of `c` in the ID-sorted list of copies of `Hi` incident to `x`. -/
noncomputable def posAt (H : KeptMultigraph n K) (Hi : Finset (LiftId n K))
    (x : Fin n × Fin 2) (c : LiftId n K) : ℕ := by
  classical
  exact (Hi.filter (fun c' => x ∈ liftEnds H c' ∧ rank c' < rank c)).card

/-- `c` and `c'` are paired at a common endpoint (consecutive positions `2k, 2k+1`). -/
def PairedIn (H : KeptMultigraph n K) (Hi : Finset (LiftId n K)) (c c' : LiftId n K) :
    Prop :=
  c ≠ c' ∧ c ∈ Hi ∧ c' ∈ Hi ∧ ∃ x, x ∈ liftEnds H c ∧ x ∈ liftEnds H c' ∧
    posAt H Hi x c / 2 = posAt H Hi x c' / 2

/-- The link graph `P_i` of the pairing in `Hi`, restricted to the copies in `S`. -/
def linkGraph (H : KeptMultigraph n K) (Hi S : Finset (LiftId n K)) :
    SimpleGraph (LiftId n K) where
  Adj c c' := c ∈ S ∧ c' ∈ S ∧ PairedIn H Hi c c'
  symm := ⟨fun c c' h => ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.2.1, h.2.2.2.1,
    let ⟨x, hx, hx', he⟩ := h.2.2.2.2.2; ⟨x, hx', hx, he.symm⟩⟩⟩
  loopless := ⟨fun c h => h.2.2.1 rfl⟩

/-- `|B_R(e)|`: the number of copies of `Hi` within link distance `R` of `e`. -/
noncomputable def ballCard (H : KeptMultigraph n K) (Hi : Finset (LiftId n K)) (R : ℕ)
    (e : LiftId n K) : ℕ := by
  classical
  exact (Hi.filter (fun c => (linkGraph H Hi Hi).edist e c ≤ (R : ℕ∞))).card

/-- The deletion rule: `e` is marked, or `|B_R(e)| ≥ R` and `B_R(e)` has no mark. -/
def Deleted (H : KeptMultigraph n K) (Hi : Finset (LiftId n K)) (mk : Fin n × Fin K → Bool)
    (R : ℕ) (e : LiftId n K) : Prop :=
  mk (e.1, e.2.1) = true ∨
    (R ≤ ballCard H Hi R e ∧
      ∀ c ∈ Hi, (linkGraph H Hi Hi).edist e c ≤ (R : ℕ∞) → mk (c.1, c.2.1) = false)

/-- One halving step. -/
noncomputable def halvingStep (H : KeptMultigraph n K) (Hi : Finset (LiftId n K))
    (mk : Fin n × Fin K → Bool) (R : ℕ) : Finset (LiftId n K) := by
  classical
  exact
    let S := Hi.filter (fun e => ¬ Deleted H Hi mk R e)
    let P := linkGraph H Hi S
    S.filter (fun e =>
      let comp := S.filter (fun c => P.Reachable e c)
      let C0 := comp.filter (fun c => ∃ m ∈ comp, (∀ c' ∈ comp, rank m ≤ rank c') ∧
        Even (P.dist m c))
      let C1 := comp \ C0
      (e ∈ C0 ∧ C1.card ≤ C0.card) ∨ (e ∈ C1 ∧ C0.card < C1.card))

/-- `H_i`, with `marks i` the marks of level `i`. -/
noncomputable def halvingSeq (H : KeptMultigraph n K) (marks : ℕ → Fin n × Fin K → Bool)
    (R : ℕ) : ℕ → Finset (LiftId n K)
  | 0 => liftAll H
  | i + 1 => halvingStep H (halvingSeq H marks R i) (marks i) R

/-- `p = ξ/(2J)` (9.1). -/
noncomputable def pParam (ξ : ℝ) (J : ℕ) : ℝ := ξ / (2 * (J : ℝ))

/-- `R = ⌈2 log(1/p)/p⌉` (9.1). -/
noncomputable def rParam (ξ : ℝ) (J : ℕ) : ℕ :=
  ⌈2 * Real.log (1 / pParam ξ J) / pParam ξ J⌉₊

/-- `E |E(H_J)|` for i.i.d. `Bern(p)` marks at levels `0, …, J-1`. -/
noncomputable def expectedFinal (H : KeptMultigraph n K) (J : ℕ) (ξ : ℝ) : ℝ :=
  ∑ marks : Fin J → Fin n × Fin K → Bool,
    (∏ i : Fin J, ∏ c : Fin n × Fin K,
        (if marks i c then pParam ξ J else 1 - pParam ξ J)) *
      ((halvingSeq H (fun i => if h : i < J then marks ⟨i, h⟩ else fun _ => false)
        (rParam ξ J) J).card : ℝ)

/-- The machine environment of Proposition 9.3: list oracle of `H₀ = B(H)` (sorted by ID)
and mark oracle; no graph oracle. -/
noncomputable def halvingEnv (H : KeptMultigraph n K) (marks : ℕ → Fin n × Fin K → Bool) :
    Env := by
  classical
  exact
  { deg := fun _ => 0
    nbr := fun _ _ => -1
    tape := fun _ => 0
    coin := fun _ _ => false
    mark := fun i u j =>
      if h : 0 ≤ i ∧ 0 ≤ u ∧ u < n ∧ 0 ≤ j ∧ j < K then
        marks i.toNat (⟨u.toNat, by omega⟩, ⟨j.toNat, by omega⟩) else false
    list := fun v side =>
      if h : 0 ≤ v ∧ v < n ∧ 0 ≤ side ∧ side < 2 then
        let x : Fin n × Fin 2 := (⟨v.toNat, by omega⟩, ⟨side.toNat, by omega⟩)
        (((liftAll H).filter (fun c => x ∈ liftEnds H c)).toList.mergeSort
            (fun a b => decide (rank a ≤ rank b))).map
          (fun c => ((c.1.val : ℤ), (c.2.1.val : ℤ), (c.2.2.val : ℤ),
            (((liftEnds H c).erase x).toList.headD x).1.val,
            (((liftEnds H c).erase x).toList.headD x).2.val))
      else [] }

/-- The memory of a mate query at the `H₀`-vertex `x = (v, side)`. -/
def halvingInput (x : Fin n × Fin 2) : ℤ → ℝ := fun a =>
  if a = 0 then (x.1.val : ℝ) else if a = 1 then (x.2.val : ℝ) else 0

/-- The run halts with at most `B` total work when each list call costs `A` and every
other instruction costs one unit. -/
def HaltsWithinListCost (P : Program) (env : Env) (m : ℤ → ℝ) (A B : ℝ) : Prop :=
  ∃ t, Halted P (run P env m t) ∧
    (((run P env m t).work - (run P env m t).listCalls : ℕ) : ℝ) +
      A * ((run P env m t).listCalls : ℝ) ≤ B

end OptimalLCA.Matching


