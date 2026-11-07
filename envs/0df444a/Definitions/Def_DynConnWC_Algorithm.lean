-- Prove2me | Definitions.Def_DynConnWC_Algorithm
-- name    : DynConnWC_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:55.183442+00:00
-- url     : https://prove2.me/theorems/97632c48-3c8f-470c-967f-e5bd50b8436f
-- title:
--   The update algorithm as a deterministic function of the random choices
-- statement:
--   The structure keeps forests $F_0,\dots,F_L$ with $F_0$ edgeless and $L=128\lceil\log_2 n\rceil$, a final forest $F_{\mathrm{final}}$, one cutset instance $C_i$ per level and $r$ final instances. At level $i$ the trees of $F_{i-1}$ are the **lower trees** and those of $F_i$ the **upper trees**. The representative $z(P)$ of a lower tree $P$ has weight $1$ if $C_i(P)\ne\bot$ and $2$ if $C_i(P)=\bot$, and every other vertex has weight $0$; an upper tree is **light** if its mass $\sum_{v\in T'}w_{i-1}(v)$ is at most $1$.
--
--   An update of $\{x,y\}$ changes the graph and adjusts $F_{\mathrm{final}}$. It then processes the levels from bottom to top: on a deletion it removes $\{x,y\}$ from $F_i$, brings the weights up to date with `UpdateWeights`, and, if the list $Q_i$ of light trees is nonempty, links the pair returned by `Promote` for its head. A link at level $L$ also goes into $F_{\mathrm{final}}$, exchanging out the first path edge leaving the $F_L$-tree if needed. On a deletion, if $x,y$ are disconnected in $F_{\mathrm{final}}$, the replacement search `FinalSearch` runs on the tree of $x$. Queries ask whether two vertices lie in the same tree of $F_{\mathrm{final}}$.
--
--   Once the random choices are fixed the algorithm is deterministic. The analysis of §4 is about this function.
--
--   **Formalization Note** `FindEdgeLeavingTree` is a parameter `sel`: any function of the two forests and two vertices meeting Lemma 7's specification (`IsLeaveSelector`). The Euler-tour search of Appendix B.2 is one such function, because all tours use the canonical vertex order of B.3. The fixed order of Remark 13 is increasing minimum vertex, and $Q_i$ is FIFO. The cases the paper proves impossible make no link, so the function is total. An unordered pair is oriented with `Sym2.out` where an endpoint is needed. `AlgSetup.Wf` collects the standing assumptions: $k$ even, $k\ge2$, $w\ge J$, and a selector meeting the specification.
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), §3.2–§3.6, pp.7–13 (PDF 8–14); §4.1, p.17 (PDF 18); Remark 13, p.18 (PDF 19)

import Mathlib
import Definitions.Def_PunctSketch_Update
import Definitions.Def_DynConnWC_Op
import Definitions.Def_DynConnWC_Forest
import Definitions.Def_DynConnWC_Cutset

set_option autoImplicit false

namespace DynConnWC

/-! # The update algorithm: levels, weights, Promote, the final forest

King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027
submission, sha256 9d16c13e…), §3.2–§3.6, pp.7–13, §4.1, p.17, and Remark 13, p.18.

* §3.2, p.7: forests `F_0, …, F_L`, `F_0` edgeless; at level `i` the trees of `F_{i−1}` are the
  lower trees and the trees of `F_i` the upper trees; `C_i(P)` is the answer of the cutset instance
  `C_i` on the lower tree `P`; the representative `z(P)` is the minimum vertex of `P`, with weight
  `w_{i−1}(z(P)) = 1` if `C_i(P) ≠ ⊥` and `2` if `C_i(P) = ⊥`, all other vertices `0`; the mass of
  an upper tree `T′` is `M(T′) = Σ_{v∈T′} w_{i−1}(v)`; `T′` is light if `M(T′) ≤ 1`.
* §3.5, p.10 (maintenance rules): "A link in `F_{i−1}` merges two lower trees into one, and a cut
  splits one lower tree into two. Set the old representatives' weights to zero, then give each
  resulting tree's representative temporary weight two … When a representative's weight changes,
  update the mass of its upper tree and its membership in `Q_i`. Before a link or cut in `F_i`,
  remove the affected upper trees from `Q_i`. Afterward, append each resulting tree that is light
  to the tail of `Q_i`." `UpdateWeights_i(W)` "searches `C_i` on each distinct lower tree
  containing a vertex of `W`. It sets the representative's weight to one if the search returns a
  pair and to two if it returns ⊥".
* §3.5, pp.10–11 (initialization and the update): steps 1, 2(a)–(c).
* §3.4, p.9: `Promote(T′)` (mass zero; mass one, cases 1–3).
* §3.6, pp.12–13: the final forest, the exchange into `F_L` ("If a and b are connected in
  `F_final`, let T be their common tree in `F_final` and let `T′` be the tree of `F_L` containing a
  … remove [the first edge leaving `T′` on the path from a to b in T] from `F_final`. Add {a, b} to
  `F_final`, and then add it to `F_L`."), `FinalSearch` and the replacement repair.
* §4.1, p.17: `L = 128⌈log₂ n⌉`.
* Remark 13, p.18: "The maintenance rules of Section 3.5 process the affected trees in a fixed
  order, a tree added to `Q_i` is appended to its tail, and Promote takes the head of `Q_i`."

**Formalization Note.** The algorithm is a deterministic function of its setup (`k`, `w`, `r`,
the field encoding `enc`, the leave-edge selector `sel`, the search mode), its random choices
`R` (one instance `C_i` per level `i = 1, …, L` and `r` final instances), and the update sequence.
Queries do not change the state. `FindEdgeLeavingTree(v, w, T_lower, T′)` (Lemma 7, p.9) is a
parameter `sel lower upper v w`: any deterministic function of the two forests and the two
vertices that returns, whenever `w` lies in the lower tree of `v` but not in the upper tree of `v`,
an edge of the lower tree of `v` leaving the upper tree of `v` (`IsLeaveSelector`); the paper's
Euler-tour binary search (Appendix B.2) is one such selector. `FindEdgeLeavingTreeOnPath`
(Lemma 9) returns a unique edge and is computed from the path. The fixed order of Remark 13 is
increasing minimum vertex; `Q_i` is a FIFO list of vertex sets of upper trees. An unordered pair
`e` is oriented as `e.out` where an orientation is needed (the endpoint `a` of a promoted pair,
p.11). The stored weights of level `i` are `wt i`, and `Q i` is `Q_i`. Cases that the paper shows
cannot occur (a light tree with no positive vertex of weight one, a repeated search returning ⊥,
a promoted pair inside one upper tree) make no link, so the algorithm is defined for every outcome
of the random choices. The cutset instances are the search of `Def_DynConnWC_Cutset`, which reads
the current graph; their stored summaries are not modelled separately (Appendix A.2: the summed
values are the cut sums). -/

variable {n : ℕ}

/-- `L = 128⌈log₂ n⌉`, the number of levels (§4.1, p.17). -/
def Lpar (n : ℕ) : ℕ := 128 * ell n

/-- The fixed (non-random) data of the algorithm. -/
structure AlgSetup (n : ℕ) where
  /-- the independence parameter (even, `k ≥ 2`) -/
  k : ℕ
  /-- the field bit length (`w ≥ J`) -/
  w : ℕ
  /-- the number of final cutset instances -/
  r : ℕ
  /-- the identification of `F_{2^w}` with `w`-bit strings -/
  enc : GaloisField 2 w ≃ BitVec w
  /-- the implementation of `FindEdgeLeavingTree` -/
  sel : Finset (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) → Fin n → Fin n → Sym2 (Fin n)
  /-- the tests of a search: Appendix A.2, or the dictionary version of Remark 26 -/
  mode : SearchMode

/-- The selector satisfies the specification of `FindEdgeLeavingTree` (Lemma 7, p.9): if `w` is
in the lower tree of `v` but not in the upper tree `T′` of `v`, it returns an edge of the lower
tree of `v` with exactly one endpoint in `T′`. -/
def IsLeaveSelector
    (sel : Finset (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) → Fin n → Fin n → Sym2 (Fin n)) :
    Prop :=
  ∀ (lo up : Finset (Sym2 (Fin n))) (v w : Fin n), IsForestSet lo → IsForestSet up →
    w ∈ treeOf lo v → w ∉ treeOf up v →
      sel lo up v w ∈ lo ∧ (∀ x ∈ sel lo up v w, x ∈ treeOf lo v) ∧
        Leaves (treeOf up v) (sel lo up v w)

/-- The standing assumptions on the setup: `k` even with `k ≥ 2` (Definition 4, p.5), `w ≥ J`
(Appendix A.2, p.28), and a selector meeting the specification of `FindEdgeLeavingTree`. -/
def AlgSetup.Wf (S : AlgSetup n) : Prop :=
  Even S.k ∧ 2 ≤ S.k ∧ Jbits n ≤ S.w ∧ IsLeaveSelector S.sel

/-- The random choices: one instance for each level `1, …, L` and `r` final instances. -/
abbrev RandChoices (S : AlgSetup n) := (Fin (Lpar n) → Coins S.w S.k) × (Fin S.r → Coins S.w S.k)

/-- The uniform law on the random choices: all instances independent, each uniform. -/
noncomputable def randLaw (S : AlgSetup n) : PMF (RandChoices S) :=
  PMF.uniformOfFintype (RandChoices S)

/-- The random choices of the level instance `C_i` (`1 ≤ i ≤ L`). -/
noncomputable def RandChoices.lev {S : AlgSetup n} (R : RandChoices S) (i : ℕ) : Coins S.w S.k :=
  if h : i - 1 < Lpar n then R.1 ⟨i - 1, h⟩ else (fun _ => 0, 0)

/-- The random choices of the final instance `C^final_{j+1}` (`j < r`). -/
noncomputable def RandChoices.fin {S : AlgSetup n} (R : RandChoices S) (j : ℕ) : Coins S.w S.k :=
  if h : j < S.r then R.2 ⟨j, h⟩ else (fun _ => 0, 0)

/-- The state of the data structure. `F i` is `F_i` (`0 ≤ i ≤ L`), `wt i` the stored weights of
level `i` (on the vertices, for the representatives of the trees of `F_{i−1}`), `Q i` the list
`Q_i`, `Ffin` the final forest, `G` the current graph. -/
structure State (n : ℕ) where
  G : SimpleGraph (Fin n)
  F : ℕ → Finset (Sym2 (Fin n))
  wt : ℕ → Fin n → ℕ
  Q : ℕ → List (Finset (Fin n))
  Ffin : Finset (Sym2 (Fin n))

/-- Initialization (p.10): the graph and all forests edgeless, every representative weight two,
every `Q_i` empty. -/
def initState : State n := ⟨⊥, fun _ => ∅, fun _ _ => 2, fun _ => [], ∅⟩

/-- The mass `M(T′) = Σ_{v∈T′} w(v)`. -/
def mass (wt : Fin n → ℕ) (T : Finset (Fin n)) : ℕ := ∑ v ∈ T, wt v

/-- The trees of `F` containing a vertex of `vs`, in increasing order of their minimum vertex. -/
noncomputable def orderedTrees (F : Finset (Sym2 (Fin n))) (vs : Finset (Fin n)) :
    List (Finset (Fin n)) :=
  ((vs.image (rep F)).sort (· ≤ ·)).map (treeOf F)

open Classical in
/-- Update the membership of the upper tree `T` in the list `Q` after a weight change. -/
noncomputable def refreshQ (wt : Fin n → ℕ) (Q : List (Finset (Fin n))) (T : Finset (Fin n)) :
    List (Finset (Fin n)) :=
  if mass wt T ≤ 1 then (if T ∈ Q then Q else Q ++ [T]) else Q.filter (· ≠ T)

open Classical in
/-- Replace `F_i` by `Fnew` (a link or a cut of the pair `{a, b}`) and apply the maintenance rules
of §3.5 to the records of level `i` (its upper forest) and of level `i + 1` (its lower forest). -/
noncomputable def editForest (s : State n) (i : ℕ) (a b : Fin n)
    (Fnew : Finset (Sym2 (Fin n))) : State n :=
  let Fold := s.F i
  let Qi := (orderedTrees Fnew {a, b}).foldl
    (fun Q T => if mass (s.wt i) T ≤ 1 then Q ++ [T] else Q)
    ((s.Q i).filter (fun T => T ∉ orderedTrees Fold {a, b}))
  let oldReps : Finset (Fin n) := {rep Fold a, rep Fold b}
  let newReps : Finset (Fin n) := {rep Fnew a, rep Fnew b}
  let wt' : Fin n → ℕ := fun v =>
    if v ∈ newReps then 2 else if v ∈ oldReps then 0 else s.wt (i + 1) v
  let Qnext := (orderedTrees (s.F (i + 1)) (oldReps ∪ newReps)).foldl (refreshQ wt') (s.Q (i + 1))
  if i + 1 ≤ Lpar n then
    { s with F := Function.update s.F i Fnew,
             wt := Function.update s.wt (i + 1) wt',
             Q := Function.update (Function.update s.Q i Qi) (i + 1) Qnext }
  else
    { s with F := Function.update s.F i Fnew, Q := Function.update s.Q i Qi }

open Classical in
/-- The weights of §3.2, p.7, defined from the answers: the representative of a tree `P` of `lower`
has weight `1` if `ok P` (the search of `C_i` on `P` returns a pair) and `2` otherwise, and every
other vertex has weight `0`. -/
noncomputable def repWeight (lower : Finset (Sym2 (Fin n))) (ok : Finset (Fin n) → Prop)
    (v : Fin n) : ℕ :=
  if rep lower v = v then (if ok (treeOf lower v) then 1 else 2) else 0

/-- `UpdateWeights_i(W)` (§3.5, p.10): search `C_i` on each distinct lower tree containing a
vertex of `W`, in increasing order of the representative, set the representative's weight to `1`
or `2`, and update `Q_i`. Returns the new state and the searched lower trees. -/
noncomputable def updateWeights (S : AlgSetup n) (co : Coins S.w S.k) (s : State n) (i : ℕ)
    (W : Finset (Fin n)) : State n × List (Finset (Fin n)) :=
  let lower := s.F (i - 1)
  let zs := (W.image (rep lower)).sort (· ≤ ·)
  let s' := zs.foldl (fun (s : State n) z =>
      let wz := if (search S.mode S.enc co s.G (treeOf lower z)).isSome then 1 else 2
      let wt' := Function.update (s.wt i) z wz
      { s with wt := Function.update s.wt i wt',
               Q := Function.update s.Q i (refreshQ wt' (s.Q i) (treeOf (s.F i) z)) }) s
  (s', zs.map (treeOf lower))

open Classical in
/-- `Promote(T′)` at level `i` (§3.4, p.9), for a light upper tree `T′`. -/
noncomputable def promote (S : AlgSetup n) (co : Coins S.w S.k) (s : State n) (i : ℕ)
    (T' : Finset (Fin n)) : Option (Sym2 (Fin n)) :=
  let lower := s.F (i - 1)
  let upper := s.F i
  if hT : T'.Nonempty then
    if mass (s.wt i) T' = 0 then
      -- mass zero: the minimum vertex `v` of `T′` and the representative of its lower tree
      let v := T'.min' hT
      some (S.sel lower upper v (rep lower v))
    else if hz : (T'.filter (fun v => 0 < s.wt i v)).Nonempty then
      -- mass one: the unique lower representative `z` in `T′`
      let z := (T'.filter (fun v => 0 < s.wt i v)).min' hz
      let Tl := treeOf lower z
      match search S.mode S.enc co s.G Tl with
      | none => none
      | some p =>
        let a := if p.out.1 ∈ Tl then p.out.1 else p.out.2
        let b := if p.out.1 ∈ Tl then p.out.2 else p.out.1
        if a ∉ T' then some (S.sel lower upper z a)
        else if b ∉ T' then some p
        else some (S.sel lower upper b (rep lower b))
    else none
  else none

open Classical in
/-- The exchange of §3.6 (p.13) for adding `{a, b}` to `F_L`, applied to the final forest: if `a`
and `b` are connected in `F_final`, remove the first edge on the path from `a` to `b` in
`F_final` that leaves the tree of `F_L` containing `a`; then add `{a, b}`. -/
noncomputable def finalExchange (Ffin FL : Finset (Sym2 (Fin n))) (a b : Fin n) :
    Finset (Sym2 (Fin n)) :=
  if h : (forestGraph Ffin).Reachable a b then
    let T' := treeOf FL a
    match (h.some.toPath).1.darts.find? (fun d => decide (d.fst ∈ T' ∧ d.snd ∉ T')) with
    | some d => insert s(a, b) (Ffin.erase d.edge)
    | none => insert s(a, b) Ffin
  else insert s(a, b) Ffin

/-- What level `i` did in one update: the lower trees searched by `UpdateWeights_i`, the forests
`F_{i−1}` and `F_i` at the merge step (after step 2(b)), and whether a pair was linked. -/
structure LevelRecord (n : ℕ) where
  searched : List (Finset (Fin n))
  lowerAtMerge : Finset (Sym2 (Fin n))
  upperAtMerge : Finset (Sym2 (Fin n))
  linked : Bool

instance : Inhabited (LevelRecord n) := ⟨⟨[], ∅, ∅, false⟩⟩

open Classical in
/-- Level `i` of the bottom-up pass (§3.5, step 2(a)–(c)) for the update of `{x, y}`
(`ins` = insertion), entered with the vertex `p` set by level `i − 1`. Returns the new state, the
new `p`, and the record of the level. -/
noncomputable def levelStep (S : AlgSetup n) (R : RandChoices S) (x y : Fin n) (ins : Bool)
    (s : State n) (i : ℕ) (p : Option (Fin n)) : State n × Option (Fin n) × LevelRecord n :=
  -- (a) on deletion, delete {x, y} from F_i if present
  let s1 := if ins = false ∧ s(x, y) ∈ s.F i then editForest s i x y ((s.F i).erase s(x, y)) else s
  -- (b) bring the weights up to date
  let ws := updateWeights S (R.lev i) s1 i (({x, y} : Finset (Fin n)) ∪ p.toFinset)
  let s2 := ws.1
  let rec0 : LevelRecord n := ⟨ws.2, s2.F (i - 1), s2.F i, false⟩
  -- (c) at most one merge
  match (s2.Q i).head? with
  | none => (s2, none, rec0)
  | some T' =>
    match promote S (R.lev i) s2 i T' with
    | none => (s2, none, rec0)
    | some e =>
      if ¬ SameTree (s2.F i) e.out.1 e.out.2 then
        let s3 := if i = Lpar n then { s2 with Ffin := finalExchange s2.Ffin (s2.F i) e.out.1 e.out.2 }
                  else s2
        (editForest s3 i e.out.1 e.out.2 (insert e (s3.F i)), some e.out.1, { rec0 with linked := true })
      else (s2, none, rec0)

/-- `FinalSearch(T)` (p.12): search `T` in `C^final_1, …, C^final_r` in order and return the first
pair. -/
noncomputable def finalSearch (S : AlgSetup n) (R : RandChoices S) (G : SimpleGraph (Fin n))
    (T : Finset (Fin n)) : Option (Sym2 (Fin n)) :=
  (List.range S.r).findSome? (fun j => search S.mode S.enc (R.fin j) G T)

/-- The levels `1, …, m` of the pass, from the state `s` (with `p = ⊥` on entry to level 1). -/
noncomputable def levelsUpTo (S : AlgSetup n) (R : RandChoices S) (x y : Fin n) (ins : Bool)
    (s : State n) : ℕ → State n × Option (Fin n) × (ℕ → LevelRecord n)
  | 0 => (s, none, fun _ => default)
  | m + 1 =>
    let prev := levelsUpTo S R x y ins s m
    let res := levelStep S R x y ins prev.1 (m + 1) prev.2.1
    (res.1, res.2.1, Function.update prev.2.2 (m + 1) res.2.2)

open Classical in
/-- One update (§3.5–§3.6): apply it to the graph; update `F_final` (insertion: add `{x, y}` if
`x, y` are in different trees; deletion: remove `{x, y}`); process levels `1, …, L`; on a deletion,
the replacement repair. Returns the new state and the records of the levels. -/
noncomputable def update (S : AlgSetup n) (R : RandChoices S) (s : State n)
    (u : PunctSketch.Update n) : State n × (ℕ → LevelRecord n) :=
  let x := u.u
  let y := u.v
  let s0 : State n := { s with G := u.apply s.G }
  let s1 : State n :=
    if u.insert = true then
      (if ¬ SameTree s0.Ffin x y then { s0 with Ffin := insert s(x, y) s0.Ffin } else s0)
    else { s0 with Ffin := s0.Ffin.erase s(x, y) }
  let lv := levelsUpTo S R x y u.insert s1 (Lpar n)
  let s2 := lv.1
  let s3 : State n :=
    if u.insert = false ∧ ¬ SameTree s2.Ffin x y then
      match finalSearch S R s2.G (treeOf s2.Ffin x) with
      | some e => { s2 with Ffin := insert e s2.Ffin }
      | none => s2
    else s2
  (s3, lv.2.2)

/-- The state after the first `t` updates of `σ` (`t = 0`: the initial state). -/
noncomputable def stateAt (S : AlgSetup n) (R : RandChoices S) (σ : List (PunctSketch.Update n))
    (t : ℕ) : State n :=
  (σ.take t).foldl (fun s u => (update S R s u).1) initState

/-- The record of level `i` in update `t` (`1 ≤ t ≤ |σ|`, `1 ≤ i ≤ L`). -/
noncomputable def recAt (S : AlgSetup n) (R : RandChoices S) (σ : List (PunctSketch.Update n))
    (t i : ℕ) : LevelRecord n :=
  match σ[t - 1]? with
  | some u => (update S R (stateAt S R σ (t - 1)) u).2 i
  | none => default

/-- The state after the updates among the first `t` operations of `ops`. -/
noncomputable def stateOps (S : AlgSetup n) (R : RandChoices S) (ops : List (Op n)) (t : ℕ) :
    State n :=
  (updatesOf (ops.take t)).foldl (fun s u => (update S R s u).1) initState

open Classical in
/-- The algorithm's answer to a query `(u, v)` at operation `t` of `ops` (`t` counted from `0`):
`1` if `u` and `v` lie in the same tree of `F_final`, else `0` (§3.6, p.14). -/
noncomputable def algBit (S : AlgSetup n) (R : RandChoices S) (ops : List (Op n)) (t : ℕ)
    (u v : Fin n) : ℕ :=
  if SameTree (stateOps S R ops t).Ffin u v then 1 else 0

/-- Every query of `ops` is answered correctly by the algorithm: for `ops[t] = query (u, v)`, the
answer "`u` and `v` lie in the same tree of `F_final`" holds exactly when `u` and `v` are connected
in the current graph. -/
def AlgAllCorrect (S : AlgSetup n) (R : RandChoices S) (ops : List (Op n)) : Prop :=
  ∀ (t : ℕ) (ht : t < ops.length) (u v : Fin n), ops[t] = .query u v →
    (SameTree (stateOps S R ops t).Ffin u v ↔ (graphAt ops t).Reachable u v)

end DynConnWC


