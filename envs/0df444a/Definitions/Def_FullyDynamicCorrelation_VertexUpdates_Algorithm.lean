-- Prove2me | Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Algorithm
-- name    : FullyDynamicCorrelation_VertexUpdates_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:51:16.069938+00:00
-- url     : https://prove2.me/theorems/9c5eff4f-857c-41db-a6b9-4211cca608a8
-- title:
--   Algorithms 1–7 as a transition system on executions whose randomized subroutines succeed
-- statement:
--   Algorithms 1–7 and Remarks 5.1–5.3 (pp. 31–37), the subroutine guarantees of Lemmas 3.1–3.3 (pp. 15–18) and Lemma 7.1/Remark 7.1 (p. 50), and the budget scheme of §8.3 (pp. 57–59), as a transition relation `Step n ε κ us` on states `St`; `Reach` is reachability from `St.init` (an execution prefix), `IsRun` an indexed execution prefix.
--
--   **State.** The current graph and update count; maintained clusters `clu` by identifier, each with members, $K(t_0)$ as vertex lifetimes `init`, $c(K)$, `inc`, `del`, the alive vertices that ever joined (`ever`, the records of Lemma 8.1), those counted by `inc` (`incd`) and the formation update `formUpd`; $\tilde V_{\rm singleton}$ (`single`); the set-aside vertices awaiting Algorithm 3 (`aside`); the $L=1+\lceil\log_2n\rceil$ candidate lists of entries (`lists`); the counters $c_i$; a task stack; the step clock; the charged work. Ghost fields (never consulted by a decision): spendable budgets in units of $\Phi$, the outside lifetimes added to each cluster (`addedL`) and those already present at its formation (`algAddedL`), the first-join step and the set of every addition step of each lifetime in each cluster, the work charged to each cluster (`attr`), the budgets each formation passes on (`passed`), the transfers of each lifetime (`incTr`, `delTr`), and a log of formations (`formLog`: size, degree of the forming vertex, members with an unused budget, whether that vertex had one).
--
--   **Subroutines.** Each returns any outcome its success guarantee allows: a sparsity test at $\theta$ answers yes only on a $0.9\theta$-sparse vertex and no only on a vertex that is not $\theta$-sparse (`TestOK`); a merge (`MergeOK`) needs $\deg v\ge10/\varepsilon$, the acceptance bounds $|N(v)\setminus C|\le3.2\varepsilon\deg v$, $|C|\le(1+4\varepsilon)\deg v$, and $4\varepsilon$-dense cores of size $\ge(1-8\varepsilon)|C|$ before and after admission, the latter containing $v$; a formation (`FormOK`) gives an $(\varepsilon/2)$-almost-clique with the guarantees of Lemma 3.2 and is not allowed when the merge condition of Lemma 3.2 forces a merge (`MergeForced`); identification (`IdentOK`) reports every outside vertex with $\ge|C|/2$ neighbours in $C$ and none with $\le|C|/4$; size estimates satisfy the bounds of Lemma 7.1 with $\xi=|\tilde V_{\rm singleton}|/(1000\cdot2^iL)$ (`EstDenseOK`, `EstSparseOK`); the degree-zero fraction is estimated within $1/100$.
--
--   **Steps.** Receiving an insertion or deletion (Algorithm 1 (2a)–(2b)); the $\varepsilon/20$ test and merge-or-form; refreshment (Algorithm 3) of a cluster whose `inc` or `del` reached $\varepsilon c(K)$, which is removed — and an emptied cluster discarded — before any other step (Remark 5.3); level checks while $c_i\ge h_i=\max\{1,\lfloor\zeta2^i/10\rfloor\}$, $\zeta=\varepsilon/500$, with `FLAG` (`checkFlag`, `jOrder`) and the scan of Algorithm 5 (pruning below $2^i/10$, $12\zeta$ tests, a partial scan stopping at $2^iL^2$ failures, entries appended during the scan visited too); Algorithm 7. `Settled`: no maintained cluster due or empty, nothing set aside, and no insertion, placement or refresh task pending; `Returned`: settled with no pending task.
--
--   **Work.** Each step charges the paper's per-operation bounds with one constant $\kappa$ and $\mathrm{lgp}\,n=1+\log_2n$: test $\kappa\,\mathrm{lgp}^2/\theta^2$, merge $\kappa\,\mathrm{lgp}^2/\varepsilon^2$, formation with identification $\kappa|C|\mathrm{lgp}^3/\varepsilon^2$, entering singletons $\kappa\,\mathrm{lgp}^2$ each, a level-$i$ estimate $\kappa2^i\mathrm{lgp}^5/\varepsilon^2$, list pruning $\kappa\,\mathrm{lgp}$, a stream update $\kappa\,\mathrm{lgp}^2$ plus $\kappa\,\mathrm{lgp}^2$ per notified record, a cluster removal $\kappa(|K|+1)\mathrm{lgp}^2$, a traversal $\kappa\,\mathrm{lgp}^2(1+|\tilde V_{\rm singleton}|)$.
--
--   `OutputCluster` includes maintained clusters and the output singleton blocks omitted from the active singleton pool (p. 49). `totalWork n κ q` adds to the recorded subroutine work a charge κ for every control transition and κ m (1 + 300(1 + log₂ n)^4)^q for polynomial offline calls and degree queries at the small-graph threshold. The fixed degree q and coefficient cover the chosen implementation and amplification; these are upper accounting charges, not uncharged oracle computations.
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Algorithms 1–7 and Remarks 5.1–5.3 (pp. 31–37), Lemmas 3.1–3.3 (pp. 15–18), Lemma 7.1 and Remark 7.1 (p. 50), §8.1–8.3 (pp. 55–59)

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Tolerant
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Stream

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-!
# Algorithms 1–7 on runs whose randomized subroutines succeed

Braverman et al. (2026), supplied manuscript sha256 07ee1c8f…aab2: Algorithms 1–7 and
Remarks 5.1–5.3 (pp. 31–37), Lemmas 3.1–3.3 and their proofs (pp. 15–18), Lemma 7.1 and
Remark 7.1 (p. 50), Section 8 (pp. 55–63).

The structural and time analysis of the paper (Sections 6–8; Appendix B, p. 71: "our structural
lemmas, refreshment rules, and budgeting arguments apply deterministically to arbitrary update
sequences whenever the local guarantees hold") is about executions in which every call of a
randomized subroutine meets its guarantee. This module defines exactly those executions: a
transition relation `Step` in which each randomized subroutine may return any outcome its
success guarantee allows, and no other.

* sparsity test at `θ` (Lemma 3.1, `η = 1/10`): may answer *yes* only if `v` is `0.9θ`-sparse,
  *no* only if `v` is not `θ`-sparse;
* merge (Lemma 3.2 and its proof, p. 16): only for `deg v ≥ 10/ε`, into a maintained cluster
  `C` passing the acceptance test (`|N(v) \ C| ≤ 3.2ε deg v`, `|C| ≤ (1 + 4ε) deg v`), with a
  `4ε`-dense core of size at least `(1 − 8ε)|C|` before and after admission, the core after
  admission containing `v`;
* formation (Lemma 3.2): an `(ε/2)`-almost-clique with the size, agreement and sparsity
  guarantees of Lemma 3.2, exactly `N[v]` (an isolated exact clique) when `deg v < 10/ε`, and
  only when the merge condition of Lemma 3.2 does not force a merge;
* identification (Lemma 3.3 with `δ = α = 1/2`, `γ = α/2`): every outside vertex with at least
  `|K|/2` neighbours in `K` is reported and none with at most `|K|/4`;
* size estimates (Algorithm 6, Lemma 7.1, p. 50): within the bounds stated there, with
  `ξ = |Ṽ_singleton| / (1000 · 2^i L)`; degree-zero fraction (Remark 7.1): additive `1/100`.

Constants (Remark 5.1): `β = 4`, `α = 1/2`, `ζ = ε/500`; `L = 1 + ⌈log₂ n⌉` lists, indices
`0, …, L − 1`; `h_i = max {1, ⌊ζ 2^i / 10⌋}`.

Work. Each step charges the time the paper's analysis assigns to it (Proposition 3.2,
Lemmas 3.1–3.3, 8.1–8.6), with one constant `κ` standing for the hidden `O(·)` constants and
`lgp n = 1 + log₂ n`: a sparsity test at `θ` costs `κ lgp² / θ²`, a merge `κ lgp² / ε²`, a
formation of `K` with identification `κ |K| lgp³ / ε²`, an entry to or departure from the
singleton structures `κ lgp²`, a level-`i` size estimate `κ 2^i lgp⁵ / ε²`, a degree-zero
estimate `κ lgp²`, a traversal `κ |Ṽ_singleton| lgp²`, a stream update `κ lgp²` plus `κ lgp²`
per membership record it notifies, the removal of a cluster `κ (|K| + 1) lgp²`.

Ghost data. The state also records, without influencing any decision: lifetimes `(v, t)` of
vertices (`t` the index of the insertion), the distinct outside lifetimes ever added to each
cluster and those added algorithmically, the step at which each lifetime first joined each
cluster, and the budget scheme of Section 8.3 (spendable budgets in units of `Φ`, the work
charged to each cluster, the budgets each formation passes on, and the transfers of each
update).

Scheduling (Remark 5.3). A maintained cluster whose counter has reached its threshold
(`inc(K) ≥ ε c(K)` or `del(K) ≥ ε c(K)`), or which has become empty, is removed before any other
step; the removal of a due cluster sets its members aside and starts its refreshment, which is
completed before the interrupted operation continues. All other choices the paper leaves open
(which due level to check, which set-aside vertex to process, which cluster a vertex merges into
when several qualify) are nondeterministic.
-/

/-- A vertex lifetime: its name and the index of the update that inserted it. -/
abbrev Life := ℕ × ℕ

/-- `L = 1 + ⌈log₂ n⌉`, the number of candidate lists (p. 34). -/
def numLevels (n : ℕ) : ℕ := 1 + Nat.clog 2 n

/-- `1 + log₂ n`. -/
noncomputable def lgp (n : ℕ) : ℝ := 1 + lg n

/-- `ζ = ε/500` (Algorithm 1 (2d)). -/
noncomputable def zeta (ε : ℝ) : ℝ := ε / 500

/-- `h_i = max {1, ⌊ζ 2^i / 10⌋}` (Algorithm 4 (4b)). -/
noncomputable def hThr (ε : ℝ) (i : ℕ) : ℕ := max 1 ⌊zeta ε * 2 ^ i / 10⌋₊

/-- A maintained cluster (Algorithm 1 (1)). `mem` is the current member set `K`, `init` the
lifetimes of `K(t₀)`, `c = c(K) = |K(t₀)|`; `inc` counts the distinct vertices added to `K` that
were inserted into the graph after `K` was formed (`incd` holds those counted and still alive);
`del` counts deletions of vertices that ever joined `K` (`ever` holds the alive vertices that
ever joined); `formUpd` is the number of stream updates received when `K` was formed. -/
structure Clu where
  mem : Finset ℕ
  init : Finset Life
  c : ℕ
  inc : ℕ
  del : ℕ
  ever : Finset ℕ
  incd : Finset ℕ
  formUpd : ℕ

/-- `K` is due for refreshment: `inc(K) ≥ ε c(K)` or `del(K) ≥ ε c(K)` (Algorithm 1 (2c)). -/
def Clu.Due (ε : ℝ) (K : Clu) : Prop := ε * (K.c : ℝ) ≤ K.inc ∨ ε * (K.c : ℝ) ≤ K.del

/-- An entry of a candidate list `Ṽ_list,(i)`: a vertex and a unique entry identifier. -/
structure Entry where
  v : ℕ
  id : ℕ

/-- Pending work, kept on a stack (the top is processed first). -/
inductive Task where
  /-- Algorithm 1 (2a): process the newly inserted vertex `v` -/
  | ins (v : ℕ)
  /-- Lemma 3.2 on a vertex outside all clusters whose sparsity test answered no:
  merge it into a cluster or form a new cluster (Algorithm 2) -/
  | place (v : ℕ)
  /-- Algorithm 3 step (2) for the cluster `k`, whose remaining members `vs` were set aside -/
  | refresh (k : ℕ) (vs : Finset ℕ)
  /-- Algorithm 3, the repetition over the set-aside vertices `no` whose test answered no,
  then step (3) for the members `all` still set aside -/
  | refreshLoop (k : ℕ) (no all : Finset ℕ)
  /-- Algorithm 4 (4b)–(4c) -/
  | alg4
  /-- Algorithm 5 on level `i` with `FLAG_i`, `FAIL_i` and the identifiers of visited entries -/
  | scan (i : ℕ) (flag : Bool) (fail : ℕ) (visited : Finset ℕ)
  /-- Algorithm 7 -/
  | alg7
  /-- Algorithm 7 (3b): level checks until every `c_i < h_i` -/
  | alg7checks

/-- Ghost record of a formation (Section 8.3): the new cluster's identifier and size, the degree
of the vertex it was formed from, how many of its members had an unused budget just before the
formation, and whether that vertex had one. -/
structure FormRec where
  id : ℕ
  size : ℕ
  seedDeg : ℕ
  budgeted : ℕ
  seedBudgeted : Bool

/-- The state of the algorithm (with ghost fields). -/
structure St where
  /-- number of stream updates received -/
  upd : ℕ
  /-- the current graph -/
  H : SGraph
  /-- index of the update that inserted each present vertex -/
  insTime : ℕ → ℕ
  /-- maintained clusters by identifier (`none`: not, or no longer, maintained) -/
  clu : ℕ → Option Clu
  /-- next fresh cluster identifier -/
  nextId : ℕ
  /-- `Ṽ_singleton` -/
  single : Finset ℕ
  /-- vertices set aside for Algorithm 3 -/
  aside : Finset ℕ
  /-- the candidate lists `Ṽ_list,(i)` -/
  lists : ℕ → List Entry
  /-- fresh entry identifiers -/
  nextEntry : ℕ
  /-- the level counters `c_i` -/
  cnt : ℕ → ℕ
  /-- pending tasks -/
  stack : List Task
  /-- number of steps taken -/
  clock : ℕ
  /-- total work charged -/
  work : ℝ
  /-- ghost: spendable budget of each lifetime, in units of `Φ` -/
  bud : Life → ℕ
  /-- ghost: distinct lifetimes outside `K(t₀)` ever added to cluster `k` -/
  addedL : ℕ → Finset Life
  /-- ghost: those of them that were already in the graph when `k` was formed -/
  algAddedL : ℕ → Finset Life
  /-- ghost: the step at which a lifetime first joined cluster `k` -/
  firstJoin : ℕ → Life → Option ℕ
  /-- ghost: every addition step, including repeated entries -/
  joins : ℕ → Life → Finset ℕ
  /-- ghost: work charged to cluster `k` (Lemma 8.11) -/
  attr : ℕ → ℝ
  /-- ghost: budgets `Φ` passed on by the formation of cluster `k` -/
  passed : ℕ → ℕ
  /-- ghost: insertion-reserve transfers made for a lifetime (Section 8.3) -/
  incTr : Life → ℕ
  /-- ghost: deletion transfers made when a lifetime was deleted -/
  delTr : Life → ℕ
  /-- ghost: all formations so far -/
  formLog : List FormRec

/-- The initial state: empty graph, no clusters, empty structures. -/
noncomputable def St.init : St where
  upd := 0
  H := SGraph.empty
  insTime := fun _ => 0
  clu := fun _ => none
  nextId := 0
  single := ∅
  aside := ∅
  lists := fun _ => []
  nextEntry := 0
  cnt := fun _ => 0
  stack := []
  clock := 0
  work := 0
  bud := fun _ => 0
  addedL := fun _ => ∅
  algAddedL := fun _ => ∅
  firstJoin := fun _ _ => none
  joins := fun _ _ => ∅
  attr := fun _ => 0
  passed := fun _ => 0
  incTr := fun _ => 0
  delTr := fun _ => 0
  formLog := []

namespace St

variable (s : St)

/-- The current lifetime of vertex `u`. -/
def life (u : ℕ) : Life := (u, s.insTime u)

/-- Lifetimes of a set of present vertices. -/
noncomputable def lifeSet (A : Finset ℕ) : Finset Life := A.image s.life

/-- `u` belongs to a maintained cluster. -/
def InCluster (u : ℕ) : Prop := ∃ k K, s.clu k = some K ∧ u ∈ K.mem

/-- `u` has an entry in the list `Ṽ_list,(i)`. -/
def InList (i u : ℕ) : Prop := ∃ e ∈ s.lists i, e.v = u

/-- No maintained cluster is due for refreshment or empty. -/
def NoPending (ε : ℝ) : Prop := ∀ k K, s.clu k = some K → ¬ K.Due ε ∧ K.mem.Nonempty

/-- All cluster operations and refreshments are complete: nothing is due, empty or set aside,
and no insertion test, placement or refresh task is pending. A level scan may still be pending. -/
def Settled (ε : ℝ) : Prop :=
  s.NoPending ε ∧ s.aside = ∅ ∧ ∀ task ∈ s.stack,
    match task with
    | .ins _ | .place _ | .refresh _ _ | .refreshLoop _ _ _ => False
    | _ => True

/-- The clusters checked by Theorem 3: maintained clusters and output singleton blocks omitted
from the active singleton pool (Section 6.6, p. 49). -/
def OutputCluster (K : Finset ℕ) : Prop :=
  (∃ k C, s.clu k = some C ∧ K = C.mem) ∨
    ∃ v ∈ s.H.V, v ∉ s.single ∧ ¬ s.InCluster v ∧ K = {v}

/-- Charged work for the whole algorithm. `work` records the subroutine allowances, `clock`
charges the control transitions, and the last term reserves a polynomial-time offline call per
update on at most `300 log⁴ n` vertices (Algorithm 4 (1)). The exponent `q` is any fixed degree
of a polynomial upper bound for that implementation, including its degree queries and
amplification. The constant-size branch is absorbed by the coefficient `κ`. This is an upper
accounting allowance, as are the individual subroutine charges, not a free computation oracle. -/
noncomputable def totalWork (n : ℕ) (κ : ℝ) (q : ℕ) : ℝ :=
  s.work + κ * (s.clock : ℝ) +
    κ * (s.upd : ℝ) * (1 + 300 * lgp n ^ 4) ^ q

/-- A returned time: the current update has been processed completely. -/
def Returned (ε : ℝ) : Prop := s.Settled ε ∧ s.stack = []

/-- Add `x` to the work. -/
def charge (x : ℝ) : St := { s with work := s.work + x }

/-- Add `x` to the work charged to cluster `k` (and to the total work). -/
def chargeTo (k : ℕ) (x : ℝ) : St :=
  { s with work := s.work + x, attr := Function.update s.attr k (s.attr k + x) }

/-- Advance the step counter. -/
def tick : St := { s with clock := s.clock + 1 }

/-- The vertices of `A` enter `Ṽ_singleton` (those not already in it are entries and are
counted by every `c_i`), and each vertex of `A` gets an entry, appended at the end, in every
list `Ṽ_list,(i)`, `i < L`, in which it has none (Algorithms 2–4). -/
noncomputable def enterSet (n : ℕ) (A : Finset ℕ) : St :=
  { s with
    single := s.single ∪ A
    cnt := fun i => s.cnt i + (A \ s.single).card
    lists := fun i =>
      if i < numLevels n then
        s.lists i ++ ((A.toList.filter (fun u => ¬ s.InList i u)).map
          (fun u => (⟨u, Nat.pair s.nextEntry (Nat.pair u i)⟩ : Entry)))
      else s.lists i
    nextEntry := s.nextEntry + 1 }

/-- The vertices of `A` leave `Ṽ_singleton` (departures, counted by every `c_i`) and all their
list entries are removed (Algorithm 4 (4a)). -/
noncomputable def leaveSet (A : Finset ℕ) : St :=
  { s with
    single := s.single \ A
    cnt := fun i => s.cnt i + (A ∩ s.single).card
    lists := fun i => (s.lists i).filter (fun e => e.v ∉ A) }

/-- Remove the vertices of `A` from every maintained cluster (algorithmic removals). -/
def dropFromClusters (A : Finset ℕ) : St :=
  { s with clu := fun k => (s.clu k).map (fun K => { K with mem := K.mem \ A }) }

/-- Add `v` to the maintained cluster `k = K` (a merge, Algorithm 1 (2a)iiA, Algorithm 3 (2a),
Algorithm 5 (2b)iiA): `v` leaves `Ṽ_singleton` and the set-aside vertices; `inc(K)` increases
iff `v` was inserted after `K` was formed and has not joined `K` before; the record of `v` in
`K` is created; the merge consumes `v`'s budget, and a first addition of `v` from outside
`K(t₀)` charges its record bookkeeping `κ lgp²` to `K`. -/
noncomputable def mergeInto (n : ℕ) (κ : ℝ) (k : ℕ) (K : Clu) (v : ℕ) : St :=
  let lv := s.life v
  let counted : Prop := K.formUpd < s.insTime v ∧ v ∉ K.incd
  let outside : Prop := lv ∉ K.init
  let first : Prop := outside ∧ lv ∉ s.addedL k
  let K' : Clu :=
    { K with
      mem := insert v K.mem
      ever := insert v K.ever
      inc := if counted then K.inc + 1 else K.inc
      incd := if counted then insert v K.incd else K.incd }
  let s1 := s.leaveSet {v}
  let s2 : St :=
    { s1 with
      clu := Function.update s1.clu k (some K')
      aside := s1.aside.erase v
      bud := Function.update s1.bud lv 0
      addedL := if outside then Function.update s1.addedL k (insert lv (s1.addedL k))
        else s1.addedL
      algAddedL := if outside ∧ s.insTime v ≤ K.formUpd then
          Function.update s1.algAddedL k (insert lv (s1.algAddedL k))
        else s1.algAddedL
      firstJoin := if s1.firstJoin k lv = none then
          Function.update s1.firstJoin k (Function.update (s1.firstJoin k) lv (some s.clock))
        else s1.firstJoin
      joins := Function.update s1.joins k
        (Function.update (s1.joins k) lv (insert s.clock (s1.joins k lv)))
      incTr := if counted then Function.update s1.incTr lv (s1.incTr lv + 1) else s1.incTr }
  if first then s2.chargeTo k (κ * lgp n ^ 2) else s2

/-- Algorithm 2: form the new cluster `C` (identifier `nextId`) from the vertex `v`, then process
the identified set `S`: an identified vertex in a maintained cluster `K'` with `|C| ≥ c(K')/2`
is removed from `K'` and enters `Ṽ_singleton` and all lists; an identified vertex in no cluster
enters `Ṽ_singleton` (if not already there) and all lists. Members of `C` leave
`Ṽ_singleton`, the set-aside vertices and their old clusters. Ghost: the formation record, the
members' first joins, the budgets (members' budgets are spent, each identified vertex removed
from a cluster receives `Φ`), and the formation work charged to the new cluster. -/
noncomputable def formCluster (n : ℕ) (κ ε : ℝ) (v : ℕ) (C S : Finset ℕ) : St :=
  let k := s.nextId
  let rec_ : FormRec :=
    ⟨k, C.card, s.H.deg v, (C.filter (fun u => 0 < s.bud (s.life u))).card,
      decide (0 < s.bud (s.life v))⟩
  let R := S.filter (fun u => ∃ k' K', s.clu k' = some K' ∧ u ∈ K'.mem ∧ K'.c ≤ 2 * C.card)
  let F := S.filter (fun u => ¬ s.InCluster u)
  let newK : Clu := ⟨C, s.lifeSet C, C.card, 0, 0, C, ∅, s.upd⟩
  let s1 := (s.leaveSet C).dropFromClusters C
  let s2 : St :=
    { s1 with
      clu := Function.update s1.clu k (some newK)
      nextId := k + 1
      aside := s1.aside \ C
      bud := fun l => if l ∈ s.lifeSet C then 0 else s1.bud l
      firstJoin := Function.update s1.firstJoin k
        (fun l => if l ∈ s.lifeSet C then some s.clock else none)
      joins := Function.update s1.joins k
        (fun l => if l ∈ s.lifeSet C then {s.clock} else ∅)
      formLog := s1.formLog ++ [rec_] }
  let s3 := (s2.dropFromClusters R).enterSet n (R ∪ F)
  let s4 : St :=
    { s3 with
      bud := fun l => if l ∈ s.lifeSet R then s3.bud l + 1 else s3.bud l
      passed := Function.update s3.passed k R.card }
  s4.chargeTo k (κ * (C.card : ℝ) * lgp n ^ 3 / ε ^ 2)

/-- The effect of receiving the deletion of `v` (see `Step.recvDel`). -/
noncomputable def receiveDel (n : ℕ) (κ : ℝ) (v : ℕ) : St :=
  let recs := {k | ∃ K, s.clu k = some K ∧ v ∈ K.ever}.ncard
  let s1 := ({ s with cnt := fun i => s.cnt i + 1 } : St).leaveSet {v}
  ({ s1 with
      upd := s.upd + 1
      H := s.H.apply (Update.del v)
      clu := fun k => (s1.clu k).map (fun K =>
        if v ∈ K.ever then
          { K with mem := K.mem.erase v, del := K.del + 1, ever := K.ever.erase v,
                   incd := K.incd.erase v }
        else { K with mem := K.mem.erase v })
      delTr := Function.update s1.delTr (s.life v) recs
      stack := [Task.alg4] } : St).charge (κ * lgp n ^ 2 * (1 + recs))

end St

/-! ## Success guarantees of the randomized subroutines -/

/-- A sparsity test at `θ` may answer `yes` only on a `0.9θ`-sparse vertex and `no` only on a
vertex that is not `θ`-sparse (Lemma 3.1 with `η = 1/10`). -/
def TestOK (H : SGraph) (θ : ℝ) (v : ℕ) (yes : Bool) : Prop :=
  (yes = true → H.Sparse ((9 / 10) * θ) v) ∧ (yes = false → ¬ H.Sparse θ v)

/-- `K` has a `θ`-dense core (Definition 7: a subset that is a `θ`-almost-clique) of size at
least `frac · |K|`, containing `w` when `w` is given. -/
def HasCore (H : SGraph) (θ frac : ℝ) (K : Finset ℕ) (w : Option ℕ) : Prop :=
  ∃ C ⊆ K, H.IsAlmostClique θ C ∧ frac * (K.card : ℝ) ≤ (C.card : ℝ) ∧
    ∀ x, w = some x → x ∈ C

/-- The merge of Lemma 3.2 forced: `deg(v) ≥ 10/ε` and some maintained cluster `C` has
`|N(v) \ C| < 3ε deg(v)` and `|C| ≤ (1 + 4ε) deg(v)`. -/
def MergeForced (s : St) (ε : ℝ) (v : ℕ) : Prop :=
  10 / ε ≤ (s.H.deg v : ℝ) ∧
    ∃ k K, s.clu k = some K ∧
      (((s.H.nbr v \ K.mem).card : ℕ) : ℝ) < 3 * ε * s.H.deg v ∧
      (K.mem.card : ℝ) ≤ (1 + 4 * ε) * s.H.deg v

/-- An outcome "merge `v` into the maintained cluster `k = K`" allowed by Lemma 3.2. -/
def MergeOK (s : St) (ε : ℝ) (v k : ℕ) (K : Clu) : Prop :=
  s.clu k = some K ∧ 10 / ε ≤ (s.H.deg v : ℝ) ∧
    (((s.H.nbr v \ K.mem).card : ℕ) : ℝ) ≤ (16 / 5) * ε * s.H.deg v ∧
    (K.mem.card : ℝ) ≤ (1 + 4 * ε) * s.H.deg v ∧
    HasCore s.H (4 * ε) (1 - 8 * ε) K.mem none ∧
    HasCore s.H (4 * ε) (1 - 8 * ε) (insert v K.mem) (some v)

/-- An outcome "form the cluster `C` from `v`" allowed by Lemma 3.2. -/
def FormOK (s : St) (ε : ℝ) (v : ℕ) (C : Finset ℕ) : Prop :=
  v ∈ C ∧ s.H.IsAlmostClique (ε / 2) C ∧
    (1 - ε / 20) * ((s.H.cnbr v).card : ℝ) ≤ (C.card : ℝ) ∧
    (C.card : ℝ) ≤ (1 + (51 / 1000) * ε) * ((s.H.cnbr v).card : ℝ) ∧
    (∀ u ∈ s.H.V, s.H.Agree (ε / 5) u v → u ∈ C) ∧
    (∀ u ∈ C, ¬ s.H.Sparse (2 * ε) u) ∧
    ((s.H.deg v : ℝ) < 10 / ε → C = s.H.cnbr v ∧ ∀ u ∈ C, s.H.cnbr u = C) ∧
    ¬ MergeForced s ε v

/-- An identified set allowed by Lemma 3.3 with `δ = 1/2`, `γ = 1/4` for the new cluster `C`. -/
def IdentOK (H : SGraph) (C S : Finset ℕ) : Prop :=
  S ⊆ H.V \ C ∧
    (∀ u ∈ H.V \ C, (C.card : ℝ) / 2 ≤ (((H.nbr u ∩ C).card : ℕ) : ℝ) → u ∈ S) ∧
    (∀ u ∈ S, (C.card : ℝ) / 4 < (((H.nbr u ∩ C).card : ℕ) : ℝ))

/-- The `θ`-dense vertices of degree level `j` of `Ṽ_singleton`. -/
noncomputable def denseAt (s : St) (n : ℕ) (θ : ℝ) (j : ℤ) : Finset ℕ :=
  (s.H.bucket n s.single j).filter (fun v => ¬ s.H.Sparse θ v)

/-- `ξ = |Ṽ_singleton| / (1000 · 2^i L)` (proof of Lemma 7.1). -/
noncomputable def xiAt (s : St) (n i : ℕ) : ℝ :=
  (s.single.card : ℝ) / (1000 * 2 ^ i * numLevels n)

/-- Estimate `ū_i` of the `5ζ`-dense singleton vertices of levels `S_i(3)` (Algorithm 4 (4b)ii),
within the bounds of Lemma 7.1 (p. 50). -/
def EstDenseOK (s : St) (n : ℕ) (ε : ℝ) (i : ℕ) (x : ℝ) : Prop :=
  let ζ := zeta ε
  let w (θ : ℝ) : Finset ℕ :=
    denseAt s n θ ((i : ℤ) - 1) ∪ denseAt s n θ i ∪ denseAt s n θ ((i : ℤ) + 1)
  (9 / 10) * ((w ((9 / 2) * ζ)).card : ℝ) - xiAt s n i ≤ x ∧
    x ≤ (11 / 10) * ((w (5 * ζ)).card : ℝ) + xiAt s n i

/-- Estimate `ū'_j` of the singleton vertices of level `j` passing the `5ζ` test, made with the
sample size of level `i` (Algorithm 4 (4b)v–vi), within the bounds of Lemma 7.1. -/
def EstSparseOK (s : St) (n : ℕ) (ε : ℝ) (i j : ℕ) (x : ℝ) : Prop :=
  let ζ := zeta ε
  (9 / 10) * (((s.H.bucket n s.single j \ denseAt s n (5 * ζ) j).card : ℕ) : ℝ) - xiAt s n i ≤ x ∧
    x ≤ (11 / 10) * (((s.H.bucket n s.single j \ denseAt s n ((9 / 2) * ζ) j).card : ℕ) : ℝ) +
      xiAt s n i

/-- The ordered list `{L − 1, L − 2, …, max {0, i − 4}} \ {i}` of Algorithm 4 (4b)vi. -/
def jOrder (n i : ℕ) : List ℕ :=
  (List.range (numLevels n)).reverse.filter (fun j => (i : ℤ) - 4 ≤ (j : ℤ) ∧ j ≠ i)

/-- `FLAG_i` and the number of size estimates performed, from the estimates `ū_i`, `ū'_i` and
`ū_j` (Algorithm 4 (4b)iii–vi; the loop of vi stops at the first `j` with `ū_j > 100 L ū_i`). -/
noncomputable def checkFlag (s : St) (n i : ℕ) (u u' : ℝ) (est : ℕ → ℝ) : Bool × ℕ :=
  let L := numLevels n
  let js := jOrder n i
  let stop := fun j => 100 * (L : ℝ) * u < est j
  let before := (js.takeWhile (fun j => ¬ stop j)).length
  let f3 := decide (∃ j ∈ js, stop j)
  (decide (u < (s.single.card : ℝ) / (100 * 2 ^ i * L)) || decide (u < u' / 5) || f3,
    2 + (if f3 then before + 1 else before))

/-- The first entry of `Ṽ_list,(i)` (in list order) not yet visited by the current scan. -/
def firstUnvisited (s : St) (i : ℕ) (visited : Finset ℕ) : Option Entry :=
  (s.lists i).find? (fun e => e.id ∉ visited)

/-! ## The transition relation -/

/-- One step of Algorithms 1–7 on the stream `us`, with vertex bound `n`, accuracy `ε` and cost
constant `κ`. -/
inductive Step (n : ℕ) (ε κ : ℝ) (us : List Update) : St → St → Prop where
  /-- Remove a maintained cluster that is due for refreshment or empty (Remark 5.3; Lemma 8.1:
  emptied clusters are discarded). A due cluster's members are set aside, each receives a
  budget `Φ` (Section 8.3), and its refreshment (Algorithm 3) is started on top of the stack. -/
  | remove (s : St) (k : ℕ) (K : Clu) :
      s.clu k = some K → (K.Due ε ∨ K.mem = ∅) →
      Step n ε κ us s
        (({ s with
            clu := Function.update s.clu k none
            aside := s.aside ∪ K.mem
            bud := fun l => if l ∈ s.lifeSet K.mem then s.bud l + 1 else s.bud l
            stack := if K.mem = ∅ then s.stack else Task.refresh k K.mem :: s.stack }).chargeTo
          k (κ * ((K.mem.card : ℝ) + 1) * lgp n ^ 2)).tick
  /-- Receive an insertion (Algorithm 1 (2a); Algorithm 4 (3)): the graph is updated, every
  `c_i` counts the update, the new lifetime gets its budget, and the vertex is processed. -/
  | recvIns (s : St) (v : ℕ) (P : Finset ℕ) (h : s.upd < us.length) :
      s.stack = [] → s.NoPending ε → us[s.upd]'h = Update.ins v P →
      Step n ε κ us s
        (({ s with
            upd := s.upd + 1
            H := s.H.apply (Update.ins v P)
            insTime := Function.update s.insTime v (s.upd + 1)
            cnt := fun i => s.cnt i + 1
            bud := Function.update s.bud (v, s.upd + 1) 1
            stack := [Task.ins v, Task.alg4] }).charge (κ * lgp n ^ 2)).tick
  /-- Receive a deletion (Algorithm 1 (2b); Lemma 8.1): the graph is updated, every `c_i` counts
  it, `v` leaves `Ṽ_singleton` and its lists (a departure) and its cluster, and every maintained
  cluster that `v` ever joined increases `del` and drops its record of `v`. -/
  | recvDel (s : St) (v : ℕ) (h : s.upd < us.length) :
      s.stack = [] → s.NoPending ε → us[s.upd]'h = Update.del v →
      Step n ε κ us s ((s.receiveDel n κ v).tick)
  /-- Algorithm 1 (2a)i–ii: the `ε/20` sparsity test answers yes; `v` enters `Ṽ_singleton`. -/
  | insYes (s : St) (v : ℕ) (rest : List Task) :
      s.stack = Task.ins v :: rest → s.NoPending ε → TestOK s.H (ε / 20) v true →
      Step n ε κ us s
        ((({ s with stack := rest }.enterSet n {v}).charge
          (κ * lgp n ^ 2 / (ε / 20) ^ 2 + κ * lgp n ^ 2))).tick
  /-- Algorithm 1 (2a)ii: the test answers no; merge or form (Lemma 3.2). -/
  | insNo (s : St) (v : ℕ) (rest : List Task) :
      s.stack = Task.ins v :: rest → s.NoPending ε → TestOK s.H (ε / 20) v false →
      Step n ε κ us s
        (({ s with stack := Task.place v :: rest }).charge (κ * lgp n ^ 2 / (ε / 20) ^ 2)).tick
  /-- Lemma 3.2, merge outcome. -/
  | placeMerge (s : St) (v k : ℕ) (K : Clu) (rest : List Task) :
      s.stack = Task.place v :: rest → s.NoPending ε → MergeOK s ε v k K →
      Step n ε κ us s
        ((({ s with stack := rest }.mergeInto n κ k K v).charge (κ * lgp n ^ 2 / ε ^ 2))).tick
  /-- Lemma 3.2, formation outcome, followed by identification (Algorithm 2). -/
  | placeForm (s : St) (v : ℕ) (C S : Finset ℕ) (rest : List Task) :
      s.stack = Task.place v :: rest → s.NoPending ε → FormOK s ε v C → IdentOK s.H C S →
      Step n ε κ us s (({ s with stack := rest }.formCluster n κ ε v C S)).tick
  /-- Algorithm 3 (2): the `ε/20` sparsity test on every remaining set-aside member;
  `no` is the set answering no. -/
  | refreshTest (s : St) (k : ℕ) (vs no : Finset ℕ) (rest : List Task) :
      s.stack = Task.refresh k vs :: rest → s.NoPending ε → no ⊆ vs ∩ s.aside →
      (∀ u ∈ vs ∩ s.aside, TestOK s.H (ε / 20) u (decide (u ∉ no))) →
      Step n ε κ us s
        (({ s with stack := Task.refreshLoop k no vs :: rest }).chargeTo k
          (κ * ((vs ∩ s.aside).card : ℝ) * lgp n ^ 2 / (ε / 20) ^ 2)).tick
  /-- Algorithm 3 (2): repeat on a still set-aside vertex whose test answered no. -/
  | refreshPick (s : St) (k : ℕ) (no all : Finset ℕ) (v : ℕ) (rest : List Task) :
      s.stack = Task.refreshLoop k no all :: rest → s.NoPending ε → v ∈ no ∩ s.aside →
      Step n ε κ us s
        ({ s with stack := Task.place v :: Task.refreshLoop k (no.erase v) all :: rest }).tick
  /-- Algorithm 3 (3): the members still set aside enter `Ṽ_singleton` and all lists. -/
  | refreshEnd (s : St) (k : ℕ) (no all : Finset ℕ) (rest : List Task) :
      s.stack = Task.refreshLoop k no all :: rest → s.NoPending ε → no ∩ s.aside = ∅ →
      Step n ε κ us s
        ((({ s with stack := rest, aside := s.aside \ all }.enterSet n (all ∩ s.aside)).chargeTo k
          (κ * ((all ∩ s.aside).card : ℝ) * lgp n ^ 2))).tick
  /-- Algorithm 4 (4b) and Algorithm 7 (3b): check a level `i` with `c_i ≥ h_i`: reset `c_i`,
  draw the size estimates, set `FLAG_i`, and start Algorithm 5 on `Ṽ_list,(i)`. -/
  | check (s : St) (i : ℕ) (t : Task) (rest : List Task) (u u' : ℝ) (est : ℕ → ℝ) :
      s.stack = t :: rest → (t = Task.alg4 ∨ t = Task.alg7checks) → s.NoPending ε →
      i < numLevels n → hThr ε i ≤ s.cnt i →
      EstDenseOK s n ε i u → EstSparseOK s n ε i i u' →
      (∀ j ∈ jOrder n i, EstSparseOK s n ε i j (est j)) →
      Step n ε κ us s
        (({ s with
            cnt := Function.update s.cnt i 0
            stack := Task.scan i (checkFlag s n i u u' est).1 0 ∅ :: t :: rest }).charge
          (κ * ((checkFlag s n i u u' est).2 : ℝ) * 2 ^ i * lgp n ^ 5 / ε ^ 2)).tick
  /-- Algorithm 4 (4c): every `c_i < h_i`; run Algorithm 7. -/
  | alg4Done (s : St) (rest : List Task) :
      s.stack = Task.alg4 :: rest → s.NoPending ε →
      (∀ i < numLevels n, s.cnt i < hThr ε i) →
      Step n ε κ us s ({ s with stack := Task.alg7 :: rest }).tick
  /-- Algorithm 5 (3): no unvisited entry remains. -/
  | scanDone (s : St) (i : ℕ) (fl : Bool) (fail : ℕ) (vis : Finset ℕ) (rest : List Task) :
      s.stack = Task.scan i fl fail vis :: rest → s.NoPending ε → firstUnvisited s i vis = none →
      Step n ε κ us s ({ s with stack := rest }).tick
  /-- Algorithm 5 (2a): a visited vertex of degree below `2^i/10` is deleted from the list. -/
  | scanPrune (s : St) (i : ℕ) (fl : Bool) (fail : ℕ) (vis : Finset ℕ) (rest : List Task)
      (e : Entry) :
      s.stack = Task.scan i fl fail vis :: rest → s.NoPending ε →
      firstUnvisited s i vis = some e → (s.H.deg e.v : ℝ) < 2 ^ i / 10 →
      Step n ε κ us s
        (({ s with
            lists := Function.update s.lists i ((s.lists i).filter (fun e' => e'.id ≠ e.id))
            stack := Task.scan i fl fail (insert e.id vis) :: rest }).charge (κ * lgp n)).tick
  /-- Algorithm 5 (2b)i and (2c): the `12ζ` test answers yes; `FAIL_i` increases, and a partial
  scan stops when `FAIL_i = 2^i L²`. -/
  | scanYes (s : St) (i : ℕ) (fl : Bool) (fail : ℕ) (vis : Finset ℕ) (rest : List Task)
      (e : Entry) :
      s.stack = Task.scan i fl fail vis :: rest → s.NoPending ε →
      firstUnvisited s i vis = some e → 2 ^ i / 10 ≤ (s.H.deg e.v : ℝ) →
      TestOK s.H (12 * zeta ε) e.v true →
      Step n ε κ us s
        (({ s with
            stack :=
              if fl = true ∧ fail + 1 = 2 ^ i * numLevels n ^ 2 then rest
              else Task.scan i fl (fail + 1) (insert e.id vis) :: rest }).charge
          (κ * lgp n ^ 2 / (12 * zeta ε) ^ 2)).tick
  /-- Algorithm 5 (2b)ii: the `12ζ` test answers no; merge or form, then continue the scan. -/
  | scanNo (s : St) (i : ℕ) (fl : Bool) (fail : ℕ) (vis : Finset ℕ) (rest : List Task)
      (e : Entry) :
      s.stack = Task.scan i fl fail vis :: rest → s.NoPending ε →
      firstUnvisited s i vis = some e → 2 ^ i / 10 ≤ (s.H.deg e.v : ℝ) →
      TestOK s.H (12 * zeta ε) e.v false →
      Step n ε κ us s
        (({ s with stack := Task.place e.v :: Task.scan i fl fail (insert e.id vis) :: rest }).charge
          (κ * lgp n ^ 2 / (12 * zeta ε) ^ 2)).tick
  /-- Algorithm 7 with `Ṽ_singleton = ∅` (an empty sample pool): nothing to clean. -/
  | alg7Empty (s : St) (rest : List Task) :
      s.stack = Task.alg7 :: rest → s.NoPending ε → s.single = ∅ →
      Step n ε κ us s ({ s with stack := rest }).tick
  /-- Algorithm 7 (1)–(2): the estimated degree-zero fraction (additive error `1/100`) is below
  `1/20`. -/
  | alg7Low (s : St) (rest : List Task) (f : ℝ) :
      s.stack = Task.alg7 :: rest → s.NoPending ε → s.single ≠ ∅ →
      |f - ((s.single.filter (fun v => s.H.deg v = 0)).card : ℝ) / (s.single.card : ℝ)| ≤ 1 / 100 →
      f < 1 / 20 →
      Step n ε κ us s (({ s with stack := rest }).charge (κ * lgp n ^ 2)).tick
  /-- Algorithm 7 (3a): traverse `Ṽ_singleton` and remove its degree-zero vertices from it and
  from all lists (they remain singleton clusters of the output), then (3b). -/
  | alg7Traverse (s : St) (rest : List Task) (f : ℝ) :
      s.stack = Task.alg7 :: rest → s.NoPending ε → s.single ≠ ∅ →
      |f - ((s.single.filter (fun v => s.H.deg v = 0)).card : ℝ) / (s.single.card : ℝ)| ≤ 1 / 100 →
      1 / 20 ≤ f →
      Step n ε κ us s
        ((({ s with stack := Task.alg7checks :: rest }.leaveSet
            (s.single.filter (fun v => s.H.deg v = 0))).charge
          (κ * lgp n ^ 2 * (1 + s.single.card)))).tick
  /-- Algorithm 7 (3b) finished: every `c_i < h_i`. -/
  | alg7ChecksDone (s : St) (rest : List Task) :
      s.stack = Task.alg7checks :: rest → s.NoPending ε →
      (∀ i < numLevels n, s.cnt i < hThr ε i) →
      Step n ε κ us s ({ s with stack := rest }).tick

/-- `s` is reachable on the stream `us` (an execution prefix in which every randomized
subroutine met its guarantee). -/
def Reach (n : ℕ) (ε κ : ℝ) (us : List Update) (s : St) : Prop :=
  Relation.ReflTransGen (Step n ε κ us) St.init s

/-- `r 0, …, r T` is an execution prefix. -/
def IsRun (n : ℕ) (ε κ : ℝ) (us : List Update) (r : ℕ → St) (T : ℕ) : Prop :=
  r 0 = St.init ∧ ∀ j < T, Step n ε κ us (r j) (r (j + 1))

end FullyDynamicCorrelation.VertexUpdates


