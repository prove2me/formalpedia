-- Prove2me | Definitions.Def_WindowedMatching_PostponedGreedy
-- name    : WindowedMatching_PostponedGreedy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:56.939662+00:00
-- url     : https://prove2.me/theorems/a36b6c60-bfc7-43a5-9fda-3923a50a520b
-- title:
--   Algorithm 3 — Postponed Greedy on the online graph
-- statement:
--   This module defines Postponed Greedy (Algorithm 3, p.7). Each vertex $k$ has a virtual seller $s_k$ and a virtual buyer $b_k$. The state holds the seller and buyer sets $S_t$, $B_t$, the prices $p(s_k)$, the tentative matches $m(s_k)$, the margins $q(b_k)$, a status for each vertex (undetermined, seller or buyer), and the list of finalized pairs.
--
--   **Arrival of a vertex $k$** (step 1).
--
--   1. Set $k$'s status to undetermined, add $s_k$ to $S_t$ with $p(s_k)=0$ and $m(s_k)=\emptyset$, and add $b_k$ to $B_t$.
--   2. Let $s=\operatorname{argmax}_{s'\in S_t}\,(v_{s',b_k}-p(s'))$, and record the maximal margin as $q(b_k)$.
--   3. If $v_{s,b_k}-p(s)>0$, set $m(s)=b_k$ and $p(s)=v_{s,b_k}$.
--
--   **Vertex $k$ becomes critical** (step 2).
--
--   1. If $m(s_k)=\emptyset$, do nothing.
--   2. If $m(s_k)=b_l$, remove $s_k$ from $S_t$ and $b_l$ from $B_t$.
--   3. If $k$ is undetermined, a fair coin sets its status to seller or buyer.
--   4. If $k$ is a seller, finalize $(k,l)$, which collects $v_{k,l}$, and set $l$'s status to buyer. If $k$ is a buyer, set $l$'s status to seller.
--
--   In period $t$, vertex $t$ arrives if $t<n$, and then vertex $t-d$ becomes critical if it exists. The run lasts $n+d$ periods. The **reward** of a run is the sum of $v_{k,l}$ over the finalized pairs, and $\mathrm{PG}$ is its expectation over $n$ independent fair coins:
--   $$\mathrm{PG}=\frac1{2^n}\sum_{\omega\in\{0,1\}^n}\mathrm{reward}(\omega).$$
--
--   **Formalization Note** Within a period, the arrival precedes the criticality. The $\operatorname{argmax}$ is a free rule `tie`; the predicate `IsArgmaxRule` says that it chooses a maximizer. It sees the arriving vertex, the seller set and the margins of the sellers in the set, and it sees no coin. The seller set is never empty in step 1(d), since it contains $s_k$. The margin $q$ is written only for the proof; no decision reads it. A displaced buyer does not bid again. The status of a vertex that has not arrived is undetermined. The printed step 1(d) reads "virtual seller for the virtual seller", a typo for "virtual buyer".
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, Algorithm 3, p.7; virtual copies and statuses, p.6; q(b), p.7

import Definitions.Def_WindowedMatching_OnlineGraph

namespace WindowedMatching

/-! # Postponed Greedy (Algorithm 3, Ashlagi et al., arXiv:1808.03526v1, p.7)

One state machine holding the virtual run and the vertex statuses together, as the algorithm is
printed, with one run on the online graph `G_{d,σ}` and one outcome `ω` of the coins.

**Formalization Note.**
1. Vertices are `Fin n`, 0-based: vertex `k` arrives in period `k` and becomes critical in period
   `k + d`. A seller `s_k` and a buyer `b_k` are both represented by `k`.
2. Within a period, the arrival is processed before the criticality. The run lasts `n + d` periods
   (`0, …, n + d − 1`), so that every vertex becomes critical.
3. `argmax` in step 1(d) is an arbitrary rule `tie` choosing a maximizer. It sees the arriving vertex,
   the seller set and the margins of the sellers in that set. It sees no coin.
4. The coins are `ω : Fin n → Bool`, one per vertex, with `true` meaning seller. Coin `ω k` is read
   only if `k` is undetermined when step 2(c) processes it.
5. `q` is the margin `q(b)` of the proof (p.7). No decision of the algorithm reads it.
6. The status of a vertex that has not arrived is `undetermined`; step 1(a) sets the same value. -/

/-- The status of a vertex in Postponed Greedy (arXiv:1808.03526v1, p.6). -/
inductive Status where
  | undetermined
  | seller
  | buyer
  deriving DecidableEq, Repr

/-- The state of a run of Postponed Greedy (arXiv:1808.03526v1, Algorithm 3, p.7).

* `S`, `B`: the sets `S_t`, `B_t` of virtual sellers and virtual buyers;
* `p`: the prices `p(s_k)`;
* `m`: the tentative matches, with `m k = some l` for `m(s_k) = b_l` and `none` for `m(s_k) = ∅`;
* `q`: the margins `q(b_k)` (p.7);
* `status`: the status of each vertex;
* `finalized`: the pairs `(k, l)` finalized in step 2(c)i, in the order of finalization. -/
@[ext]
structure State (n : ℕ) where
  S : Finset (Fin n)
  B : Finset (Fin n)
  p : Fin n → ℝ
  m : Fin n → Option (Fin n)
  q : Fin n → ℝ
  status : Fin n → Status
  finalized : List (Fin n × Fin n)

/-- The state before period `0`: no vertex has arrived. -/
def State.init (n : ℕ) : State n where
  S := ∅
  B := ∅
  p := fun _ => 0
  m := fun _ => none
  q := fun _ => 0
  status := fun _ => .undetermined
  finalized := []

/-- A tie-breaking rule for `argmax` in step 1(d): it maps the arriving vertex, the seller set and
the margins to a seller. It takes no coin. -/
def TieRule (n : ℕ) : Type := Fin n → Finset (Fin n) → (Fin n → ℝ) → Fin n

/-- `tie` chooses a maximizer: `tie k S f = argmax_{s ∈ S} f s` for every nonempty `S`
(arXiv:1808.03526v1, Algorithm 3, step 1(d), p.7). -/
def IsArgmaxRule {n : ℕ} (tie : TieRule n) : Prop :=
  ∀ (k : Fin n) (S : Finset (Fin n)) (f : Fin n → ℝ),
    S.Nonempty → tie k S f ∈ S ∧ ∀ s ∈ S, f s ≤ f (tie k S f)

variable {n : ℕ}

/-- Steps 1(a)–(c) for vertex `k`: `k`'s status is undetermined, `S_t ← S_{t−1} ∪ {s_k}`,
`p(s_k) ← 0`, `m(s_k) = ∅`, `B_t ← B_{t−1} ∪ {b_k}` (arXiv:1808.03526v1, Algorithm 3, p.7). -/
def addVertex (k : Fin n) (st : State n) : State n :=
  { st with
    status := Function.update st.status k .undetermined
    S := insert k st.S
    p := Function.update st.p k 0
    m := Function.update st.m k none
    B := insert k st.B }

/-- The margins `v_{s,b_k} − p(s)` for the sellers `s ∈ S_t` (arXiv:1808.03526v1, Algorithm 3,
step 1(d), p.7).

**Formalization Note.** Outside the seller set the row is `0`, so the row reads no weight of a
vertex that has not arrived. -/
noncomputable def margins (d : ℕ) (v : Sym2 (Fin n) → ℝ) (k : Fin n) (st : State n) :
    Fin n → ℝ :=
  fun s => if s ∈ st.S then onlineWeight d v s k - st.p s else 0

/-- Steps 1(d)–(e) for the buyer `b_k`: `s = argmax_{s' ∈ S_t} v_{s',b_k} − p(s')`, recording the
maximal margin as `q(b_k)`, and if `v_{s,b_k} − p(s) > 0`, setting `m(s) ← b_k` and
`p(s) ← v_{s,b_k}` (arXiv:1808.03526v1, Algorithm 3, p.7; `q`: p.7).

**Formalization Note.** Line 1(d) of the page reads "Find a virtual seller for the virtual seller",
a typo for "virtual buyer". -/
noncomputable def bid (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n)
    (st : State n) : State n :=
  let row := margins d v k st
  let s := tie k st.S row
  let st' := { st with q := Function.update st.q k (row s) }
  if 0 < row s then
    { st' with
      m := Function.update st.m s (some k)
      p := Function.update st.p s (onlineWeight d v s k) }
  else st'

/-- Step 1 of Algorithm 3: the arrival of vertex `k` (arXiv:1808.03526v1, p.7). -/
noncomputable def arrive (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (k : Fin n)
    (st : State n) : State n :=
  bid d v tie k (addVertex k st)

/-- Step 2 of Algorithm 3: vertex `k` becomes critical (arXiv:1808.03526v1, p.7).

* Step 2(a): if `m(s_k) = ∅`, do nothing.
* Step 2(b): if `m(s_k) = b_l`, set `S_t ← S_t \ {s_k}` and `B_t ← B_t \ {b_l}`.
* Step 2(c): if `k` is undetermined, its status becomes seller or buyer according to `ω k`.
* Step 2(c)i: if `k` is a seller, finalize `(k, l)` and set `l`'s status to buyer.
* Step 2(c)ii: if `k` is a buyer, set `l`'s status to seller. -/
def critical (ω : Fin n → Bool) (k : Fin n) (st : State n) : State n :=
  match st.m k with
  | none => st
  | some l =>
    let st' := { st with S := st.S.erase k, B := st.B.erase l }
    let isSeller : Bool :=
      match st.status k with
      | .undetermined => ω k
      | .seller => true
      | .buyer => false
    if isSeller then
      { st' with
        status := Function.update (Function.update st.status k .seller) l .buyer
        finalized := st.finalized ++ [(k, l)] }
    else
      { st' with
        status := Function.update (Function.update st.status k .buyer) l .seller }

/-- The events of period `t`: the arrival of vertex `t` if `t < n`, then the criticality of vertex
`t − d` if `d ≤ t` and `t − d < n`. -/
noncomputable def period (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (ω : Fin n → Bool)
    (t : ℕ) (st : State n) : State n :=
  let st₁ := if h : t < n then arrive d v tie ⟨t, h⟩ st else st
  if h : d ≤ t ∧ t - d < n then critical ω ⟨t - d, h.2⟩ st₁ else st₁

/-- The state after `t` periods, that is, after periods `0, …, t − 1`. -/
noncomputable def stateAfter (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) (ω : Fin n → Bool) :
    ℕ → State n
  | 0 => State.init n
  | t + 1 => period d v tie ω t (stateAfter d v tie ω t)

/-- The state at the end of the run, after the `n + d` periods in which every vertex arrives and
becomes critical. The superscript `f` of the paper's `p^f`, `m^f` refers to this state. -/
noncomputable def finalState (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n)
    (ω : Fin n → Bool) : State n :=
  stateAfter d v tie ω (n + d)

/-- The reward of a run: the sum of `v_{k,l}` over the pairs finalized in step 2(c)i
(arXiv:1808.03526v1, Algorithm 3, p.7). -/
noncomputable def reward (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n)
    (ω : Fin n → Bool) : ℝ :=
  ((finalState d v tie ω).finalized.map fun e => v s(e.1, e.2)).sum

/-- `PG`: the expected reward over `n` independent fair coins (arXiv:1808.03526v1, p.6). -/
noncomputable def expectedReward (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n) : ℝ :=
  (1 / 2 ^ n : ℝ) * ∑ ω : Fin n → Bool, reward d v tie ω

end WindowedMatching


