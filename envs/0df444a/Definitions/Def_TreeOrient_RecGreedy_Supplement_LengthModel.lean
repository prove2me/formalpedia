-- Prove2me | Definitions.Def_TreeOrient_RecGreedy_Supplement_LengthModel
-- name    : TreeOrient_RecGreedy_Supplement_LengthModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:52:29.836941+00:00
-- url     : https://prove2.me/theorems/75e410cd-8433-4178-a8c6-82f3cf6e8f5d
-- title:
--   §4.1, Algorithm 3, §4.1.1 — STO with length constraints and the recursive greedy RG-DC(r, k_r, Y, D, B, L, X, i)
-- statement:
--   **STO with length constraints** (§4.1). Besides a submodular tree orienteering instance (vertices $\{0,\dots,n-1\}$, root $r^*$, edge costs $c$, budget $B$, monotone submodular reward $f$), an instance carries an edge length $\ell(u,v)\in\mathbb Z_{\ge0}$ and a bound $L$. For an edge set $T$ and a vertex $w$, $l_T(w)$ is the least total length of a directed walk from the root of $T$ to $w$ along edges of $T$; in an arborescence it is the length of the unique root–$w$ path. For an offset $k_r$ (the length from $r^*$ to the current root $r$) the **length sum** is
--
--   $$\Lambda_{k_r}(T)=\sum_{w\in V(T)\setminus\{r\}}\bigl(k_r+l_T(w)\bigr).$$
--
--   The goal is an $r^*$-rooted arborescence $T$ maximizing $f(V(T))$ subject to $c(T)\le B$ and $\Lambda_0(T)\le L$.
--
--   **Compatibility and feasibility** (Lemma 4.2). An arborescence $T^*$ is compatible with $(r,k_r,Y,D,B,L,X)$ and the size cap $q$ if it is $r$-rooted, visits every vertex of $Y$, has at most $q$ non-root vertices, has cost at most $B$ and length sum $\Lambda_{k_r}(T^*)\le L$, and satisfies $l_{T^*}(w)\le D(w)$ for every $w\in Y\setminus\{r\}$. An output edge set $T$ is feasible for these parameters if every vertex of $T$ is reachable from $r$, $c(T)\le B$, $Y\subseteq V(T)$, and $T$ contains an $r$-rooted arborescence on the same vertex set with length sum at most $L$ that respects $D$ on $Y$.
--
--   **Algorithm 3**, $RG\text{-}DC(r,k_r,Y,D,B,L,X,i)$. If $|Y|>(3/2)^i$ it returns Infeasible. At depth $1$: if $Y=\emptyset$ it returns the best of $\emptyset$ and the single edges $(r,v)$ with $c(r,v)\le B$ and $k_r+\ell(r,v)\le L$, by $f_X$; if $Y=\{v\}$ it returns $\{(r,v)\}$ when $c(r,v)\le B$, $k_r+\ell(r,v)\le L$ and $\ell(r,v)\le D(v)$, and Infeasible otherwise. At depth $i\ge2$ it guesses a separator $v$, responsibilities $S\subseteq Y$, a cost budget $B_1$, a length budget $L_1$ and a length $d_1$ from $r$ to $v$; it sets $D_1=D$ on $S$, $D_1(v)=\min\{d_1,D(v)\}$ if $v\in Y$ and $D_1(v)=d_1$ otherwise, and $D_2=D-d_1$; it computes
--
--   $$T_1=RG\text{-}DC\bigl(r,k_r,(S\cup\{v\})\setminus\{r\},D_1,B_1,L_1,X,i-1\bigr),$$
--   $$T_2=RG\text{-}DC\bigl(v,k_r+l_{T_1}(v),Y\setminus(S\cup\{v\}),D_2,B-B_1,L-L_1,X\cup V(T_1),i-1\bigr),$$
--
--   and returns the best union $T_1\cup T_2$ by $f_X$, starting from $\emptyset$ when $Y=\emptyset$.
--
--   **Grouped version** (§4.1.1). With $s$ grouped levels, one call guesses every quantity of $s$ levels of Algorithm 3 and keeps the best combined result; the size cap is $(3/2)^{si}$, and at grouped depth one the call keeps the best arborescence with at most $\lfloor(3/2)^s\rfloor$ edges that passes every compatibility check. In the binary-search mode the cost budget of a subproblem is the least $b$ whose result has $f_X$ at least a guessed threshold $u\in[0,U]$; length budgets and the lengths $d_1$ are always enumerated.
--
--   The algorithm of Theorem 4.3 is Algorithm 3 with depth $d=2\lceil\log_2k\rceil$ called from $(r^*,0,\emptyset)$; the algorithm of Theorem 1.2 is the grouped version with $s=\max\{1,\lceil\varepsilon\log_2\log_2k\rceil\}$, binary search with $U=n^a$, and depth $\lceil d/s\rceil$.
--
--   **Formalization Note** The model reuses the published `TreeOrient.RecGreedy.Model` (`Inst`, `verts`, `cost`, `fX`, `IsArbo`, `Feasible`, `Compatible`, `capImp`, `Mode`, `bsearch`, `chooseBest`, `edgeCandidates`, `dOf`, `sOf`, `depthOf`). Lengths and $L$ are natural numbers, zero allowed. The guesses $B_1$, $L_1$, $d_1$ start at $0$, as the published budgets do, so that zero costs and zero lengths are covered. A guess with $d_1>D(w)$ for some $w\in Y\setminus(S\cup\{v\})$ is skipped, because $D(w)-d_1$ would be negative; this keeps $D_2$ in $\mathbb N$ without truncation. The bound $D(v)$ of a separator $v\in Y$ is kept in $D_1(v)=\min\{d_1,D(v)\}$ also when the guess $S$ omits $v$: printed line 16 copies $D$ only on $S$, so for $v\in Y\setminus S$ the printed $D_1(v)=d_1$ forgets $D(v)$ and the returned arborescence can violate the bound $D(v)$ that the parameter description requires. The offset of $T_2$ is $k_r+l_{T_1}(v)$ computed on the returned $T_1$, as in line 20. In the grouped version the cost and length budgets are assigned leaf by leaf, as in the published `runPlan`: every leaf but the last receives a guessed (or binary-searched) cost budget and a guessed length budget, and the last leaf receives what remains; intermediate levels of a group do not repeat the size check. The step count is $1$ per call, $n$ per base call, plus every recursive call and binary-search probe, $1$ per guess and $1$ per evaluated candidate. $l_T(w)$ is $0$ for a vertex not reachable from the root; every statement evaluates it only on reachable vertices. No triangle inequality is assumed.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, pp. 10–11 (PDF 11–12), §4.1; p. 12 (PDF 13), Algorithm 3; p. 11 (PDF 12), Lemma 4.2 (compatibility); p. 13 (PDF 14), §4.1.1

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Model

namespace TreeOrient.RecGreedy.Supplement

/-- An instance of submodular tree orienteering with length constraints (§4.1, p. 10):
an STO instance together with edge lengths `len` and a bound `L` on the sum of path lengths. -/
structure LInst (n : ℕ) extends Inst n where
  len : Fin n → Fin n → ℕ
  L : ℕ

/-- One step of a walk along an edge of `T`, accumulating the edge length. -/
def WalkStep {n : ℕ} (len : Fin n → Fin n → ℕ) (T : Edges n) :
    Fin n × ℕ → Fin n × ℕ → Prop :=
  fun p q => (p.1, q.1) ∈ T ∧ q.2 = p.2 + len p.1 q.1

/-- There is a directed `r`–`w` walk in `T` of total length `m`. -/
def HasWalkOfLength {n : ℕ} (len : Fin n → Fin n → ℕ) (T : Edges n) (r w : Fin n)
    (m : ℕ) : Prop :=
  Relation.ReflTransGen (WalkStep len T) (r, 0) (w, m)

open Classical in
/-- `l_T(w)`: the least length of a directed walk from `r` to `w` along edges of `T`.
In an `r`-rooted arborescence this is the length of the unique `r`–`w` path. The value `0`
for a vertex not reachable from `r` is never used by the statements, which only evaluate it
on reachable vertices. -/
noncomputable def lenTo {n : ℕ} (len : Fin n → Fin n → ℕ) (T : Edges n) (r w : Fin n) : ℕ :=
  if h : ∃ m, HasWalkOfLength len T r w m then Nat.find h else 0

/-- `∑_{v ∈ T, v ≠ r} (k_r + l_T(v))`, summed over the non-root vertices of `T`. -/
noncomputable def lenSum {n : ℕ} (len : Fin n → Fin n → ℕ) (kr : ℕ) (r : Fin n)
    (T : Edges n) : ℕ :=
  ∑ w ∈ (verts r T).erase r, (kr + lenTo len T r w)

/-- `T∗` is compatible with `RG-DC(r, k_r, Y, D, B, L, X, i)` (Lemma 4.2, p. 11) for the size
cap `cap = (3/2)^i`: an `r`-rooted arborescence visiting `Y`, with at most `cap` non-root
vertices, cost at most `B`, length sum at most `L`, and respecting the length bounds `D`. -/
def CompatibleDC {n : ℕ} (I : LInst n) (r : Fin n) (kr : ℕ) (Y : Finset (Fin n))
    (D : Fin n → ℕ) (B L : ℕ) (cap : ℝ) (A : Edges n) : Prop :=
  Compatible I.c r Y B cap A ∧ lenSum I.len kr r A ≤ L ∧
    ∀ w ∈ Y.erase r, lenTo I.len A r w ≤ D w

/-- A feasible output of `RG-DC(r, k_r, Y, D, B, L, X, i)`: an edge set in which every vertex
is reachable from `r`, of cost at most `B`, visiting `Y`, that contains an `r`-rooted
arborescence on the same vertices satisfying the length-sum bound and the bounds `D`. -/
def FeasibleDC {n : ℕ} (I : LInst n) (r : Fin n) (kr : ℕ) (Y : Finset (Fin n))
    (D : Fin n → ℕ) (B L : ℕ) (T : Edges n) : Prop :=
  Feasible I.c r Y B T ∧
    ∃ A' : Edges n, A' ⊆ T ∧ IsArbo r A' ∧ verts r A' = verts r T ∧
      lenSum I.len kr r A' ≤ L ∧ ∀ w ∈ Y.erase r, lenTo I.len A' r w ≤ D w

/-- The type of a recursive call `RG-DC(r, k_r, Y, D, B, L, X, ·)` at a fixed depth. -/
abbrev SubCall (n : ℕ) :=
  Fin n → ℕ → Finset (Fin n) → (Fin n → ℕ) → ℕ → ℕ → Finset (Fin n) → Option (Edges n) × ℕ

/-- Solve one leaf subproblem of a guessed structure. A non-final leaf receives its own length
budget `l ∈ [0, Lrem]` and its own cost budget: every `b ∈ [0, Brem]` (`enum`), or, for each
value guess `u ∈ [0, U]`, the least `b` found by binary search whose result has `f_X ≥ u`
(`bsearch U`). The final leaf receives the whole remaining budgets. Each candidate is returned
with the budgets left for later leaves. The step count sums all calls and probes. -/
noncomputable def solveLeaf {n : ℕ} (I : LInst n) (mode : Mode) (sub : SubCall n)
    (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ) (X : Finset (Fin n))
    (Brem Lrem : ℕ) (final : Bool) : List (Edges n × ℕ × ℕ) × ℕ :=
  if final then
    let (o, t) := sub r kr Y D Brem Lrem X
    (o.toList.map (fun T => (T, 0, 0)), t)
  else
    (List.range (Lrem + 1)).foldl (fun (acc, steps) l =>
      match mode with
      | .enum =>
          (List.range (Brem + 1)).foldl (fun (acc', steps') b =>
            let (o, t) := sub r kr Y D b l X
            (acc' ++ o.toList.map (fun T => (T, Brem - b, Lrem - l)), steps' + t))
            (acc, steps)
      | .bsearch U =>
          (List.range (U + 1)).foldl (fun (acc', steps') u =>
            let probe := fun b =>
              let (o, t) := sub r kr Y D b l X
              match o with
              | none => (false, t)
              | some T => (decide ((u : ℝ) ≤ fX I.f X r T), t + 1)
            let (ob, probes) := bsearch probe 0 Brem
            match ob with
            | none => (acc', steps' + probes)
            | some b =>
                let (o, t) := sub r kr Y D b l X
                (acc' ++ o.toList.map (fun T => (T, Brem - b, Lrem - l)),
                  steps' + probes + t))
            (acc, steps)) ([], 0)

/-- Guess every quantity of `j` levels of Algorithm 3 below a subproblem
`(r, k_r, Y, D, X)`: for each level the separator `v`, the responsibilities `S ⊆ Y` and the
length `d₁ ∈ [0, Lrem]` from `r` to `v` (lines 11–18; a guess with `d₁ > D(w)` for some
`w ∈ Y \ (S ∪ {v})` is skipped, since then `D(w) − d₁ < 0`), with `D₁ = D` on `S` and
`D₁(v) = min(d₁, D(v))` whenever `v ∈ Y` (or `d₁` if `v ∉ Y`), and `D₂ = D − d₁`. The left part is solved first;
the right part is rooted at `v` with `k_r + l_{T₁}(v)` computed on the returned left edge set
`T₁` and with `X ∪ V(T₁)` (lines 19–20). Budgets are assigned leaf by leaf (`solveLeaf`). The
result lists every combined candidate with the budgets it leaves. -/
noncomputable def expand {n : ℕ} (I : LInst n) (mode : Mode) (sub : SubCall n) :
    ℕ → Fin n → ℕ → Finset (Fin n) → (Fin n → ℕ) → Finset (Fin n) → ℕ → ℕ → Bool →
      List (Edges n × ℕ × ℕ) × ℕ
  | 0, r, kr, Y, D, X, Brem, Lrem, final => solveLeaf I mode sub r kr Y D X Brem Lrem final
  | j + 1, r, kr, Y, D, X, Brem, Lrem, final =>
      (List.finRange n).foldl (fun (acc, steps) v =>
        Y.powerset.toList.foldl (fun (acc', steps') S =>
          (List.range (Lrem + 1)).foldl (fun (acc'', steps'') d1 => by
            classical
            exact
              if ∃ w ∈ Y \ (S ∪ {v}), D w < d1 then (acc'', steps'' + 1)
              else
                let D1 : Fin n → ℕ := fun w =>
                  if w = v then (if v ∈ Y then min d1 (D v) else d1) else D w
                let D2 : Fin n → ℕ := fun w => D w - d1
                let (left, t1) := expand I mode sub j r kr ((S ∪ {v}) \ {r}) D1 X Brem Lrem false
                let (more, t2) := left.foldl (fun (more, t2) (p : Edges n × ℕ × ℕ) =>
                  let (right, t') := expand I mode sub j v (kr + lenTo I.len p.1 r v)
                    (Y \ (S ∪ {v})) D2 (X ∪ verts r p.1) p.2.1 p.2.2 final
                  (more ++ right.map (fun q => (p.1 ∪ q.1, q.2.1, q.2.2)), t2 + t')) ([], 0)
                (acc'' ++ more, steps'' + 1 + t1 + t2)) (acc', steps')) (acc, steps)) ([], 0)

/-- `RG-DC(r, k_r, Y, D, B, L, X, i)` (Algorithm 3, p. 12 (PDF 13)) with `s` grouped levels
per recursion step (§4.1.1). Line 1 is the size check `|Y| > (3/2)^{s i}`. For `s = 1` the base
level is lines 2–8; for `s ≥ 2` the grouped depth one keeps the best arborescence with at most
`⌊(3/2)^s⌋` edges passing every compatibility check. Deeper levels guess `s` levels of
Algorithm 3 (`expand`) and keep the best union by `f_X`, starting from `∅` exactly when
`Y = ∅`. The second component counts steps: 1 per call, `n` per base call, every sub-call and
probe, 1 per guess and per evaluated candidate. -/
noncomputable def rgdc {n : ℕ} (I : LInst n) (s : ℕ) (mode : Mode) :
    ℕ → Fin n → ℕ → Finset (Fin n) → (Fin n → ℕ) → ℕ → ℕ → Finset (Fin n) →
      Option (Edges n) × ℕ
  | 0, _, _, _, _, _, _, _ => (none, 1)
  | i + 1, r, kr, Y₀, D, B, L, X =>
      let Y := Y₀.erase r
      if capImp s (i + 1) < (Y.card : ℝ) then (none, 1)
      else if i = 0 then
        if s = 1 then
          if Y = ∅ then
            let candidates := (List.finRange n).filterMap fun v =>
              if v = r || B < I.c r v || L < kr + I.len r v then none
              else some ({(r, v)} : Edges n)
            let (o, _) := chooseBest I.f X r (some ∅) candidates
            (o, 1 + n)
          else
            let o := match Y.toList with
              | [v] =>
                  if I.c r v ≤ B ∧ kr + I.len r v ≤ L ∧ I.len r v ≤ D v then
                    some ({(r, v)} : Edges n)
                  else none
              | _ => none
            (o, 1 + n)
        else
          let candidates := edgeCandidates n (Nat.floor (capImp s 1))
          let initial : Option (Edges n) := if Y = ∅ then some ∅ else none
          candidates.foldl (fun (best, steps) T => by
            classical
            exact
              if IsArbo r T ∧ Y ⊆ verts r T ∧ cost I.c T ≤ B ∧ lenSum I.len kr r T ≤ L ∧
                  ∀ w ∈ Y, lenTo I.len T r w ≤ D w then
                ((chooseBest I.f X r best [T]).1, steps + 1)
              else (best, steps + 1)) (initial, 1)
      else
        let initial : Option (Edges n) := if Y = ∅ then some ∅ else none
        let (cands, t) := expand I mode (rgdc I s mode i) s r kr Y D X B L true
        let (best, evals) := chooseBest I.f X r initial (cands.map Prod.fst)
        (best, 1 + t + evals)

/-- The algorithm of Theorem 4.3: Algorithm 3 with budget enumeration, called as
`RG-DC(r∗, 0, ∅, D₀, B, L, ∅, d)` with depth `d = dOf k ≥ log_{3/2} k`. -/
noncomputable def alg43 {n : ℕ} (I : LInst n) (k : ℕ) : Option (Edges n) × ℕ :=
  rgdc I 1 .enum (dOf k) I.root 0 ∅ (fun _ => 0) I.B I.L ∅

/-- The algorithm of Theorem 1.2 (§4.1.1): `s = sOf ε k` grouped levels of Algorithm 3 per
recursion step, binary search on the cost budget with value guesses in `[0, n ^ a]`, depth
`⌈dOf k / s⌉`, called from `(r∗, k_r = 0, Y = ∅)`. -/
noncomputable def stoDCAlg {n : ℕ} (I : LInst n) (a : ℕ) (ε : ℝ) (k : ℕ) :
    Option (Edges n) × ℕ :=
  let s := sOf ε k
  rgdc I s (.bsearch (n ^ a)) (depthOf s (dOf k)) I.root 0 ∅ (fun _ => 0) I.B I.L ∅

end TreeOrient.RecGreedy.Supplement


