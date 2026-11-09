-- Prove2me | Definitions.Def_CBCLowerBound_EveryNorm_Requests
-- name    : CBCLowerBound_EveryNorm_Requests
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:46.281671+00:00
-- url     : https://prove2.me/theorems/20149431-1f06-4289-a00a-b90bc3802eff
-- title:
--   The request distribution $D_r$ with its call structure, randomized MSS algorithms, and the mapped convex instance
-- statement:
--   **Request sequence** (§2.2, pp.6–7). On $G_0$ the requests are $\{s_0\}$, then $\{t_0\}$. On $G_{r+1}$, with $m=m_r$: first $\{s_{r+1}\}$, then the pair $\{u_L,u_R\}$ of ends of the two entrance edges; each branch has a *current vertex*, initially $u_L$ resp. $u_R$. *Advancing branch $a$ through its next copy $H$* (a **call** in $H$) issues the level-$r$ sequence in $H$ with fresh independent randomness; if the opposite branch has a current vertex $z$ (a **waiting vertex**), every request $U$ of the call becomes $U\cup\{z\}$. Afterwards the current vertex of branch $a$ is $t_H$.
--
--   1. *Stage 1.* For $j=1,\dots,m^2$: advance the $j$-th small copy on the left, then the $j$-th small copy on the right.
--   2. *Stage 2.* For each of $m$ rounds, choose a branch independently and uniformly at random and advance it through its next large copy.
--   3. *Stage 3.* Request only the current vertex of the branch that advanced fewer times in Stage 2 (a fixed rule breaks a tie), discard the other branch's current vertex, advance the surviving branch through its remaining large copies (no waiting vertex at this level), and finally request $\{t_{r+1}\}$.
--
--   Within a call in a copy $H$ all waiting vertices $Z$ retained at higher levels stay in every request, so the call begins with $\{s_H\}\cup Z$ and ends with $\{t_H\}\cup Z$; repeated requests at call boundaries are kept, and there is no padding. $D_r$ is the resulting distribution of level-$r$ request sequences $S_1,\dots,S_T$ on $G_r$.
--
--   **Randomized MSS algorithms** (p.4). A randomized online algorithm for the discrete requests, started at $s_r$, holds after each prefix $S_1,\dots,S_t$ a probability distribution $P_t$ on the vertices supported in $S_t$ ($P_0=\delta_{s_r}$), chosen from the prefix alone; consecutive distributions are coupled optimally, so its expected cost is $\sum_t W_1(P_{t-1},P_t)$ for the metric $d_G$. The discrete offline optimum is $\inf\{\sum_t d_G(y_{t-1},y_t): y_0=s_r,\ y_t\in S_t\}$.
--
--   **Decomposition (7)** (p.10). For consecutive requests $S,S'$ and a level-$s$ copy $H$, local requests $U,U'$ form a *local change in $H$* if both requests are issued during the call to $H$ and $S=U\cup Z$, $S'=U'\cup Z$, $(U\cup U')\cap Z=\varnothing$, where $Z$ is the set of waiting vertices retained by the calls of level $>s$ containing $H$.
--
--   **Mapped instance** (eq. (16), p.14). For $p\in[1,\infty]$, each request $S_t$ becomes the body $K_t=\mathrm{conv}\{\Psi(v):v\in S_t\}\subseteq\ell_p^D$.
--
--   **Formalization Note** $D_r$ is a probability mass function on lists of *annotated* requests: each request records the innermost active call (a copy $H$ and its level), the local request $U$ issued by $H$'s own sequence, and the retained waiting vertices labelled by the level of the retaining call; the plain request is $U\cup Z$. Algorithms see only the plain requests. "Call to $H$" is read off the annotation ($H$ contains the innermost call). The tie rule is a Boolean parameter (the branch that survives a tie). The final request of Stage 2 is the last request of its last call, the pair of current vertices; no extra request is inserted. Copy indices are taken modulo $m_r^2+2m_r$, which never changes an index used by the construction. Expectations over $D_r$ are sums $\sum_\sigma D_r(\sigma)\cdot(\cdot)$ in $[0,\infty]$.
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), pp.6–7, §2.2 (request sequence, Stages 1–3, D_r, footnote 1); p.4 (randomized MSS algorithms); p.10, Lemma 5 eq. (7); p.14, §4 eq. (16), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib
import Definitions.Def_CBCLowerBound_EveryNorm_Chasing
import Definitions.Def_CBCLowerBound_EveryNorm_Transport
import Definitions.Def_CBCLowerBound_EveryNorm_Graph

open scoped ENNReal

namespace CBCLowerBound.EveryNorm

/-! # The random request sequence `D_r`, randomized MSS algorithms and the mapped convex
instance (Christianson, STOC 2027 #674, §2.2, pp.6–7; §2, p.4; §4, eq. (16), p.14) -/

/-! ## Annotated requests -/

/-- An **annotated request** of the level-`r` instance on `G_r`. Besides the requested vertex
set it records the call structure that produced it:
* `copy : Copy θ r lvl` is the innermost active call, i.e. the request was issued by the
  level-`lvl` request sequence run in the copy `copy` (itself, not by a sub-call of it);
* `loc` is that local request `U ⊆ copy` (in the vertices of `G_r`);
* `wait` lists the waiting vertices retained by the enclosing higher-level calls, each with the
  level `ℓ` of the copy whose call retains it (the call of the level-`ℓ` copy containing `copy`).
The requested set is `U ∪ Z`, with `Z` the retained waiting vertices. -/
structure AReq (θ : Params) (r : ℕ) where
  /-- The level of the innermost active call. -/
  lvl : ℕ
  /-- The copy in which the innermost active call runs. -/
  copy : Copy θ r lvl
  /-- The local request of that call. -/
  loc : Finset (Vert θ r)
  /-- The retained waiting vertices, labelled by the level of the retaining call. -/
  wait : List (ℕ × Vert θ r)

namespace AReq

variable {θ : Params} {r : ℕ}

/-- The requested vertex set `U ∪ Z`. -/
def set (q : AReq θ r) : Finset (Vert θ r) :=
  q.loc ∪ (q.wait.map Prod.snd).toFinset

/-- The waiting vertices of `q` retained by calls of level `> s`. -/
def waitAbove (q : AReq θ r) (s : ℕ) : Finset (Vert θ r) :=
  ((q.wait.filter fun p => decide (s < p.1)).map Prod.snd).toFinset

/-- A local request issued by the level-`r` sequence of `G_r` itself (no enclosing call). -/
def top (U : Finset (Vert θ r)) : AReq θ r :=
  ⟨r, Copy.self r, U, []⟩

/-- A level-`r` request issued in a call to the `j`-th copy of `G_r` on branch `a` of
`G_{r+1}`, viewed as a level-`(r+1)` request: every vertex is mapped into the copy, and the
waiting vertex `z` (if any) retained by the level-`(r+1)` call is added. -/
def lift (a : Bool) (j : Fin (θ.n r)) (z : Option (Vert θ (r + 1))) (q : AReq θ r) :
    AReq θ (r + 1) where
  lvl := q.lvl
  copy := .inr (a, j, q.copy)
  loc := q.loc.image (embed θ a j)
  wait := (z.map fun z => (r + 1, z)).toList ++ q.wait.map fun p => (p.1, embed θ a j p.2)

end AReq

/-! ## The request distribution -/

/-- Independent sequential concatenation: sample each list in turn, independently, and
concatenate. -/
noncomputable def seqCat {α : Type} : List (PMF (List α)) → PMF (List α)
  | [] => PMF.pure []
  | p :: ps => p.bind fun l => (seqCat ps).map fun l' => l ++ l'

/-- Stage 2 (p.6): `k` remaining rounds, the left branch having advanced `cL` times and the
right branch `cR` times through large copies. Each round chooses a branch uniformly at random,
independently of everything else, and advances it (`adv a cL cR`). Returns the requests and the
final counts. -/
noncomputable def stageTwo {α : Type} (adv : Bool → ℕ → ℕ → PMF (List α)) :
    ℕ → ℕ → ℕ → PMF (List α × ℕ × ℕ)
  | 0, cL, cR => PMF.pure ([], cL, cR)
  | k + 1, cL, cR =>
    (PMF.uniformOfFintype Bool).bind fun a =>
      (adv a cL cR).bind fun l =>
        (stageTwo adv k (if a then cL else cL + 1) (if a then cR + 1 else cR)).map
          fun res => (l ++ res.1, res.2)

/-- The **request distribution `D_r`** of the small-request construction (§2.2, pp.6–7), as a
distribution of annotated request sequences (`tie` is the branch that survives a Stage-3 tie).

* Level `0`: `{s₀}`, then `{t₀}`.
* Level `r+1`, with `m = m_r`: request `{s_{r+1}}`; then the pair `{u_L, u_R}` of entrance-edge
  ends. Calls: "advancing branch `a` through its copy `j`" issues an independent sample of
  the level-`r` sequence in that copy, adding the other branch's current vertex as waiting
  vertex if it has not been removed.
  Stage 1: for `j = 0, …, m² − 1`, advance the left `j`-th small copy (waiting vertex: the
  right current vertex, the source of its `j`-th copy), then the right `j`-th small copy
  (waiting vertex: the left current vertex, the source of its `(j+1)`-th copy).
  Stage 2: `m` rounds, each advancing an independently, uniformly chosen branch through its
  next large copy, retaining the other branch's current vertex.
  Stage 3: request only the current vertex of the branch that advanced fewer times in
  Stage 2 (`tie` on a tie), drop the other branch, advance the surviving branch through its
  remaining large copies with no waiting vertex at this level, and finally request
  `{t_{r+1}}`.
Repeated requests at call boundaries are kept, and there is no padding. -/
noncomputable def reqDist (θ : Params) (tie : Bool) : (r : ℕ) → PMF (List (AReq θ r))
  | 0 => PMF.pure [AReq.top {.src}, AReq.top {.tgt}]
  | r + 1 =>
    let M := θ.m r
    let idx : ℕ → Fin (θ.n r) := fun j => ⟨j % θ.n r, Nat.mod_lt _ (θ.n_pos r)⟩
    let jn : Bool → ℕ → Vert θ (r + 1) := fun a j => .inner (a, idx j, none)
    let call : Bool → ℕ → Option (Vert θ (r + 1)) → PMF (List (AReq θ (r + 1))) :=
      fun a j z => (reqDist θ tie r).map (List.map (AReq.lift a (idx j) z))
    let cnt : Bool → ℕ → ℕ → ℕ := fun a cL cR => if a then cR else cL
    let adv : Bool → ℕ → ℕ → PMF (List (AReq θ (r + 1))) := fun a cL cR =>
      call a (M ^ 2 + cnt a cL cR) (some (jn (!a) (M ^ 2 + cnt (!a) cL cR)))
    let stage1 : List (PMF (List (AReq θ (r + 1)))) :=
      (List.range (M ^ 2)).flatMap fun j =>
        [call false j (some (jn true j)), call true j (some (jn false (j + 1)))]
    let stage3 : ℕ → ℕ → PMF (List (AReq θ (r + 1))) := fun cL cR =>
      let surv : Bool := if cL < cR then false else if cR < cL then true else tie
      let c := cnt surv cL cR
      seqCat ([PMF.pure [AReq.top {jn surv (M ^ 2 + c)}]] ++
        (List.range (2 * M - c)).map (fun i => call surv (M ^ 2 + c + i) none) ++
        [PMF.pure [AReq.top {.tgt}]])
    (seqCat ([PMF.pure [AReq.top {.src}], PMF.pure [AReq.top {jn false 0, jn true 0}]] ++
        stage1)).bind fun l1 =>
      (stageTwo adv M 0 0).bind fun res =>
        (stage3 res.2.1 res.2.2).map fun l3 => l1 ++ res.1 ++ l3

/-- The plain request sequence `S₁, …, S_T` (vertex sets) of an annotated sequence. -/
def requests {θ : Params} {r : ℕ} (σ : List (AReq θ r)) : List (Finset (Vert θ r)) :=
  σ.map AReq.set

/-! ## Randomized algorithms for metrical service systems on `G_r` (p.4) -/

/-- A **randomized online algorithm for the discrete requests on `G_r`** started at `s_r`, in the
distributional form of p.4: after each prefix of requests it holds a probability distribution
over the vertices, supported in the newest request, and it pays the optimal transportation
distance between consecutive distributions. The decision depends only on the revealed plain
request sets. -/
structure MSSAlg (θ : Params) (r : ℕ) where
  /-- The distribution held after a prefix of requests. -/
  law : List (Finset (Vert θ r)) → Vert θ r → ℝ
  /-- It is a probability vector. -/
  prob : ∀ l, IsProbVec (law l)
  /-- The start is the point mass at `s_r`. -/
  init : law [] = fun v => if v = .src then 1 else 0
  /-- After a nonempty request `S`, the distribution is supported in `S`. -/
  supp : ∀ (l : List (Finset (Vert θ r))) (S : Finset (Vert θ r)), S.Nonempty →
    ∀ v ∉ S, law (l ++ [S]) v = 0

/-- The (expected) movement cost `∑_t W₁(P_{t−1}, P_t)` of an MSS algorithm on a request
sequence, with `W₁` for the graph metric `d_G`. -/
noncomputable def MSSAlg.cost {θ : Params} {r : ℕ} (A : MSSAlg θ r)
    (σ : List (Finset (Vert θ r))) : ℝ :=
  ∑ t ∈ Finset.range σ.length,
    W1 (dist θ r) (A.law (σ.take t)) (A.law (σ.take (t + 1)))

/-- The offline optimum of a discrete request sequence on `G_r` from `s_r`: the infimum of
`∑_t d_G(y_{t−1}, y_t)` over `y₀ = s_r`, `y_t ∈ S_t`. -/
noncomputable def mssOpt (θ : Params) (r : ℕ) (σ : List (Finset (Vert θ r))) : ℝ :=
  sInf {c : ℝ | ∃ y : ℕ → Vert θ r, y 0 = .src ∧
    (∀ (t : ℕ) (ht : t < σ.length), y (t + 1) ∈ σ[t]) ∧
    c = ∑ t ∈ Finset.range σ.length, dist θ r (y t) (y (t + 1))}

/-! ## The decomposition (7) of consecutive requests (Lemma 5, p.10) -/

/-- `IsLocalChange q q' H U U'`: the consecutive annotated requests `q, q'` both occur in the
call to the level-`s` copy `H`, and decompose as in eq. (7) into a local change `U, U'` plus the
set `Z` of waiting vertices retained by the higher-level calls (levels `> s`) containing `H`:
`S = U ∪ Z`, `S' = U' ∪ Z`, `(U ∪ U') ∩ Z = ∅`. -/
def IsLocalChange {θ : Params} {r s : ℕ} (q q' : AReq θ r) (H : Copy θ r s)
    (U U' : Finset (Vert θ r)) : Prop :=
  H.Contains q.copy ∧ H.Contains q'.copy ∧
  q.waitAbove s = q'.waitAbove s ∧
  q.set = U ∪ q.waitAbove s ∧ q'.set = U' ∪ q.waitAbove s ∧
  Disjoint (U ∪ U') (q.waitAbove s)

/-! ## The mapped convex body chasing instance (eq. (16), p.14) -/

/-- The convex body chasing instance in `ℓ_p^D`, `D = 2r + 1` (eq. (16)): each discrete request
`S_t` becomes `K_t = conv{Ψ(v) : v ∈ S_t}`. -/
noncomputable def bodies (θ : Params) (r : ℕ) (p : ℝ≥0∞) (σ : List (AReq θ r)) :
    List (Set (PiLp p fun _ : Fin (2 * r + 1) => ℝ)) :=
  σ.map fun q => convexHull ℝ ((fun v => WithLp.toLp p (Psi θ r v)) '' (q.set : Set (Vert θ r)))

end CBCLowerBound.EveryNorm


