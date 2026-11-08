-- Prove2me | Definitions.Def_DecrNbhdCover_MaintainEmulator
-- name    : DecrNbhdCover_MaintainEmulator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:30.774102+00:00
-- url     : https://prove2.me/theorems/c800bbac-32ea-4fb1-ba73-98e1bf273530
-- title:
--   Path-transforming emulators (Definition 3.2) and the MaintainEmulator problem (Definitions 3.20, 3.22)
-- statement:
--   An emulator is **path-transforming** if a deterministic algorithm, given a path $P$ in $H$ with no consecutively repeated regular vertices connecting $v,v'\in V(G)$, computes a $v$-$v'$ path $P'$ in $G$ with $\ell_G(P')\le\ell_H(P)$ and $|E(P')|\ge|E(P)|/2$, in time $\tilde O(|E(P')|)$.
--
--   In the **weak problem** the input has an $n$-vertex graph $G$ with maximum degree at most $\mu\ge1$ and edge deletions, $0<\epsilon<1/400$, integers $0<d<D<D'$ with $D'>D\cdot2^{1/\epsilon^{4c}}$, and a proper $(\epsilon,d,D)$-emulator $H$ for $G$ with dynamic degree bound $\mu'\ge1$. The goal is an $(\epsilon,D,D')$-shelled neighborhood cover $\mathcal N$ and a proper $(\epsilon',D,D')$-emulator $H'=H_{G,\mathcal N}$ with $\epsilon'=\epsilon+\epsilon^2/2$ and dynamic degree bound $\tilde O(\mu n^{O(\epsilon)}\mathrm{poly}(1/\epsilon))$, with short-path queries $(S,v,v')$, $v,v'\in\mathrm{Shell}(S)$, returning a path in $H$ of length at most $\tilde d_S(v)+\tilde d_S(v')+D_S2^{1/\epsilon^c}$ with no consecutively repeated regular vertices.
--
--   In the **strong problem** the input has an $n$-vertex graph with maximum degree at most $\mu\ge1$, positive even integer lengths, edge deletions, $0<\epsilon<1/400$, an integer $0<d\le1024n\log n/\epsilon^2$, and $D>4d\cdot2^{1/\epsilon^{4c}}$. The goal is a well-structured $H$ with dynamic degree bound $\tilde O(\mu n^{O(\epsilon)}\mathrm{poly}(1/\epsilon))$ that is a proper and path-transforming $(\epsilon,d,D)$-emulator for $G$.
--
--   **Formalization Note** The cover is reported by the update types of §7.4, plus additions and deletions in $T(S)$, whose changes the paper does not restrict. $H'$ is the function $H_{G,\mathcal N}$ of the reports, and is not reported again. In the strong problem $H$ is reported by the updates of Definition 3.1, and its transform-path queries go to the same program.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Definition 3.2, p.16 (PDF 20); Definition 3.20, p.23 (PDF 27); Definition 3.22, p.24 (PDF 28); §7.4, p.61 (PDF 65)

import Mathlib
import Definitions.Def_DecrNbhdCover_ShelledCover
import Definitions.Def_DecrNbhdCover_Streams
import Definitions.Def_DecrNbhdCover_Session

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-! # Path-transforming emulators and the MaintainEmulator problem (Definitions 3.2, 3.20, 3.22)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Definition 3.2, p.16; Definition 3.20, p.23; Definition 3.22, p.24; §7.4, p.61.

**Formalization Note.** *Weak problem.* The shelled cover is reported with the update types of §7.4, p.61 (cluster insertion and deletion; vertex deletion from `S` or from `Shell(S)`; increase of `d̃_S(v)`) plus additions and
deletions in `T(S)`, whose changes the paper does not restrict: `0, id, Dp, Dq, |S|, S, |T|, T, |Shell|, (v, p, q)…`; `1, id`; `2, id, v` (delete from `S`); `3, id, v`; `4, id, v` (add to, delete from `T`); `5, id, v` (delete from
`Shell`); `6, id, v, p, q` (raise `d̃`). An id is never reused, and `D_S` is fixed at creation. `D_S` and `d̃` are rationals. The emulator `H′` is the function `hGN` of `G` and the reported cover, so it is not reported again: every update of `H′` is a function of an update of `G` or
of the cover, and `H′ = H_{G,N}` holds by construction. Its being a dynamic well-structured graph is a stated clause. *Strong problem.* `H` is reported by the updates of Definition 3.1 in the words of the input format; the initial
`H` is what the initialization window reports. *Path-transforming*: "there is a deterministic algorithm" reads as a program `Q` with constant `C`, fed the updates and the queries `1, v, v′, k, e₁, …, e_k`; in the strong problem, the program that maintains `H` answers them. The
bound is `|E(P′)| ≥ |E(P)|/2`, written `|E(P)| ≤ 2|E(P′)|`. -/

/-- `es'` answers the transform-path query for `(v, es, v')`: a `v`-`v′` path in `G` with `ℓG(P′) ≤ ℓH(P)` and `|E(P′)| ≥ |E(P)|/2`. -/
def TransformOk (G : Graph ℕ ℕ) (H : WSGraph ℕ ℕ ℕ) (v : ℕ) (es : List ℕ) (v' : ℕ) (es' : List ℕ) : Prop :=
  G.WalkFromTo v es' v' ∧ G.walkLen es' ≤ H.walkLen es ∧ es.length ≤ 2 * es'.length

/-- An operation on `G` and `H` for a transforming program: a step of updates, or a transform-path query. -/
inductive TransformOp where
  | batch (gs : List GUpdate) (hs : List HUpdate)
  | query (v v' : ℕ) (es : List ℕ)

namespace TransformOp

/-- The words of an operation. -/
def words : TransformOp → List ℕ
  | .batch gs hs => 0 :: batchWords gs hs
  | .query v v' es => 1 :: v :: v' :: es.length :: es

/-- The updates of `G`. -/
def gPart : TransformOp → List GUpdate
  | .batch gs _ => gs
  | .query _ _ _ => []

/-- The updates of `H`. -/
def hPart : TransformOp → List HUpdate
  | .batch _ hs => hs
  | .query _ _ _ => []

/-- Whether an operation is a query. -/
def isQ : TransformOp → Bool
  | .batch _ _ => false
  | .query _ _ _ => true

end TransformOp

/-- The protocol of a transforming program: its update windows output nothing. -/
def transformProtocol : Protocol TransformOp Empty Unit where
  opWords := TransformOp.words
  isQuery := TransformOp.isQ
  enc := fun r => nomatch r
  step := fun _ r => nomatch r
  st₀ := ()

/-- The number of update steps among the first `t` operations. -/
def stepsBefore (σ : List TransformOp) (t : ℕ) : ℕ :=
  ((σ.take t).filter (fun o => !o.isQ)).length

/-- A fixed history of `G` and `H`: the initial graphs and the steps of updates. -/
structure EmuHistory where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)
  h₀ : List (List (ℕ × ℕ))
  steps : List (List GUpdate × List HUpdate)

namespace EmuHistory

variable (A : EmuHistory)

/-- The input words of the initial graphs. -/
def words : List ℕ :=
  A.n :: edgeWords A.edges ++ hInitWords A.h₀

/-- `G` after the first `τ` steps. -/
def Gτ (τ : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges A.n A.edges) (A.steps.map Prod.fst) τ

/-- `H` after the first `τ` steps. -/
noncomputable def Hτ (τ : ℕ) : HState :=
  hAt (hInit A.n A.h₀) (A.steps.map Prod.snd) τ

/-- The history is valid: the initial graphs are valid and every update is valid when it arrives. -/
structure Ok : Prop where
  edges_ok : EdgesOk A.n A.edges
  h_ok : hInitOk A.n A.h₀
  steps : ∀ (τ : ℕ) (p : List GUpdate × List HUpdate), A.steps[τ]? = some p →
    gsOk (A.Gτ τ) p.1 ∧ hsOk (A.Hτ τ) p.2

/-- The operations follow the history: their update steps are a prefix of it. -/
def Follows (σ : List TransformOp) : Prop :=
  (σ.filterMap (fun o => match o with
    | .batch gs hs => some (gs, hs)
    | .query _ _ _ => none)) <+: A.steps

end EmuHistory

/-- `Q` with constant `C` is a deterministic algorithm that supports transform-path queries for this history (Definition 3.2): on every word size that holds the inputs, every query is answered in time
`C·polylog·(|E(P′)| + 1)`. -/
def IsPathTransformingBy (Q : Program) (C c₀ : ℕ) (A : EmuHistory) : Prop :=
  NoRand Q ∧ ∀ (W : ℕ) (σ : List TransformOp), A.Follows σ →
    c₀ * Nat.clog 2 (2 + transformProtocol.inputMax A.words σ) ≤ W →
    RunsThrough W Q (transformProtocol.blocks A.words σ) ∧
    ∀ (t v v' : ℕ) (es : List ℕ), σ[t]? = some (.query v v' es) →
      v ∈ (A.Gτ (stepsBefore σ t)).V → v' ∈ (A.Gτ (stepsBefore σ t)).V →
      (A.Hτ (stepsBefore σ t)).g.NoRepeatPath v es v' →
      ∃ es', transformProtocol.answer W Q A.words σ t = some es' ∧
        TransformOk (A.Gτ (stepsBefore σ t)) (A.Hτ (stepsBefore σ t)).g v es v' es' ∧
        (transformProtocol.opTime W Q A.words σ t : ℝ) ≤
          polylog C A.n A.edges.length * ((es'.length : ℝ) + 1)

/-- `H` is a proper path-transforming `(ϵ, d, D)`-emulator for `G` along the history, with transforming program `Q`. -/
def IsProperPT (Q : Program) (C c₀ : ℕ) (A : EmuHistory) (eps : ℝ) (d : ℕ) (D : ℝ) : Prop :=
  A.Ok ∧ (∀ τ, IsProper (A.Gτ τ) (A.Hτ τ).g eps d D) ∧ IsPathTransformingBy Q C c₀ A

/-! ## Definition 3.22: the strong problem -/

/-- An operation of the strong problem: an edge deletion from `G`, or a transform-path query. -/
inductive StrongEmuOp where
  | del (e : ℕ)
  | query (v v' : ℕ) (es : List ℕ)

namespace StrongEmuOp

/-- The words of an operation. -/
def words : StrongEmuOp → List ℕ
  | .del e => [0, e]
  | .query v v' es => 1 :: v :: v' :: es.length :: es

/-- The updates of `G`. -/
def gPart : StrongEmuOp → List GUpdate
  | .del e => [.delE e]
  | .query _ _ _ => []

/-- Whether an operation is a query. -/
def isQ : StrongEmuOp → Bool
  | .del _ => false
  | .query _ _ _ => true

end StrongEmuOp

/-- The protocol of the strong problem, for `n` regular vertices. The reports are the updates of the maintained well-structured graph. -/
noncomputable def strongEmuProtocol (n : ℕ) : Protocol StrongEmuOp HUpdate HState where
  opWords := StrongEmuOp.words
  isQuery := StrongEmuOp.isQ
  enc := HUpdate.words
  step := fun s u => by
    classical
    exact if u.Ok s then some (u.apply s) else none
  st₀ := HState.empty n

/-- The input of the strong MaintainEmulator problem. -/
structure StrongEmuInput where
  n : ℕ
  mu : ℕ
  edges : List (ℕ × ℕ × ℕ)
  eps : ℚ
  d : ℕ
  D : ℚ

namespace StrongEmuInput

variable (I : StrongEmuInput)

/-- The conditions of Definition 3.22, for the constant `c`. -/
structure Ok (c : ℕ) : Prop where
  n_pos : 1 ≤ I.n
  mu_pos : 1 ≤ I.mu
  edges_ok : EdgesOk I.n I.edges
  even : ∀ t ∈ I.edges, Even t.2.2
  deg : (ofEdges I.n I.edges).DegLe I.mu
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1 / 400
  d_pos : 0 < I.d
  d_le : (I.d : ℝ) ≤ 1024 * (I.n : ℝ) * Real.logb 2 (I.n : ℝ) / (I.eps : ℝ) ^ 2
  D_gt : 4 * (I.d : ℝ) * (2 : ℝ) ^ (1 / (I.eps : ℝ) ^ (4 * c)) < (I.D : ℝ)

/-- The initialization words. -/
def words : List ℕ :=
  [I.n, I.mu, I.d] ++ edgeWords I.edges ++ ratWords I.eps ++ ratWords I.D

/-- `G` after the first `t` operations. -/
def Gt (σ : List StrongEmuOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map StrongEmuOp.gPart) t

/-- Valid operations: a present edge is deleted; a query is on a path, in the graph `H` reported so far, with no consecutively repeated regular vertices, connecting two vertices of `G`. -/
def Valid (W : ℕ) (P : Program) (σ : List StrongEmuOp) : Prop :=
  ∀ (t : ℕ) (o : StrongEmuOp), σ[t]? = some o →
    match o with
    | .del e => e ∈ (I.Gt σ t).E
    | .query v v' es => ∃ s, (strongEmuProtocol I.n).state W P I.words σ t = some s ∧
        v ∈ (I.Gt σ t).V ∧ v' ∈ (I.Gt σ t).V ∧ s.g.NoRepeatPath v es v'

end StrongEmuInput

/-- The clauses of the strong problem with the time bound of Theorem 3.23: the maintained `H` is a proper path-transforming `(ϵ, d, D)`-emulator with dynamic degree bound `Õ(μ·n^{O(ϵ)}·poly(1/ϵ))`. -/
structure StrongEmuHolds (C W : ℕ) (P : Program) (I : StrongEmuInput) (σ : List StrongEmuOp) : Prop where
  runs : RunsThrough W P ((strongEmuProtocol I.n).blocks I.words σ)
  /-- At every time the log parses and `H` is a proper emulator for the current `G`. -/
  log : ∀ t ≤ σ.length, ∃ s, (strongEmuProtocol I.n).state W P I.words σ t = some s ∧
    IsProper (I.Gt σ t) s.g (I.eps : ℝ) I.d (I.D : ℝ) ∧
    ∀ v, (({f | f < s.nextE ∧ s.g.reg f = v}.ncard : ℕ) : ℝ) ≤
      polylog C I.n I.edges.length * ((I.mu : ℝ) * (I.n : ℝ) ^ ((C : ℝ) * (I.eps : ℝ)) * (1 / (I.eps : ℝ)) ^ C)
  /-- Transform-path queries. -/
  query : ∀ (t v v' : ℕ) (es : List ℕ) (s : HState), σ[t]? = some (.query v v' es) →
    (strongEmuProtocol I.n).state W P I.words σ t = some s →
    ∃ es', (strongEmuProtocol I.n).answer W P I.words σ t = some es' ∧
      TransformOk (I.Gt σ t) s.g v es v' es' ∧
      ((strongEmuProtocol I.n).opTime W P I.words σ t : ℝ) ≤
        polylog C I.n I.edges.length * ((es'.length : ℝ) + 1)
  /-- The total update time. -/
  time : ((strongEmuProtocol I.n).updateTime W P I.words σ : ℝ) ≤
    (C : ℝ) * (I.n : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ)) * (I.mu : ℝ) ^ C * expEps C (I.eps : ℝ)

/-! ## Definition 3.20: the weak problem -/

/-- A report on the shelled neighborhood cover. -/
inductive CoverReport where
  | new (id Dp Dq : ℕ) (S T : List ℕ) (shell : List (ℕ × ℕ × ℕ))
  | delCluster (id : ℕ)
  | delS (id v : ℕ)
  | addT (id v : ℕ)
  | delT (id v : ℕ)
  | delShell (id v : ℕ)
  | raise (id v p q : ℕ)

/-- The words of a report. -/
def CoverReport.words : CoverReport → List ℕ
  | .new id Dp Dq S T shell =>
      [0, id, Dp, Dq] ++ S.length :: S ++ T.length :: T ++
        shell.length :: shell.flatMap (fun t => [t.1, t.2.1, t.2.2])
  | .delCluster id => [1, id]
  | .delS id v => [2, id, v]
  | .addT id v => [3, id, v]
  | .delT id v => [4, id, v]
  | .delShell id v => [5, id, v]
  | .raise id v p q => [6, id, v, p, q]

/-- The cover as reported so far. `used` is the set of ids ever used. -/
structure CoverState where
  used : Finset ℕ
  live : Finset ℕ
  S : ℕ → Finset ℕ
  T : ℕ → Finset ℕ
  DS : ℕ → ℚ
  shell : ℕ → ℕ → Option ℚ

namespace CoverState

/-- The empty cover. -/
def empty : CoverState := ⟨∅, ∅, fun _ => ∅, fun _ => ∅, fun _ => 0, fun _ _ => none⟩

/-- The effect of a report; `none` on an illegal one: a reused id, a change to a cluster not in the collection, a deletion of a non-member, a zero denominator, or a decrease of `d̃`. -/
def step (s : CoverState) : CoverReport → Option CoverState
  | .new id Dp Dq S T sh =>
    if id ∉ s.used ∧ Dq ≠ 0 ∧ ∀ t ∈ sh, t.2.2 ≠ 0 then
      some { s with
        used := insert id s.used
        live := insert id s.live
        S := Function.update s.S id S.toFinset
        T := Function.update s.T id T.toFinset
        DS := Function.update s.DS id ((Dp : ℚ) / (Dq : ℚ))
        shell := Function.update s.shell id
          (fun v => (sh.find? (fun t => t.1 = v)).map (fun t => (t.2.1 : ℚ) / (t.2.2 : ℚ))) }
    else none
  | .delCluster id =>
    if id ∈ s.live then some { s with live := s.live.erase id } else none
  | .delS id v =>
    if id ∈ s.live ∧ v ∈ s.S id then
      some { s with S := Function.update s.S id ((s.S id).erase v) } else none
  | .addT id v =>
    if id ∈ s.live then some { s with T := Function.update s.T id (insert v (s.T id)) } else none
  | .delT id v =>
    if id ∈ s.live ∧ v ∈ s.T id then
      some { s with T := Function.update s.T id ((s.T id).erase v) } else none
  | .delShell id v =>
    if id ∈ s.live ∧ (s.shell id v).isSome then
      some { s with shell := Function.update s.shell id (Function.update (s.shell id) v none) } else none
  | .raise id v p q =>
    match s.shell id v with
    | some x =>
      if id ∈ s.live ∧ q ≠ 0 ∧ x ≤ (p : ℚ) / (q : ℚ) then
        some { s with
          shell := Function.update s.shell id (Function.update (s.shell id) v (some ((p : ℚ) / (q : ℚ)))) }
      else none
    | none => none

/-- The reported state as the data `N` of Definition 3.3. -/
def toCover (s : CoverState) : ShelledCover ℕ ℕ where
  clusters := {id | id ∈ s.live}
  S := fun id => {v | v ∈ s.S id}
  DS := fun id => ((s.DS id : ℚ) : ℝ)
  T := fun id => {v | v ∈ s.T id}
  Shell := fun id => {v | (s.shell id v).isSome}
  dt := fun id v => (((s.shell id v).getD 0 : ℚ) : ℝ)

end CoverState

/-- An operation of the weak MaintainEmulator problem: a step of updates to `G` and `H`, or a short-path query. -/
inductive WeakEmuOp where
  | batch (gs : List GUpdate) (hs : List HUpdate)
  | query (id v v' : ℕ)

namespace WeakEmuOp

/-- The words of an operation. -/
def words : WeakEmuOp → List ℕ
  | .batch gs hs => 0 :: batchWords gs hs
  | .query id v v' => [1, id, v, v']

/-- The updates of `G`. -/
def gPart : WeakEmuOp → List GUpdate
  | .batch gs _ => gs
  | .query _ _ _ => []

/-- The updates of `H`. -/
def hPart : WeakEmuOp → List HUpdate
  | .batch _ hs => hs
  | .query _ _ _ => []

/-- Whether an operation is a query. -/
def isQ : WeakEmuOp → Bool
  | .batch _ _ => false
  | .query _ _ _ => true

end WeakEmuOp

/-- The protocol of the weak problem. -/
def weakEmuProtocol : Protocol WeakEmuOp CoverReport CoverState where
  opWords := WeakEmuOp.words
  isQuery := WeakEmuOp.isQ
  enc := CoverReport.words
  step := CoverState.step
  st₀ := CoverState.empty

/-- The input of the weak MaintainEmulator problem. -/
structure WeakEmuInput where
  n : ℕ
  mu : ℕ
  mu' : ℕ
  edges : List (ℕ × ℕ × ℕ)
  h₀ : List (List (ℕ × ℕ))
  eps : ℚ
  d : ℕ
  D : ℕ
  D' : ℕ

namespace WeakEmuInput

variable (I : WeakEmuInput)

/-- The conditions of Definition 3.20 that do not concern the update stream, for the constant `c`. -/
structure Ok (c : ℕ) : Prop where
  n_pos : 1 ≤ I.n
  mu_pos : 1 ≤ I.mu
  mu'_pos : 1 ≤ I.mu'
  edges_ok : EdgesOk I.n I.edges
  deg : (ofEdges I.n I.edges).DegLe I.mu
  h_ok : hInitOk I.n I.h₀
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1 / 400
  d_pos : 0 < I.d
  d_lt : I.d < I.D
  D_lt : I.D < I.D'
  D'_gt : (I.D : ℝ) * (2 : ℝ) ^ (1 / (I.eps : ℝ) ^ (4 * c)) < (I.D' : ℝ)

/-- The initialization words. -/
def words : List ℕ :=
  [I.n, I.mu, I.mu', I.d, I.D, I.D'] ++ edgeWords I.edges ++ hInitWords I.h₀ ++ ratWords I.eps

/-- `G` after the first `t` operations. -/
def Gt (σ : List WeakEmuOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map WeakEmuOp.gPart) t

/-- `H` after the first `t` operations. -/
noncomputable def Ht (σ : List WeakEmuOp) (t : ℕ) : HState :=
  hAt (hInit I.n I.h₀) (σ.map WeakEmuOp.hPart) t

/-- The promise on the input stream: each step is nonempty, has at most one update of `G`, which is an edge deletion, all updates are valid, and `H` is a proper `(ϵ, d, D)`-emulator for `G` at all times, with dynamic degree bound `μ′`. -/
structure Promise (σ : List WeakEmuOp) : Prop where
  steps : ∀ (t : ℕ) (gs : List GUpdate) (hs : List HUpdate), σ[t]? = some (.batch gs hs) →
    gs.length ≤ 1 ∧ (gs ≠ [] ∨ hs ≠ []) ∧ (∀ u ∈ gs, ∃ e, u = .delE e) ∧
      gsOk (I.Gt σ t) gs ∧ hsOk (I.Ht σ t) hs
  proper : ∀ t ≤ σ.length, IsProper (I.Gt σ t) (I.Ht σ t).g (I.eps : ℝ) I.d (I.D : ℝ)
  deg : (I.Ht σ σ.length).EverDegLe I.mu'

/-- A query names a current cluster with both vertices in its shell. -/
def QueriesOk (W : ℕ) (P : Program) (σ : List WeakEmuOp) : Prop :=
  ∀ (t id v v' : ℕ), σ[t]? = some (.query id v v') →
    ∃ s, weakEmuProtocol.state W P I.words σ t = some s ∧ id ∈ s.live ∧
      (s.shell id v).isSome ∧ (s.shell id v').isSome

end WeakEmuInput

/-- The cover after the first `t` operations (the state at the last time it parses; used only where it parses). -/
noncomputable def WeakEmuInput.coverAt (I : WeakEmuInput) (W : ℕ) (P : Program) (σ : List WeakEmuOp) (t : ℕ) : ShelledCover ℕ ℕ :=
  ((weakEmuProtocol.state W P I.words σ t).getD CoverState.empty).toCover

/-- `H′` after the first `t` operations: `H′ = H_{G,N}`, with the rounding parameter `D` of the `(ϵ, D, D′)`-shelled neighborhood cover. It stays constant after the last operation. -/
noncomputable def WeakEmuInput.hPrime (I : WeakEmuInput) (c W : ℕ) (P : Program) (σ : List WeakEmuOp) (t : ℕ) :
    WSGraph ℕ ℕ (HEdge ℕ ℕ ℕ) :=
  hGN (I.Gt σ (min t σ.length)) (I.coverAt W P σ (min t σ.length)) (I.eps : ℝ) I.D c

/-- The clauses of the weak problem with the time bound of Theorem 3.21. -/
structure WeakEmuHolds (c C W : ℕ) (P : Program) (I : WeakEmuInput) (σ : List WeakEmuOp) : Prop where
  runs : RunsThrough W P (weakEmuProtocol.blocks I.words σ)
  /-- At every time the log parses, and `N` is an `(ϵ, D, D′)`-shelled neighborhood cover for `G`. -/
  log : ∀ t ≤ σ.length, ∃ s, weakEmuProtocol.state W P I.words σ t = some s ∧
    IsShelledCover (I.Gt σ t) s.toCover (I.eps : ℝ) I.D I.D' c
  /-- `H′ = H_{G,N}` is a dynamic well-structured graph. -/
  dyn : IsDynWS (I.hPrime c W P σ)
  /-- `H′` is a proper `(ϵ′, D, D′)`-emulator for `G`, with `ϵ′ = ϵ + ϵ²/2`. -/
  proper : ∀ t ≤ σ.length, IsProper (I.Gt σ t) (I.hPrime c W P σ t)
    ((I.eps : ℝ) + (I.eps : ℝ) ^ 2 / 2) I.D (I.D' : ℝ)
  /-- The dynamic degree bound `Õ(μ·n^{O(ϵ)}·poly(1/ϵ))` of `H′`. -/
  deg : DynDegLe (I.hPrime c W P σ)
    (polylog C I.n I.edges.length * ((I.mu : ℝ) * (I.n : ℝ) ^ ((C : ℝ) * (I.eps : ℝ)) * (1 / (I.eps : ℝ)) ^ C))
  /-- Short-path queries: a `v`-`v′` path in `H` of length at most `d̃_S(v) + d̃_S(v′) + D_S·2^{1/ϵ^c}`, with no consecutively repeated regular vertices. -/
  query : ∀ (t id v v' : ℕ) (s : CoverState) (x x' : ℚ), σ[t]? = some (.query id v v') →
    weakEmuProtocol.state W P I.words σ t = some s → s.shell id v = some x → s.shell id v' = some x' →
    ∃ es, weakEmuProtocol.answer W P I.words σ t = some es ∧
      (I.Ht σ t).g.NoRepeatPath v es v' ∧
      ((I.Ht σ t).g.walkLen es : ℝ) ≤
        (x : ℝ) + (x' : ℝ) + ((s.DS id : ℚ) : ℝ) * (2 : ℝ) ^ (1 / (I.eps : ℝ) ^ c) ∧
      (weakEmuProtocol.opTime W P I.words σ t : ℝ) ≤ polylog C I.n I.edges.length * ((es.length : ℝ) + 1)
  /-- The total update time. -/
  time : (weakEmuProtocol.updateTime W P I.words σ : ℝ) ≤
    (C : ℝ) * (I.n : ℝ) ^ (1 + (C : ℝ) * Real.sqrt (I.eps : ℝ)) *
      ((I.D : ℝ) * (I.mu : ℝ) * (I.mu' : ℝ) / (I.d : ℝ)) ^ C * expEps C (I.eps : ℝ)

end DecrNbhdCover


