-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_Ball
-- name    : DecrNbhdCover_Supplement_Ball
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:26:20.138819+00:00
-- url     : https://prove2.me/theorems/7409bbdf-773c-48c2-be05-348fc6f8a657
-- title:
--   The strong ApproxBall problem (Definition 3.14) and the interface of ApproxBall in decremental graphs (Theorem 3.26)
-- statement:
--   **Strong ApproxBall (Definition 3.14).** The input is a decremental graph $G$ (edge and vertex deletions) that initially has $n$ vertices and maximum degree at most $\mu$, a decremental set $S\subseteq V(G)$, a rational $0<\epsilon<1/400$, and an integer $D$ with
--   $$2^{1/\epsilon^{4c}}<D\le2^{1/\epsilon^{16c}}\cdot n\log_2 n,$$
--   where $c$ is a parameter of the condition. The algorithm maintains a set $S'\subseteq V(G)$ and a value $\tilde d(v)$ for each $v\in S'$ such that, at all times, $B_G(S,10D/\epsilon^2)\subseteq S'$, $0\le\tilde d(v)\le256D/\epsilon^2$ and $\tilde d(v)\le(1+\epsilon)\,\mathrm{dist}_G(S,v)+\epsilon D$. The set $S'$ is decremental, $\tilde d(v)$ never decreases while $v\in S'$, and every change is reported. A query $v\in S'$ returns a path in $G$ from $v$ to a vertex of $S$ of length at most $\tilde d(v)$, in $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps. The item also records the time bound $C\,n^{1+C\epsilon}\max(1,\mu)^C\,2^{C/\epsilon^C}$ of Theorem 3.25.
--
--   **Theorem 3.26's interface.** The input is an $n$-vertex, $m$-edge graph $G$ under edge deletions, a set $S\subseteq V(G)$ under vertex deletions, and rationals $0<\epsilon<1$, $D>0$. With a constant $C$: at all times $B_G(S,D/\epsilon^2)\subseteq S'\subseteq V(G)$, and for $v\in S'$, $d(v)\le C\,D/\epsilon^2$ and
--   $$\mathrm{dist}_G(v,S)\le d(v)\le(1+\epsilon)\,\mathrm{dist}_G(v,S)+\epsilon D.$$
--   $S'$ is decremental, $d(v)$ never decreases while $v\in S'$, every change is reported, queries are as above, and the total update time is at most $C\left(n+m^{1+C\epsilon}2^{C/\epsilon^C}\right)$.
--
--   These two problems differ from the published weak ApproxBall problem: no emulator is given, and paths are in $G$.
--
--   **Formalization Note** The strong problem has no lower bound $\mathrm{dist}_G(S,v)\le\tilde d(v)$, as printed. Reports reuse the published format of the weak problem. A vertex deleted from $G$ also leaves $S$. Paths are walks given by edge numbers.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Definition 3.14, p.21 (PDF 25); Theorems 3.25, 3.26, pp.27–28 (PDF 31–32)

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Common
import Definitions.Def_DecrNbhdCover_ApproxBall

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # The strong ApproxBall problem (Definition 3.14) and ApproxBall in decremental graphs (Theorem 3.26)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Definition 3.14, p.21 (PDF 25); Theorems 3.25 and 3.26, pp.27–28
(PDF 31–32).

**Formalization Note.** The reports are those of the published weak problem (`BallReport`): `0, v, p, q` sets the estimate of `v` to
`p/q` (`v` joins `S′` if it was not in it) and `1, v` removes `v` from `S′`; that `S′` is decremental and that an estimate does not
decrease while its vertex stays in `S′` are stated clauses, so every change is reported and no other change is allowed. Paths are
walks in `G`, given by edge ids; a query `v` is answered with `k, e₁, …, e_k`. *Strong problem.* Operations: `0, e` (delete edge `e`),
`1, v` (delete vertex `v` with its edges; `v` also leaves `S`, which keeps `S ⊆ V(G)`), `2, v` (delete `v` from `S`), `3, v` (query).
Input words: `n, μ, D`, the edge list, `|S|, S`, and `ϵ` as a rational; `D` is an integer as Definition 3.14 requires. *Theorem 3.26.*
Operations: `0, e` (delete edge `e`), `2, v` (delete `v` from `S`), `3, v` (query); input words: `n`, the edge list, `|S|, S`, `ϵ` and `D`
as rationals. -/

/-! ## The strong ApproxBall problem -/

/-- An operation of the strong problem. -/
inductive SBallOp where
  | delE (e : ℕ)
  | delV (v : ℕ)
  | delS (v : ℕ)
  | query (v : ℕ)

namespace SBallOp

/-- The words of an operation. -/
def words : SBallOp → List ℕ
  | .delE e => [0, e]
  | .delV v => [1, v]
  | .delS v => [2, v]
  | .query v => [3, v]

/-- The updates of `G`. -/
def gPart : SBallOp → List GUpdate
  | .delE e => [.delE e]
  | .delV v => [.delV v]
  | _ => []

/-- The vertices leaving `S`: a vertex deleted from `G` leaves `S` too. -/
def sPart : SBallOp → List ℕ
  | .delV v => [v]
  | .delS v => [v]
  | _ => []

/-- Whether an operation is a query. -/
def isQ : SBallOp → Bool
  | .query _ => true
  | _ => false

end SBallOp

/-- The protocol of the strong problem. -/
def sballProtocol : Protocol SBallOp BallReport BallState where
  opWords := SBallOp.words
  isQuery := SBallOp.isQ
  enc := BallReport.words
  step := ballStep
  st₀ := fun _ => none

/-- The input of the strong problem. -/
structure SBallInput where
  n : ℕ
  mu : ℕ
  edges : List (ℕ × ℕ × ℕ)
  S₀ : List ℕ
  eps : ℚ
  D : ℕ

namespace SBallInput

variable (I : SBallInput)

/-- The conditions of Definition 3.14 (strong problem) for the constant `c`: `G` has `n ≥ 1` vertices and maximum degree at most
`μ`, `S ⊆ V(G)`, `0 < ϵ < 1/400`, and `2^{1/ϵ^{4c}} < D ≤ 2^{1/ϵ^{16c}}·n log n`. -/
structure Ok (c : ℕ) : Prop where
  n_pos : 1 ≤ I.n
  edges_ok : EdgesOk I.n I.edges
  deg : (ofEdges I.n I.edges).DegLe I.mu
  S_sub : ∀ v ∈ I.S₀, v < I.n
  S_nodup : I.S₀.Nodup
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1 / 400
  D_gt : (2 : ℝ) ^ (1 / (I.eps : ℝ) ^ (4 * c)) < (I.D : ℝ)
  D_le : (I.D : ℝ) ≤ (2 : ℝ) ^ (1 / (I.eps : ℝ) ^ (16 * c)) * ((I.n : ℝ) * Real.logb 2 (I.n : ℝ))

/-- The initialization words. -/
def words : List ℕ :=
  [I.n, I.mu, I.D] ++ edgeWords I.edges ++ I.S₀.length :: I.S₀ ++ ratWords I.eps

/-- `G` after the first `t` operations. -/
def Gt (σ : List SBallOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map SBallOp.gPart) t

/-- `S` after the first `t` operations. -/
def St (σ : List SBallOp) (t : ℕ) : Set ℕ :=
  {v | v ∈ I.S₀ ∧ ∀ o ∈ σ.take t, v ∉ o.sPart}

/-- Valid operations: what is deleted is present, and a query names a vertex of `S′` as reported so far. -/
def Valid (W : ℕ) (P : Program) (σ : List SBallOp) : Prop :=
  ∀ (t : ℕ) (o : SBallOp), σ[t]? = some o →
    match o with
    | .delE e => e ∈ (I.Gt σ t).E
    | .delV v => v ∈ (I.Gt σ t).V
    | .delS v => v ∈ I.St σ t
    | .query v => ∃ s x, sballProtocol.state W P I.words σ t = some s ∧ s v = some x

end SBallInput

/-- What the strong problem requires at one moment: `S′ ⊆ V(G)`, `BG(S, 10D/ϵ²) ⊆ S′`, and `0 ≤ d̃(v) ≤ 256D/ϵ²` with
`d̃(v) ≤ (1 + ϵ)·distG(S, v) + ϵ·D`. -/
structure SBallAt (G : Graph ℕ ℕ) (S : Set ℕ) (s : BallState) (eps D : ℝ) : Prop where
  sub : ∀ v x, s v = some x → v ∈ G.V
  ball_sub : ∀ v ∈ G.ballSet S (10 * D / eps ^ 2), (s v).isSome
  values : ∀ v x, s v = some x →
    0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 256 * D / eps ^ 2 ∧
      ENNReal.ofReal (x : ℝ) ≤ ENNReal.ofReal (1 + eps) * ((G.distSet S v : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (eps * D)

/-- The clauses of the strong ApproxBall problem with the time bound `C·n^{1+Cϵ}·max(1, μ)^C·2^{C/ϵ^C}` of Theorem 3.25. -/
structure SBallHolds (C W : ℕ) (P : Program) (I : SBallInput) (σ : List SBallOp) : Prop where
  runs : RunsThrough W P (sballProtocol.blocks I.words σ)
  log : ∀ t ≤ σ.length, ∃ s, sballProtocol.state W P I.words σ t = some s ∧
    SBallAt (I.Gt σ t) (I.St σ t) s (I.eps : ℝ) (I.D : ℝ)
  /-- `S′` is decremental and, as long as `v` lies in `S′`, `d̃(v)` does not decrease. -/
  mono : ∀ t < σ.length, ∀ s s', sballProtocol.state W P I.words σ t = some s →
    sballProtocol.state W P I.words σ (t + 1) = some s' →
    ∀ v x', s' v = some x' → ∃ x, s v = some x ∧ x ≤ x'
  /-- Queries return a walk in `G` from `v` to a vertex of `S`, of length at most `d̃(v)`. -/
  query : ∀ (t v : ℕ) (s : BallState) (x : ℚ), σ[t]? = some (.query v) →
    sballProtocol.state W P I.words σ t = some s → s v = some x →
    ∃ es, sballProtocol.answer W P I.words σ t = some es ∧
      (∃ a ∈ I.St σ t, (I.Gt σ t).WalkFromTo v es a) ∧ ((I.Gt σ t).walkLen es : ℝ) ≤ (x : ℝ) ∧
      (sballProtocol.opTime W P I.words σ t : ℝ) ≤ polylog C I.n I.edges.length * ((es.length : ℝ) + 1)
  time : (sballProtocol.updateTime W P I.words σ : ℝ) ≤
    (C : ℝ) * (I.n : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ)) * mx1 I.mu ^ C * expEps C (I.eps : ℝ)

/-! ## ApproxBall in decremental graphs (Theorem 3.26) -/

/-- An operation of Theorem 3.26. -/
inductive DBallOp where
  | delE (e : ℕ)
  | delS (v : ℕ)
  | query (v : ℕ)

namespace DBallOp

/-- The words of an operation. -/
def words : DBallOp → List ℕ
  | .delE e => [0, e]
  | .delS v => [2, v]
  | .query v => [3, v]

/-- The updates of `G`. -/
def gPart : DBallOp → List GUpdate
  | .delE e => [.delE e]
  | _ => []

/-- The vertices leaving `S`. -/
def sPart : DBallOp → List ℕ
  | .delS v => [v]
  | _ => []

/-- Whether an operation is a query. -/
def isQ : DBallOp → Bool
  | .query _ => true
  | _ => false

end DBallOp

/-- The protocol of Theorem 3.26. -/
def dballProtocol : Protocol DBallOp BallReport BallState where
  opWords := DBallOp.words
  isQuery := DBallOp.isQ
  enc := BallReport.words
  step := ballStep
  st₀ := fun _ => none

/-- The input of Theorem 3.26. -/
structure DBallInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)
  S₀ : List ℕ
  eps : ℚ
  D : ℚ

namespace DBallInput

variable (I : DBallInput)

/-- The number of edges. -/
def m : ℕ := I.edges.length

/-- The conditions of Theorem 3.26: `n ≥ 1`, `S ⊆ V(G)`, `0 < ϵ < 1`, `D > 0`. -/
structure Ok : Prop where
  n_pos : 1 ≤ I.n
  edges_ok : EdgesOk I.n I.edges
  S_sub : ∀ v ∈ I.S₀, v < I.n
  S_nodup : I.S₀.Nodup
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1
  D_pos : 0 < I.D

/-- The initialization words. -/
def words : List ℕ :=
  I.n :: edgeWords I.edges ++ I.S₀.length :: I.S₀ ++ ratWords I.eps ++ ratWords I.D

/-- `G` after the first `t` operations. -/
def Gt (σ : List DBallOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map DBallOp.gPart) t

/-- `S` after the first `t` operations. -/
def St (σ : List DBallOp) (t : ℕ) : Set ℕ :=
  {v | v ∈ I.S₀ ∧ ∀ o ∈ σ.take t, v ∉ o.sPart}

/-- Valid operations: what is deleted is present, and a query names a vertex of `S′` as reported so far. -/
def Valid (W : ℕ) (P : Program) (σ : List DBallOp) : Prop :=
  ∀ (t : ℕ) (o : DBallOp), σ[t]? = some o →
    match o with
    | .delE e => e ∈ (I.Gt σ t).E
    | .delS v => v ∈ I.St σ t
    | .query v => ∃ s x, dballProtocol.state W P I.words σ t = some s ∧ s v = some x

end DBallInput

/-- What Theorem 3.26 requires at one moment, with constant `C`: `S′ ⊆ V(G)`, `BG(S, D/ϵ²) ⊆ S′`, and
`distG(v, S) ≤ d(v) ≤ (1 + ϵ)distG(v, S) + ϵ·D` with `d(v) ≤ C·D/ϵ²`. -/
structure DBallAt (C : ℕ) (G : Graph ℕ ℕ) (S : Set ℕ) (s : BallState) (eps D : ℝ) : Prop where
  sub : ∀ v x, s v = some x → v ∈ G.V
  ball_sub : ∀ v ∈ G.ballSet S (D / eps ^ 2), (s v).isSome
  values : ∀ v x, s v = some x →
    (x : ℝ) ≤ (C : ℝ) * D / eps ^ 2 ∧
      ((G.distSet S v : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (x : ℝ) ∧
      ENNReal.ofReal (x : ℝ) ≤ ENNReal.ofReal (1 + eps) * ((G.distSet S v : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (eps * D)

/-- The clauses of Theorem 3.26 with the constant `C`. -/
structure DBallHolds (C W : ℕ) (P : Program) (I : DBallInput) (σ : List DBallOp) : Prop where
  runs : RunsThrough W P (dballProtocol.blocks I.words σ)
  log : ∀ t ≤ σ.length, ∃ s, dballProtocol.state W P I.words σ t = some s ∧
    DBallAt C (I.Gt σ t) (I.St σ t) s (I.eps : ℝ) (I.D : ℝ)
  /-- `S′` is decremental and, as long as `v` lies in `S′`, `d(v)` does not decrease. -/
  mono : ∀ t < σ.length, ∀ s s', dballProtocol.state W P I.words σ t = some s →
    dballProtocol.state W P I.words σ (t + 1) = some s' →
    ∀ v x', s' v = some x' → ∃ x, s v = some x ∧ x ≤ x'
  /-- Queries return a walk in `G` from `v` to a vertex of `S`, of length at most `d(v)`. -/
  query : ∀ (t v : ℕ) (s : BallState) (x : ℚ), σ[t]? = some (.query v) →
    dballProtocol.state W P I.words σ t = some s → s v = some x →
    ∃ es, dballProtocol.answer W P I.words σ t = some es ∧
      (∃ a ∈ I.St σ t, (I.Gt σ t).WalkFromTo v es a) ∧ ((I.Gt σ t).walkLen es : ℝ) ≤ (x : ℝ) ∧
      (dballProtocol.opTime W P I.words σ t : ℝ) ≤ polylog C I.n I.m * ((es.length : ℝ) + 1)
  /-- The total update time `C·(n + m^{1+Cϵ}·2^{C/ϵ^C})`. -/
  time : (dballProtocol.updateTime W P I.words σ : ℝ) ≤
    (C : ℝ) * ((I.n : ℝ) + (I.m : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ)) * expEps C (I.eps : ℝ))

end DecrNbhdCover.Supplement


