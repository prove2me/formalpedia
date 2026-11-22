-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_SSSP
-- name    : DecrNbhdCover_Supplement_SSSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:30:33.151919+00:00
-- url     : https://prove2.me/theorems/88441911-7915-4b49-9530-165bd004ef03
-- title:
--   The interface of decremental single-source shortest paths (Theorem 10.1)
-- statement:
--   The input is an $n$-vertex, $m$-edge graph $G$ with positive integer lengths under edge deletions, a source $s\in V(G)$, and a rational $0<\epsilon<1$. $L$ is the largest edge length of the input graph.
--
--   The algorithm maintains, for every vertex $v$, a value $d(v)\in[0,\infty]$. With a constant $C$:
--
--   1. At all times, for every vertex $v$,
--   $$\mathrm{dist}_G(v,s)\le d(v)\le(1+\epsilon)\,\mathrm{dist}_G(v,s).$$
--   2. No value $d(v)$ ever decreases, and every change is reported.
--   3. A query $v$ with $d(v)<\infty$ returns a $v$-$s$ path $P$ in $G$ of length at most $d(v)$, in at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps.
--   4. The total update time is at most $C\left(n+m^{1+C\epsilon}\cdot2^{C/\epsilon^C}\cdot\log_2(2+L)\right)$.
--
--   **Formalization Note** Before any report every estimate is $\infty$. A report sets $d(v)$ to a rational or to $\infty$. Clause 1 forces $d(v)=\infty$ exactly when $v$ is disconnected from $s$. Paths are walks given by edge numbers.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 10.1, p.77 (PDF 81)

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Common

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # Decremental single-source shortest paths (Theorem 10.1)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Theorem 10.1, p.77 (PDF 81).

**Formalization Note.** The program reports the estimates: `0, v, p, q` sets `d(v) = p/q`, and `1, v` sets `d(v) = ∞`. Before any report every
estimate is `∞`, so a vertex whose estimate is never reported keeps the value `∞`. That `d(v)` never decreases (with `∞` the largest value)
is a stated clause between consecutive moments, so every change is reported. Operations: `0, e` (delete edge `e`) and `1, v` (query,
answered with `k, e₁, …, e_k`). Input words: `n`, the edge list, the source `s`, and `ϵ` as a rational. `L` is the largest edge length of
the input graph, and `log L` is read as `log₂(2 + L)`. -/

/-- A report: `d(v) = p/q`, or `d(v) = ∞`. -/
inductive SSSPReport where
  | set (v p q : ℕ)
  | inf (v : ℕ)

/-- The words of a report. -/
def SSSPReport.words : SSSPReport → List ℕ
  | .set v p q => [0, v, p, q]
  | .inf v => [1, v]

/-- The estimates: `some x` is the value `x`, `none` is `∞`. -/
abbrev SSSPState := ℕ → Option ℚ

/-- The effect of a report; a zero denominator is illegal. -/
def ssspStep (s : SSSPState) : SSSPReport → Option SSSPState
  | .set v p q => if q = 0 then none else some (Function.update s v (some ((p : ℚ) / (q : ℚ))))
  | .inf v => some (Function.update s v none)

/-- An estimate as an extended nonnegative real. -/
noncomputable def estVal : Option ℚ → ℝ≥0∞
  | some x => ENNReal.ofReal (x : ℝ)
  | none => ⊤

/-- An estimate did not decrease (`none` is `∞`). -/
def NotDecreased : Option ℚ → Option ℚ → Prop
  | _, none => True
  | none, some _ => False
  | some x, some y => x ≤ y

/-- An operation: an edge deletion or a query. -/
inductive SSSPOp where
  | del (e : ℕ)
  | query (v : ℕ)

namespace SSSPOp

/-- The words of an operation. -/
def words : SSSPOp → List ℕ
  | .del e => [0, e]
  | .query v => [1, v]

/-- The updates of `G`. -/
def gPart : SSSPOp → List GUpdate
  | .del e => [.delE e]
  | .query _ => []

/-- Whether an operation is a query. -/
def isQ : SSSPOp → Bool
  | .del _ => false
  | .query _ => true

end SSSPOp

/-- The protocol of Theorem 10.1. -/
def ssspProtocol : Protocol SSSPOp SSSPReport SSSPState where
  opWords := SSSPOp.words
  isQuery := SSSPOp.isQ
  enc := SSSPReport.words
  step := ssspStep
  st₀ := fun _ => none

/-- The input of Theorem 10.1. -/
structure SSSPInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)
  src : ℕ
  eps : ℚ

namespace SSSPInput

variable (I : SSSPInput)

/-- The number of edges. -/
def m : ℕ := I.edges.length

/-- The largest edge length `L`. -/
def L : ℕ := maxWord (I.edges.map (fun t => t.2.2))

/-- The conditions of Theorem 10.1: `s ∈ V(G)` and `0 < ϵ < 1`. -/
structure Ok : Prop where
  edges_ok : EdgesOk I.n I.edges
  src_lt : I.src < I.n
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1

/-- The initialization words. -/
def words : List ℕ :=
  I.n :: edgeWords I.edges ++ I.src :: ratWords I.eps

/-- `G` after the first `t` operations. -/
def Gt (σ : List SSSPOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map SSSPOp.gPart) t

/-- Valid operations: a present edge is deleted; a query names a vertex `v` with `d(v) < ∞` as reported so far. -/
def Valid (W : ℕ) (P : Program) (σ : List SSSPOp) : Prop :=
  ∀ (t : ℕ) (o : SSSPOp), σ[t]? = some o →
    match o with
    | .del e => e ∈ (I.Gt σ t).E
    | .query v => v < I.n ∧ ∃ s x, ssspProtocol.state W P I.words σ t = some s ∧ s v = some x

end SSSPInput

/-- The clauses of Theorem 10.1 with the constant `C`. -/
structure SSSPHolds (C W : ℕ) (P : Program) (I : SSSPInput) (σ : List SSSPOp) : Prop where
  runs : RunsThrough W P (ssspProtocol.blocks I.words σ)
  /-- At all times `distG(v, s) ≤ d(v) ≤ (1 + ϵ)·distG(v, s)` for every vertex `v`. -/
  log : ∀ t ≤ σ.length, ∃ st, ssspProtocol.state W P I.words σ t = some st ∧
    ∀ v ∈ (I.Gt σ t).V,
      (((I.Gt σ t).dist v I.src : ℕ∞) : ℝ≥0∞) ≤ estVal (st v) ∧
      estVal (st v) ≤ ENNReal.ofReal (1 + (I.eps : ℝ)) * (((I.Gt σ t).dist v I.src : ℕ∞) : ℝ≥0∞)
  /-- No estimate decreases. -/
  mono : ∀ t < σ.length, ∀ s s', ssspProtocol.state W P I.words σ t = some s →
    ssspProtocol.state W P I.words σ (t + 1) = some s' → ∀ v, NotDecreased (s v) (s' v)
  /-- Queries: a walk in `G` from `v` to `s` of length at most `d(v)`. -/
  query : ∀ (t v : ℕ) (st : SSSPState) (x : ℚ), σ[t]? = some (.query v) →
    ssspProtocol.state W P I.words σ t = some st → st v = some x →
    ∃ es, ssspProtocol.answer W P I.words σ t = some es ∧
      (I.Gt σ t).WalkFromTo v es I.src ∧ ((I.Gt σ t).walkLen es : ℝ) ≤ (x : ℝ) ∧
      (ssspProtocol.opTime W P I.words σ t : ℝ) ≤ polylog C I.n I.m * ((es.length : ℝ) + 1)
  /-- The total update time `C·(n + m^{1+Cϵ}·2^{C/ϵ^C}·log₂(2 + L))`. -/
  time : (ssspProtocol.updateTime W P I.words σ : ℝ) ≤
    (C : ℝ) * ((I.n : ℝ) + (I.m : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ)) * expEps C (I.eps : ℝ) * lg (I.L : ℝ))

end DecrNbhdCover.Supplement


