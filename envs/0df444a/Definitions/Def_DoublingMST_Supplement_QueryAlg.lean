-- Prove2me | Definitions.Def_DoublingMST_Supplement_QueryAlg
-- name    : DoublingMST_Supplement_QueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:17:36.87152+00:00
-- url     : https://prove2.me/theorems/a39aeae4-a5fa-4194-b15a-8ed49d0ecec1
-- title:
--   Exact-distance query algorithms (Definition 6.2): histories and query counts
-- statement:
--   A deterministic **exact-distance query algorithm** on $n$ points is an adaptive strategy $A$: given the history of queried unordered pairs $\{x,y\}$ and the exact distances $d(x,y)$ returned so far, it either queries one more pair or stops and outputs an explicit edge set. Computation on returned values is unrestricted and free. The **query count** $q(A,d)\in\mathbb N\cup\{\infty\}$ is the number of queries made before the output ($\infty$ if $A$ never outputs). A randomized query algorithm is a family $(A_\omega)_{\omega\in\Omega}$ indexed by a probability space $(\Omega,\mu)$.
--
--   This is the model of the accuracy-dependent lower bound (Theorem 6.7); since free computation is allowed, a lower bound on queries in this model is a lower bound on real-RAM running time.
--
--   **Formalization Note** The answer to a query $\{x,y\}$ is the published `edgeCost`, which equals $d(x,y)$ for a metric.
-- source:
--   Höckendorff–Hommelsheim–Sohler–Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 6.2, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_DoublingMST_edgeCost
open scoped Classical

namespace DoublingMST.Supplement

/-!
# Exact-distance query algorithms (Definition 6.2)

Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning
Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759),
Definition 6.2, p.31 (PDF p.33): "A distance query names an unordered pair {x, y} and returns the
exact value d(x, y). Computation on values already returned is unrestricted; each query costs one
unit."

A deterministic query algorithm is an adaptive strategy: given the history of queried pairs and
their exact distances, it either queries one more unordered pair or stops with an explicit edge set.

**Formalization Note.**
* The answer to the query `s(x, y)` is `DoublingMST.edgeCost d s(x, y)`, which is `d(x, y)` for a
  metric. Computation between queries is free and arbitrary (the strategy is any function).
* `qryCount A d ∈ ℕ∞` is the number of queries before the output (`⊤` if the strategy never
  outputs); the output is the edge set returned then (`QryOutputs`).
* A randomized algorithm is a family `A : Ω → QryStrategy n` over a probability space `(Ω, μ)`.
-/

/-- A deterministic query strategy: from the history of (pair, distance) answers, the next queried
pair or the output edge set. -/
abbrev QryStrategy (n : ℕ) :=
  List (Sym2 (Fin n) × ℝ) → Sym2 (Fin n) ⊕ Finset (Sym2 (Fin n))

/-- The history after `k` rounds of `A` on the metric `d`. -/
noncomputable def qryHistory {n : ℕ} (A : QryStrategy n) (d : Fin n → Fin n → ℝ) :
    ℕ → List (Sym2 (Fin n) × ℝ)
  | 0 => []
  | k + 1 =>
    match A (qryHistory A d k) with
    | .inl e => qryHistory A d k ++ [(e, DoublingMST.edgeCost d e)]
    | .inr _ => qryHistory A d k

/-- The number of queries `A` makes on `d` before it outputs; `⊤` if it never outputs. -/
noncomputable def qryCount {n : ℕ} (A : QryStrategy n) (d : Fin n → Fin n → ℝ) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : (A (qryHistory A d k)).isRight = true), (k : ℕ∞)

/-- `A` run on `d` outputs the edge set `T`. -/
def QryOutputs {n : ℕ} (A : QryStrategy n) (d : Fin n → Fin n → ℝ)
    (T : Finset (Sym2 (Fin n))) : Prop :=
  ∃ k : ℕ, A (qryHistory A d k) = .inr T

end DoublingMST.Supplement


