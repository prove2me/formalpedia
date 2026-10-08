-- Prove2me | Definitions.Def_SAGA_Convex_sagaRun
-- name    : SAGA_Convex_sagaRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:43:32.776017+00:00
-- url     : https://prove2.me/theorems/964f561d-f56e-4ce4-8854-27b3b8127df4
-- title:
--   SAGA run from $x^0$, the averaged iterate $\bar x^k$ and the expectation over indices
-- statement:
--   SAGA starts at $x^0\in\mathbb R^d$ with the table $\phi_i^0=x^0$ for every $i$. For a sequence of indices $j^1,\dots,j^k\in\{1,\dots,n\}$, let $x^t$ ($0\le t\le k$) be the iterate after the steps with indices $j^1,\dots,j^t$; it depends on the first $t$ indices only. The **averaged iterate** is
--
--   $$
--   \bar x^k=\frac1k\sum_{t=1}^k x^t ,
--   $$
--
--   which excludes $x^0$. When the indices are drawn independently and uniformly from $\{1,\dots,n\}$, the **expectation** of a quantity $g(j^1,\dots,j^k)$ is
--
--   $$
--   \mathbb E[g]=\frac1{n^k}\sum_{(j^1,\dots,j^k)\in\{1,\dots,n\}^k} g(j^1,\dots,j^k).
--   $$
--
--   These objects give a precise meaning to "the expectation over all choices of index $j^k$ up to step $k$" in Theorem 2.
--
--   **Formalization Note** `sagaRun` folds `sagaStep` over a list of indices; `sagaIterate f' P γ x0 js t` is $x^t$ for `js : Fin k → Fin n`, computed from the first $t$ entries; `avgIterate` is $\bar x^k$; `expectIdx n k g` is the uniform average over `Fin k → Fin n`, which is exactly the law of $k$ i.i.d. uniform indices. No measure theory is used.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 2 (initialization phi_i^0 = x^0) and p. 11, Theorem 2 (averaged iterate, expectation)

import Mathlib
import Definitions.Def_SAGA_Convex_sagaStep

namespace SAGA.Convex

/-- The SAGA state after applying the steps with the indices of the list `l`, in order, from the
initial state `(x^0, φ^0)` with `φᵢ^0 = x^0` for every `i` (p. 2). -/
noncomputable def sagaRun {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) (l : List (Fin n)) :
    EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) :=
  l.foldl (sagaStep f' P γ) (x0, fun _ => x0)

/-- The iterate `x^t` for the index sequence `js = (j^1, …, j^k)`: the iterate after the first
`t` steps (for `t ≤ k`; it uses only the first `t` indices). -/
noncomputable def sagaIterate {d n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) (js : Fin k → Fin n) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  (sagaRun f' P γ x0 ((List.ofFn js).take t)).1

/-- The averaged iterate `x̄^k = (1/k) ∑_{t=1}^k x^t` (Theorem 2, p. 11), which excludes `x^0`. -/
noncomputable def avgIterate {d n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) (js : Fin k → Fin n) : EuclideanSpace ℝ (Fin d) :=
  (1 / (k : ℝ)) • ∑ t ∈ Finset.range k, sagaIterate f' P γ x0 js (t + 1)

/-- The expectation over `k` independent indices, each uniform on `Fin n`: the uniform average
`(1/n^k) ∑_{js : Fin k → Fin n} g(js)`. -/
noncomputable def expectIdx (n k : ℕ) (g : (Fin k → Fin n) → ℝ) : ℝ :=
  (1 / (n : ℝ) ^ k) * ∑ js, g js

end SAGA.Convex


