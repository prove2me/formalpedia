-- Prove2me | Definitions.Def_SAGA_StronglyConvex_sagaRun
-- name    : SAGA_StronglyConvex_sagaRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:25:58.843225+00:00
-- url     : https://prove2.me/theorems/66b2580f-53af-42fc-b672-83c884d6c5fb
-- title:
--   The SAGA iterates $(x^k,\phi^k)$ along an index sequence
-- statement:
--   Let $f_1',\dots,f_n'$, $P$ and $\gamma$ be as for one SAGA iteration, and let $x^0\in E$. For $k\ge0$ and a sequence of indices $j_1,\dots,j_k\in\{1,\dots,n\}$, the **SAGA run** is the state $(x^k,\phi^k)$ obtained by starting from
--
--   $$
--   x^0,\qquad \phi^0_i=x^0\ \ (i=1,\dots,n),
--   $$
--
--   and applying one SAGA iteration with index $j_1$, then $j_2$, …, then $j_k$.
--
--   This is the state of the SAGA algorithm of Defazio, Bach and Lacoste-Julien after $k$ iterations when the random indices take the values $j_1,\dots,j_k$. Averaging a quantity of the final state over all $n^k$ sequences gives its expectation under independent uniform indices, which is how Corollary 1 is stated.
--
--   **Formalization Note** The index sequence is a function `Fin k → Fin n`; entry `t` is the index used at iteration `t + 1` (0-based on both sides).
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 2, Section 2 (initialization φ_i^0 = x^0 and the SAGA Algorithm)

import Mathlib
import Definitions.Def_SAGA_StronglyConvex_sagaStep

namespace SAGA.StronglyConvex

/-- The SAGA state `(x^k, φ^k)` after `k` iterations started at `x^0` with `φ_i^0 = x^0` for all `i`,
when the indices drawn at iterations `1, …, k` are `js 0, …, js (k-1)`. -/
noncomputable def sagaRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (f' : Fin n → E → E) (P : E → E) (γ : ℝ) (x0 : E) :
    (k : ℕ) → (Fin k → Fin n) → E × (Fin n → E)
  | 0, _ => (x0, fun _ => x0)
  | k + 1, js => sagaStep f' P γ (sagaRun f' P γ x0 k (fun t => js (Fin.castSucc t))) (js (Fin.last k))

end SAGA.StronglyConvex


