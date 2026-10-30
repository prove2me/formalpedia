-- Prove2me | Definitions.Def_NestedLogitAssort_General_prefixVec
-- name    : NestedLogitAssort_General_prefixVec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:46:53.748231+00:00
-- url     : https://prove2.me/theorems/546fb976-0c68-4369-a01e-577195cae7a8
-- title:
--   Prefix vector $(1,\dots,1,\rho,0,\dots,0)$
-- statement:
--   For $k\in\{1,\dots,n\}$ and $\rho\in[0,1]$, the prefix vector is $z\in[0,1]^n$ with
--
--   $$
--   z_1=\dots=z_{k-1}=1,\qquad z_k=\rho,\qquad z_{k+1}=\dots=z_n=0 .
--   $$
--
--   Lemma 6 shows that problem (8) has an optimal solution of this form.
--
--   **Formalization Note** $k$ is the paper's 1-based index; the `Fin n` index $j$ is the paper's product $j+1$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Lemma 6, p. 21

import Mathlib

namespace NestedLogitAssort.General

/-- **The prefix vector `z_{i1} = … = z_{i,k−1} = 1`, `z_{ik} = ρ`, `z_{i,k+1} = … = z_{in} = 0`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Lemma 6, p. 21: the form of the optimal solution of (8), "for some `k = 1, …, n`".

**Formalization Note.** `k` is the paper's 1-based index: the `Fin n` index `j` is the paper's
product `j + 1`. -/
noncomputable def prefixVec {n : ℕ} (k : ℕ) (ρ : ℝ) : Fin n → ℝ :=
  fun j => if j.val + 1 < k then 1 else if j.val + 1 = k then ρ else 0

end NestedLogitAssort.General


