-- Prove2me | Definitions.Def_SampleRemoval_ind
-- name    : SampleRemoval_ind
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:05:46.953659+00:00
-- url     : https://prove2.me/theorems/c03cbb22-6544-4e2d-a708-2ffa900575b7
-- title:
--   Indicator vector $\mathbf 1_S$ of a set of observations
-- statement:
--   For a set $S\subseteq[n]$ of observations, its **indicator** is the weight vector $\mathbf 1_S\in\{0,1\}^n$ with
--
--   $$
--   (\mathbf 1_S)_i=\begin{cases}1,& i\in S,\\ 0,& i\notin S.\end{cases}
--   $$
--
--   Integral weight vectors are exactly the indicators: the weighting $\mathbf 1_S$ keeps the observations in $S$ and removes the other $n-|S|$.
--
--   **Formalization Note** $S$ is a `Finset (Fin n)`; the paper's index $i$ is the Lean index $i-1$. The full sample $[n]$ is `Finset.univ`.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), §2, Weighted least squares, p.3 (PDF p.5)

import Mathlib

set_option autoImplicit false

namespace SampleRemoval

/-- The indicator vector `1_S ∈ {0, 1}ⁿ` of a set `S ⊆ [n]` of observations
(Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), §2, "Weighted least squares", p.3: "For S ⊆ [n] we write 1S for its indicator").

**Formalization Note** `S` is a `Finset (Fin n)`; the paper's index `i ∈ [n]` is the Lean
index `i − 1`. `ind Finset.univ` is the all-ones weight, i.e. the full sample `[n]`. -/
def ind {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

end SampleRemoval


