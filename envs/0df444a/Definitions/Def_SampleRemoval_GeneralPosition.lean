-- Prove2me | Definitions.Def_SampleRemoval_GeneralPosition
-- name    : SampleRemoval_GeneralPosition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:05:55.847921+00:00
-- url     : https://prove2.me/theorems/72d8c6c3-ddb8-4c75-981b-9456e8566769
-- title:
--   General position of the design (every $d$ of the $x_i$ are linearly independent)
-- statement:
--   The design $x_1,\dots,x_n\in\mathbb R^d$ is in **general position** (GP) when every $d$ of the vectors are linearly independent: for every set $T\subseteq[n]$ of $d$ distinct indices, $\{x_i\}_{i\in T}$ is linearly independent.
--
--   With an intercept and one real regressor ($d=2$, $x_i=(1,u_i)$), GP means that the $u_i$ are distinct. Under GP the Gram matrix of a weighting is nonsingular exactly when the weighting keeps at least $d$ observations.
--
--   **Formalization Note** The condition ranges over $d$-element sets of distinct indices (`Finset (Fin n)` of cardinality $d$), not over maps $[d]\to[n]$ with possible repetitions. When $n<d$ it holds vacuously, as in the paper.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), §2, General position, p.3 (PDF p.5)

import Mathlib

set_option autoImplicit false

namespace SampleRemoval

/-- The design `x₁, …, xₙ ∈ ℝᵈ` is in general position (GP) when every `d` of the vectors are
linearly independent (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), §2, "General position", p.3).

**Formalization Note** "Every `d` of the vectors" ranges over `d`-element sets of distinct
indices (`Finset (Fin n)` of cardinality `d`), not over maps `Fin d → Fin n`, which would
allow repeated indices. When `n < d` there is no such set and the condition holds vacuously,
as in the paper. -/
def GeneralPosition {n d : ℕ} (x : Fin n → Fin d → ℝ) : Prop :=
  ∀ s : Finset (Fin n), s.card = d → LinearIndependent ℝ (fun i : s => x i)

end SampleRemoval


