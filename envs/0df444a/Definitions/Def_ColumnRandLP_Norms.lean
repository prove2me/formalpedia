-- Prove2me | Definitions.Def_ColumnRandLP_Norms
-- name    : ColumnRandLP_Norms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:18.533813+00:00
-- url     : https://prove2.me/theorems/19d37641-13cf-4f21-9463-8b8636a1c67b
-- title:
--   The norms $\|v\|_1$, $\|v\|_2$, $\|v\|_\infty$ and $\|A\|_{\max}=\max_{ij}|A_{ij}|$
-- statement:
--   For a vector $v\in\mathbb R^d$ the module fixes the three norms used throughout the paper,
--   $$
--   \|v\|_1=\sum_{i=1}^d |v_i|,\qquad \|v\|_2=\Big(\sum_{i=1}^d v_i^2\Big)^{1/2},\qquad \|v\|_\infty=\max_{i}|v_i|,
--   $$
--   and, for an $m\times n$ matrix $A$, the max-entry norm
--   $$
--   \|A\|_{\max}=\max_{i,j}|A_{ij}|.
--   $$
--
--   These are the quantities in which the deviation bounds (Lemmas EC.1 and EC.2), the sensitivity step (EC.12) and the constant of Theorem 1 are expressed.
--
--   **Formalization Note** Vectors are functions `Fin d → ℝ` and the norms are written as explicit sums and suprema (`l1Norm`, `l2Norm`, `supNorm`, `Amax`) rather than through Mathlib's norm on `Fin d → ℝ` (which is the sup norm). The maxima are `⨆` over finite index types; on an empty index type they equal $0$.
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, §3.1, p.6 (ℓ1, ℓ2, ℓ∞ norms and ‖A‖max); Theorem 1, p.7 (‖A‖max = maxij |Aij|)

import Mathlib

namespace ColumnRandLP

/-- `‖A‖_max = max_{i,j} |A_{ij}|` (Akchen–Mišić, arXiv:2007.10461v5, §3.1, p.6, and
Theorem 1, p.7).

**Formalization Note** Written as `⨆ i, ⨆ j, |A i j|` over the finite index types; this is the
maximum when `m, n ≥ 1` and `0` for an empty matrix. -/
noncomputable def Amax {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨆ i, ⨆ j, |A i j|

/-- `‖v‖∞ = max_i |v_i|` (Akchen–Mišić, arXiv:2007.10461v5, §3.1, p.6).

**Formalization Note** `⨆ i, |v i|`; `0` for the empty vector. -/
noncomputable def supNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ⨆ i, |v i|

/-- `‖v‖₁ = ∑_i |v_i|` (Akchen–Mišić, arXiv:2007.10461v5, §3.1, p.6). -/
def l1Norm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ∑ i, |v i|

/-- `‖v‖₂ = √(∑_i v_i²)` (Akchen–Mišić, arXiv:2007.10461v5, §3.1, p.6). -/
noncomputable def l2Norm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

end ColumnRandLP


