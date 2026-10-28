-- Prove2me | Definitions.Def_LL_Decomp1525c_PsiV
-- name    : LL_Decomp1525c_PsiV
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-28T17:02:22.472429+00:00
-- url     : https://prove2.me/theorems/8e46d786-8813-4a3d-bc0c-bb7559dcb42d
-- title:
--   Weighted count of prime pairs
-- statement:
--   For real $x$, $\Psi(x)$ sums $\log p_1$ over prime pairs satisfying $3\le p_1\le\lfloor x-3\rfloor_+$, $1\le p_2\le\lfloor 2x-p_1\rfloor_+$, and $x-p_1<p_2$.

import Mathlib
open Finset Real MeasureTheory intervalIntegral
open scoped Classical
noncomputable section
namespace LL_Decomp1525c
def PsiV (x : ℝ) : ℝ :=
  ∑ p₁ ∈ (Icc 3 ⌊x - 3⌋₊).filter Nat.Prime,
    ∑ _p₂ ∈ (Icc 1 ⌊2 * x - p₁⌋₊).filter (fun p : ℕ => p.Prime ∧ x - p₁ < (p : ℝ)), Real.log p₁
end LL_Decomp1525c


