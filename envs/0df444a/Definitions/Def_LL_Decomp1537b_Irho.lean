-- Prove2me | Definitions.Def_LL_Decomp1537b_Irho
-- name    : LL_Decomp1537b_Irho
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:31:26.056207+00:00
-- url     : https://prove2.me/theorems/3e144858-7e7f-4124-a7df-a6b6e45a061a
-- title:
--   The weighted difference sum
-- statement:
--   For natural numbers $N,N_1$, an integer $h$ and complex numbers $\rho,\rho'$, let $I(h,\rho,\rho')=\sum m^{\rho-1}(m-h)^{\rho'-1}$, the sum over natural numbers $m$ with $N_1<m<N$ and $N_1<m-h<N$, with complex powers taken via the principal branch as in Mathlib.

import Mathlib

namespace LL_Decomp1537b

open Finset Real

noncomputable def Irho (N N1 : ℕ) (h : ℤ) (ρ ρ' : ℂ) : ℂ :=
  ∑ m ∈ (Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N),
    (m : ℂ) ^ (ρ - 1) * (((m : ℤ) - h : ℤ) : ℂ) ^ (ρ' - 1)

end LL_Decomp1537b


