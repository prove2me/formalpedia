-- Prove2me | Definitions.Def_LL_Decomp1537b_I1
-- name    : LL_Decomp1537b_I1
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:31:13.627172+00:00
-- url     : https://prove2.me/theorems/61fff3ae-0654-4e44-9188-5e4b1008fca6
-- title:
--   The difference counting function
-- statement:
--   For natural numbers $N,N_1$ and an integer $h$, let $I(h)$ be the number of natural numbers $m$ with $N_1<m<N$ and $N_1<m-h<N$, that is, the number of pairs $m,\ell\in(N_1,N)$ with $m-\ell=h$.

import Mathlib

namespace LL_Decomp1537b

open Finset Real

def I1 (N N1 : ℕ) (h : ℤ) : ℕ :=
  ((Ioo N1 N).filter (fun m : ℕ => (N1 : ℤ) < (m : ℤ) - h ∧ (m : ℤ) - h < N)).card

end LL_Decomp1537b


