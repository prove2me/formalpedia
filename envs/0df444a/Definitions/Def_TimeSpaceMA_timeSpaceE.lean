-- Prove2me | Definitions.Def_TimeSpaceMA_timeSpaceE
-- name    : TimeSpaceMA_timeSpaceE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:10.763067+00:00
-- url     : https://prove2.me/theorems/65ea5e6d-7746-4705-ace6-1d47791e1bd9
-- title:
--   The bound $E=\max\{N,\,T^{3/4}N^{1/8}S^{1/2},\,T^{1/3}N^{2/3}S^{1/6}\}$
-- statement:
--   For real $T,N,S$,
--   $$E := \max\{N,\ T^{3/4}N^{1/8}S^{1/2},\ T^{1/3}N^{2/3}S^{1/6}\}.$$
--   This is the quantity that bounds Merlin's message length and Arthur's running time, up to $t^\varepsilon$.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), §3.1, p.8; Theorem 3.1, p.6

import Mathlib

namespace TimeSpaceMA

/-- The bound `E := max{N, T^{3/4} N^{1/8} S^{1/2}, T^{1/3} N^{2/3} S^{1/6}}` (Williams, Xi, STOC 2027
submission, manuscript sha256 184c2f95…, §3.1, p.8, and Theorem 3.1, p.6). -/
noncomputable def timeSpaceE (T N S : ℝ) : ℝ :=
  max N (max (T ^ (3 / 4 : ℝ) * N ^ (1 / 8 : ℝ) * S ^ (1 / 2 : ℝ))
    (T ^ (1 / 3 : ℝ) * N ^ (2 / 3 : ℝ) * S ^ (1 / 6 : ℝ)))

end TimeSpaceMA


