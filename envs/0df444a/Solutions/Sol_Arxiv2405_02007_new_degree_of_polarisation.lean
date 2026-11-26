-- Prove2me | solution 1 for Arxiv2405_02007.new_degree_of_polarisation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:36:28.161995+00:00
-- url     : https://prove2.me/submissions/8b1cf02b-de8d-4fdb-b978-2a3d3075cce7

import Mathlib
import Definitions.Def_Arxiv2405_02007_Basic

set_option autoImplicit false

open Arxiv2405_02007 in
theorem solution (span m m' dPv : ℝ) (hspan : 0 < span) (hm0 : 0 ≤ m)
    (hm1 : m ≤ 1) (h11 : volumePower m' span = volumePower m span + dPv) :
    m' = (span - volumePower m span - dPv) / span := by
  unfold volumePower at *
  field_simp
  linarith
