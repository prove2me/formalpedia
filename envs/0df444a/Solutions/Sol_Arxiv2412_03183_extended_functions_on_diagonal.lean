-- Prove2me | solution 1 for Arxiv2412_03183.extended_functions_on_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:47:49.16095+00:00
-- url     : https://prove2.me/submissions/feac5e85-eb88-4e98-a405-75e0afc905e5

import Mathlib
import Definitions.Def_Arxiv2412_03183_Basic

open Arxiv2412_03183 in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] {N : S → ℕ}
    {M Nx Ny : ℕ} (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (hx : x ∈ nonnegImages)
    (g : Gains N) (mu1 mu2 : ℝ) (hmu1 : 0 ≤ mu1) (hmu2 : 0 ≤ mu2) :
    extDataLoss D x g g = dataLoss D x g ∧ extGainReg D mu1 mu2 g g = gainReg D mu1 mu2 g := by
  constructor
  · unfold extDataLoss dataLoss
    refine Finset.sum_congr rfl fun k _ => ?_
    have := D.sigma_pos k
    field_simp
    ring
  · unfold extGainReg gainReg
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs
    · ring
    · rfl
