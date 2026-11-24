-- Prove2me | solution 1 for AbsorbK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:15:01.082799+00:00
-- url     : https://prove2.me/submissions/016f68bc-9301-42b2-b8a4-bbe80b2240bd

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_AbsorbK

set_option autoImplicit false
@[expose] public section
public section
open Real
theorem _root_.solution (k δ a b s A : ℝ) (hk : 1 ≤ k) (hδ0 : 0 ≤ δ) (hA : 0 ≤ A)
    (hsa : (1 - δ) * a ≤ s) :
    s - (k + 1 - δ) * a + k * (|b| / Real.pi) + (k - δ) * A
      ≤ k * (s + |b| / Real.pi - (2 - δ) * a + A) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hk) (sub_nonneg.2 hsa), mul_nonneg hδ0 hA]
