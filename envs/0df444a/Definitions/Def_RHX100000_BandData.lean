-- Prove2me | Definitions.Def_RHX100000_BandData
-- name    : RHX100000_BandData
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:30:28.353942+00:00
-- url     : https://prove2.me/theorems/7b144f32-f142-4d8a-b56f-7b06a483ab2e
-- title:
--   Turing band data for the box [121, 100000]
-- statement:
--   The Turing band data `RHX100000.band : BandGlue.BandData` for the box $121\le t\le100000$: $T_0=121$, $T_1=100000$, $n=138031$, the ball centre $c=1/2+i\,100121/2$ and radius $R=\sqrt{9975814658/4}$, and the proof that $1\notin B(c,R)$. The enclosure fields are zero; the count data `RHX_Count100000Data` supply the enclosures through `H11K.validS_of_B`.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_BandGlue
/-! The Turing band data `[121, 100000]` (enclosures replaced by the count data via `withEncl`). -/
open Complex BandGlue
namespace RHX100000
/-- The band data of the Turing band `[121, 100000]` (enclosures replaced by `Count.E` via `withEncl`). -/
noncomputable def band : BandData where
  T0 := 121
  T1 := 100000
  n := 138031
  L1 := 0
  H1 := 0
  L2 := 0
  H2 := 0
  L3 := 0
  H3 := 0
  L4 := 0
  H4 := 0
  L5 := 0
  H5 := 0
  c := ⟨1 / 2, (100121 : ℝ) / 2⟩
  R := Real.sqrt ((9975814658 : ℝ) / 4)
  hs1 := by
    rw [Metric.mem_ball, not_lt, dist_comm, Complex.dist_eq]
    have hR : Real.sqrt ((9975814658 : ℝ) / 4) ≤ (100121 : ℝ) / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have him : |((⟨1 / 2, (100121 : ℝ) / 2⟩ : ℂ) - 1).im| ≤ ‖(⟨1 / 2, (100121 : ℝ) / 2⟩ : ℂ) - 1‖ :=
      Complex.abs_im_le_norm _
    have hv : ((⟨1 / 2, (100121 : ℝ) / 2⟩ : ℂ) - 1).im = (100121 : ℝ) / 2 := by simp
    rw [hv, abs_of_pos (by norm_num)] at him
    linarith

end RHX100000

def RHX100000_BandData : Nat := 0


