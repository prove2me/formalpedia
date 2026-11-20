-- Prove2me | Definitions.Def_RHX1000000_BandData
-- name    : RHX1000000_BandData
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-19T20:50:51.37192+00:00
-- url     : https://prove2.me/theorems/a55e0cdf-cb13-4ba4-b18c-1b848c1971f1
-- title:
--   Turing band data for the box [121, 1000000]
-- statement:
--   The band data `RHX1000000.band : BandGlue.BandData` for the box $121\le t\le10^6$: $T_0=121$, $T_1=10^6$, $n=1747108$, the ball centre $c=1/2+i\,1000121/2$ and radius $R=\sqrt{999758014658/4}$, and the proof that $1\notin B(c,R)$. The enclosure fields are zero; the count data `RHX_Count1000000Data` supply the enclosures through `H11K.validS_of_B`.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_BandGlue
/-! The Turing band data `[121, 1000000]`. -/
open Complex BandGlue
namespace RHX1000000
noncomputable def band : BandData where
  T0 := 121
  T1 := 1000000
  n := 1747108
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
  c := ⟨1 / 2, (1000121 : ℝ) / 2⟩
  R := Real.sqrt ((999758014658 : ℝ) / 4)
  hs1 := by
    rw [Metric.mem_ball, not_lt, dist_comm, Complex.dist_eq]
    have hR : Real.sqrt ((999758014658 : ℝ) / 4) ≤ (1000121 : ℝ) / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have him : |((⟨1 / 2, (1000121 : ℝ) / 2⟩ : ℂ) - 1).im| ≤ ‖(⟨1 / 2, (1000121 : ℝ) / 2⟩ : ℂ) - 1‖ :=
      Complex.abs_im_le_norm _
    have hv : ((⟨1 / 2, (1000121 : ℝ) / 2⟩ : ℂ) - 1).im = (1000121 : ℝ) / 2 := by simp
    rw [hv, abs_of_pos (by norm_num)] at him
    linarith

end RHX1000000

def RHX1000000_BandData : Nat := 0


