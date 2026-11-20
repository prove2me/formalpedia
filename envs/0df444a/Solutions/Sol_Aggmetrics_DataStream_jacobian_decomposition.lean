-- Prove2me | solution 1 for Aggmetrics.DataStream.jacobian_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:03:12.58795+00:00
-- url     : https://prove2.me/submissions/af42d33f-0794-4cb0-819b-6c3bedbd54cc

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream

set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution
    (g : ℝ × ℝ × ℝ → ℝ) (R11 R00 π : ℝ → ℝ) (t : ℝ)
    (r11' r00' π' : ℝ)
    (hR11 : HasDerivAt R11 r11' t) (hR00 : HasDerivAt R00 r00' t) (hπ : HasDerivAt π π' t)
    (g' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (hg : HasFDerivAt g g' (R11 t, R00 t, π t)) :
    HasDerivAt (fun s => g (R11 s, R00 s, π s))
      (g' (1, 0, 0) * r11' + g' (0, 1, 0) * r00' + g' (0, 0, 1) * π') t := by
  have hpath : HasDerivAt (fun s => (R11 s, R00 s, π s)) (r11', r00', π') t :=
    hR11.prodMk (hR00.prodMk hπ)
  have hcomp : HasDerivAt (fun s => g (R11 s, R00 s, π s)) (g' (r11', r00', π')) t :=
    hg.comp_hasDerivAt t hpath
  have hval : g' (r11', r00', π')
      = g' (1, 0, 0) * r11' + g' (0, 1, 0) * r00' + g' (0, 0, 1) * π' := by
    have hsplit : (r11', r00', π') =
        r11' • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + r00' • ((0 : ℝ), (1 : ℝ), (0 : ℝ))
          + π' • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      simp
    rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  rwa [hval] at hcomp
end Aggmetrics.DataStream
