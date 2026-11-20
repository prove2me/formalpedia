-- Prove2me | Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
-- name    : Kyprianou_Ch08_ScaleConvolutionPower
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T23:52:29.381322+00:00
-- url     : https://prove2.me/theorems/4743b14f-b346-451d-bd1e-6ede8f93be2c
-- title:
--   Chapter 8 causal scale-function convolution powers
-- statement:
--   Chapter 8 Lemma 8.3 (8.23) requires the recursively defined causal convolution powers W^(∗(n+1)). We provide their exact zero-based real-valued recurrence over 0<s≤x, using W as the base case.
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3, (8.22)–(8.24), printed p. 221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

/-- Zero-based causal convolution powers of a q-scale kernel. -/
noncomputable def scaleConvolutionPower (W : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => W
  | n + 1 => fun x =>
      ∫ s in Set.Ioc (0 : ℝ) x, W s * scaleConvolutionPower W n (x - s)

end Kyprianou.Ch08.StageB


