-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_Rounding
-- name    : MultiSpinCounting_Positive_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:30.53139+00:00
-- url     : https://prove2.me/theorems/c030ab60-4976-4664-9da7-9d61c421a6c9
-- title:
--   Outward dyadic rounding at fixed precision
-- statement:
--   For $x>0$, put $s=\lfloor\log_2x\rfloor$ and, for precision $P$, let
--   $$h_P(x)=2^{s-P+1},\quad \operatorname{round}_P^-(x)=h_P(x)\lfloor x/h_P(x)\rfloor,\quad \operatorname{round}_P^+(x)=h_P(x)\lceil x/h_P(x)\rceil,\quad \xi_P=2^{2-P}.$$
--   The step and both rounded values are dyadic rationals, even when $x$ is real. The computational input is a positive rational together with $P\ge3$; both rounded values are serialized as output. The functions are total, while every theorem applies their guarantees only to positive inputs. These are the exact outward-rounding constructions used by the recursive polytopes.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 9, §2.4 and (2.2)

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Encoding

noncomputable section

namespace MultiSpinCounting.Positive

/-- §2.4. The floor-log exponent is the unique s for positive x. -/
def roundExponent (x : ℝ) : ℤ := ⌊Real.log x / Real.log 2⌋

def roundStep (P : ℕ) (x : ℝ) : ℚ := (2 : ℚ) ^ (roundExponent x - (P : ℤ) + 1)

def roundDown (P : ℕ) (x : ℝ) : ℚ :=
  roundStep P x * (⌊x / (roundStep P x : ℝ)⌋ : ℤ)

def roundUp (P : ℕ) (x : ℝ) : ℚ :=
  roundStep P x * (⌈x / (roundStep P x : ℝ)⌉ : ℤ)

def roundingAccuracy (P : ℕ) : ℝ := (2 : ℝ) ^ ((2 : ℤ) - (P : ℤ))

def encRoundingInput (P : ℕ) (x : ℚ) : List OnlineCRS.Combine.Sym :=
  OnlineCRS.Combine.encNat P ++ [3] ++ OnlineCRS.Combine.encRat x

def encRoundingOutput (P : ℕ) (x : ℝ) : List OnlineCRS.Combine.Sym :=
  OnlineCRS.Combine.encRat (roundDown P x) ++ [3] ++ OnlineCRS.Combine.encRat (roundUp P x)

end MultiSpinCounting.Positive


