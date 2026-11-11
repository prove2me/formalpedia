-- Prove2me | Definitions.Def_SubquadCutReach_Faster_Rounding
-- name    : SubquadCutReach_Faster_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:59:09.506589+00:00
-- url     : https://prove2.me/theorems/43d796f8-f066-477c-aaee-c3e46e51e812
-- title:
--   Binary truncation and least-significant-bit orientation rounding
-- statement:
--   For a fractional rule $z$, set $p=(1+z)/2$ and truncate down to multiples of $2^{-B}$, where $B=\lceil\log_2 n\rceil$. The current odd numerator at bit $j$ selects a known family of potential pairs. A supplied subroutine return supplies its orientation signs.
--
--   $$p_{uv}\leftarrow p_{uv}+2^{-j}\sigma_{uv},\qquad j=B,B-1,\ldots,1.$$
--
--   The recursion specifies the probability update, including its bit order. In use, each subroutine acts on the hidden skeleton intersected with that known bit predicate. No balance property is built into the data type or presumed by this definition.
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), §A.3, Lemmas A.4–A.5, pp.22–24 (PDF pp.24–26)

import Mathlib
import Definitions.Def_SubquadCutReach_Faster_Averaging

set_option autoImplicit false

namespace SubquadCutReach.Faster

noncomputable def roundingBits (n : ℕ) : ℕ := Nat.ceil (Real.logb 2 n)

noncomputable def truncateProbability {n : ℕ} (z : Fractional n) (B : ℕ) : Fractional n :=
  fun u v => (⌊((1+z u v)/2)*(2:ℝ)^B⌋ : ℤ)/(2:ℝ)^B

/-- Odd jth numerator means that this bit still needs rounding. -/
noncomputable def oddBit {n : ℕ} (p : Fractional n) (j : ℕ) : Rule n :=
  fun u v => decide (Odd (⌊p u v*(2:ℝ)^j⌋ : ℤ))

/-- A sign comes from the balanced orientation returned for H intersected with oddBit p j.
This operation changes the probability by 2^-j, not the signed z value. -/
noncomputable def roundBit {n : ℕ} (p : Fractional n) (j : ℕ) (D : Rule n) : Fractional n :=
  fun u v => if oddBit p j u v then p u v + (if D u v then 1 else -1)/(2:ℝ)^j else p u v

/-- Stage r processes j=B-r; stages after the Bth do nothing. σ r is the actual
subroutine return at that stage, not a premise that the unknown graph is balanced. -/
noncomputable def roundingState {n : ℕ} (z : Fractional n) (B : ℕ)
    (σ : ℕ → Rule n) : ℕ → Fractional n
  | 0 => truncateProbability z B
  | r+1 => if r < B then roundBit (roundingState z B σ r) (B-r) (σ r)
    else roundingState z B σ r

end SubquadCutReach.Faster


