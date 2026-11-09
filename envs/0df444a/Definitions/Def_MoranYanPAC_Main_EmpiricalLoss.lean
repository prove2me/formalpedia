-- Prove2me | Definitions.Def_MoranYanPAC_Main_EmpiricalLoss
-- name    : MoranYanPAC_Main_EmpiricalLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:04:46.337385+00:00
-- url     : https://prove2.me/theorems/08de48de-70ea-48ce-ba89-9bddb70a2412
-- title:
--   Integer empirical loss and normalized error
-- statement:
--   For a finite ordered sample $S=((x_i,y_i))_{i=1}^n$, repetitions allowed, and a binary predictor $h$, the **empirical loss** is the number of mistaken positions:
--
--   $$\ell_S(h)=\sum_{i=1}^n\mathbf1\{h(x_i)\ne y_i\},\qquad L_S(h)=\ell_S(h)/n\quad(n\ge1).$$
--
--   The count is natural-valued and counts multiplicities. Filtering a list retains exactly the mistaken positions. The normalized expression is totalized to zero at the empty list, but every statistical use has a strictly positive sample threshold. This supplies the source's integer score and relative-generalization interface without importing a bounded-rank binary-loss system.
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Definition 4, p. 14 (PDF p. 14)

import Mathlib

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Definition 4, p. 14: integer mistake count, retaining repetitions. -/
def empiricalLoss {X : Type*} (S : List (X × Bool)) (h : X → Bool) : ℕ :=
  (S.filter (fun z => h z.1 ≠ z.2)).length

/-- Defined for all lists; statistical statements use positive sample sizes. -/
noncomputable def empiricalRate {X : Type*} (S : List (X × Bool)) (h : X → Bool) : ℝ :=
  (empiricalLoss S h : ℝ) / S.length

end MoranYanPAC.Main


