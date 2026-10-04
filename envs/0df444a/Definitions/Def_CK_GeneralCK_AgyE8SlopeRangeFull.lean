-- Prove2me | Definitions.Def_CK_GeneralCK_AgyE8SlopeRangeFull
-- name    : CK_GeneralCK_AgyE8SlopeRangeFull
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:39:32.577218+00:00
-- url     : https://prove2.me/theorems/ac58b2da-8c65-48bd-8583-89fa9f870b79
-- title:
--   Courtade–Kumar proof module `GeneralCK.AgyE8SlopeRangeFull` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.AgyE8SlopeRangeFull` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.AgyE8SlopeRangeFull` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.AgyE8SlopeRangeFull (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/AgyE8SlopeRangeFull.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableJet5
import Definitions.Def_CK_GeneralCK_PureGapE8RegularizedInverse
import Definitions.Def_CK_GeneralCK_PureGapE8CertificateReduction

-- ===== source module GeneralCK.AgyE8SlopeRangeFull =====
section
/-
`e8SlopeRange` is ALL of `Ioi 0`, so every `E8Admissible` region is inhabited.

WHY THIS EXISTS
===============
`4bbee9c8` ran the census: every numeric `e8SlopeRange` membership in the corpus
is one of

  17/100  3/4  77/100  79/100  81/100  83/100  17/20 = 0.85  63/20 = 3.15

and `63/20` is the largest, proved for exactly one consumer.  Zero hits for
surjectivity, `Tendsto … atTop`, or `range e8Theta`.

So NO POINT WITH `2*s + t > 3.15` HAD EVER BEEN EXHIBITED AS ADMISSIBLE.  Since
`E8PositiveOn region := ∀ s t, E8Admissible s t → region s t → …`, every theorem
over such a region is guarded by a hypothesis nobody could show is satisfiable:

  * `e8_sAxis_tail_sixteen` is a proved theorem about `16 ≤ t`,
  * residual #6 needs `119/10 ≤ t`,
  * residual #7's strip reaches `2*s + t = 16.04`.

None of that is UNSOUND -- a vacuous region makes a guarded statement true.
That is exactly the problem, and it is the same failure mode as the junk-valued
`0 ≤ deriv f x` one level up: **declared is not inhabited, and no gate we own
distinguishes a theorem with content from a theorem with an empty domain.**

THE ROUTE, WHICH IS SHORTER THAN PRECONNECTEDNESS
=================================================
`e8SlopeRange_downward` is already in the corpus, so ONE arbitrarily large
member suffices; the whole positive ray follows in a single step.  No
`IsPreconnected`, no germ at zero, no `Tendsto` -- an explicit WITNESS.

  Y_mem_e8SlopeRange (ha : 0 < a) : Y a ∈ e8SlopeRange     Jet5:131
  Y a = (2 / Real.log 2) * (a + r a * h a / (q a * ell a)) Scalar:23

and every factor of the correction term already has a positivity lemma in the
same file -- `r_pos`, `h_pos`, `q_pos`, `ell_pos` -- so `Y` dominates
`(2 / log 2) * a`, which is unbounded.  Choosing `a` makes the witness explicit
rather than asymptotic.

`4bbee9c8`'s numerics, labelled as theirs and as numeric, predicted this:
`Θ(1.0e-4) = 1.154e-3`, `Θ(43.74) = 11.61`, growing like `log₂(1/v)` with no
ceiling.  That made it a writing problem rather than a discovery problem.
-/

namespace GeneralCK.AgyE8SlopeRange

open Set GeneralCK GeneralCK.Certificates.E8TAxisStableScalar

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

theorem two_div_log_two_pos : (0 : ℝ) < 2 / Real.log 2 :=
  div_pos (by norm_num) log_two_pos

/-- `Y` dominates a linear function of `a`.  The correction term is
non-negative because each of its four factors already has a positivity lemma. -/
theorem lin_le_Y {a : ℝ} (ha : 0 < a) : (2 / Real.log 2) * a ≤ Y a := by
  have hc : 0 ≤ r a * h a / (q a * ell a) :=
    (div_pos (mul_pos (r_pos ha) (h_pos ha))
      (mul_pos (q_pos a) (ell_pos ha))).le
  unfold Y
  exact mul_le_mul_of_nonneg_left (by linarith) two_div_log_two_pos.le

/-- `e8SlopeRange` contains arbitrarily large reals, by an EXPLICIT WITNESS.
`max 1 _` keeps the parameter positive without a case split. -/
theorem exists_mem_ge (y : ℝ) : ∃ x ∈ e8SlopeRange, y ≤ x := by
  refine ⟨Y (max 1 (y * Real.log 2 / 2)),
    Certificates.E8TAxisStableJet5.Y_mem_e8SlopeRange
      (lt_of_lt_of_le one_pos (le_max_left _ _)), ?_⟩
  refine le_trans ?_ (lin_le_Y (lt_of_lt_of_le one_pos (le_max_left _ _)))
  have hb : y * Real.log 2 / 2 ≤ max 1 (y * Real.log 2 / 2) := le_max_right _ _
  calc y = (2 / Real.log 2) * (y * Real.log 2 / 2) := by
            field_simp
    _ ≤ (2 / Real.log 2) * max 1 (y * Real.log 2 / 2) :=
            mul_le_mul_of_nonneg_left hb two_div_log_two_pos.le

/-- **The normalised slope range is exactly the positive reals.** -/
theorem e8SlopeRange_eq_Ioi : e8SlopeRange = Ioi (0 : ℝ) := by
  refine Set.Subset.antisymm e8SlopeRange_subset_pos ?_
  intro y hy
  obtain ⟨x, hx, hyx⟩ := exists_mem_ge y
  exact e8SlopeRange_downward hx hy hyx

/-- Directly usable form: positivity alone puts a real in the range. -/
theorem mem_e8SlopeRange_of_pos {y : ℝ} (hy : 0 < y) : y ∈ e8SlopeRange := by
  rw [e8SlopeRange_eq_Ioi]
  exact hy

/-- **The payoff: every point of the open first quadrant is admissible.**
This is what turns the guarded region theorems from possibly-vacuous into
inhabited, and it is now a positivity check rather than a membership proof. -/
theorem e8Admissible_of_pos {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    E8Admissible s t :=
  ⟨hs, ht, mem_e8SlopeRange_of_pos hs, mem_e8SlopeRange_of_pos ht,
    mem_e8SlopeRange_of_pos (by linarith),
    mem_e8SlopeRange_of_pos (by linarith)⟩

/-- The specific number the s-axis strip needed and nobody could produce:
`2*s + t` at the top of residual #7's region. -/
theorem sixteen_point_oh_four_mem : ((1604 : ℝ) / 100) ∈ e8SlopeRange :=
  mem_e8SlopeRange_of_pos (by norm_num)

/-- And residual #6's region, for the same reason. -/
theorem tail_twenty_mem : ((20 : ℝ)) ∈ e8SlopeRange :=
  mem_e8SlopeRange_of_pos (by norm_num)

#check @lin_le_Y
#check @exists_mem_ge
#check @e8SlopeRange_eq_Ioi
#check @mem_e8SlopeRange_of_pos
#check @e8Admissible_of_pos
#check @sixteen_point_oh_four_mem
#check @tail_twenty_mem

#print axioms lin_le_Y
#print axioms exists_mem_ge
#print axioms e8SlopeRange_eq_Ioi
#print axioms mem_e8SlopeRange_of_pos
#print axioms e8Admissible_of_pos
#print axioms sixteen_point_oh_four_mem
#print axioms tail_twenty_mem

end GeneralCK.AgyE8SlopeRange

/- AUDIT DIRECTIVES BELOW ARE GENERATED FROM THE .ilean -- DO NOT HAND-EDIT.

   Written by add_audit_directives.py.  The fleet runner audits what the
   SOURCE asks for, not what the module contains; before this block this
   module asked for 7 of 9.  A hand-maintained audit list is the
   defect this fixes, so regenerate rather than edit.

   Appended at END OF FILE, and written as a plain block comment rather
   than a module-doc one, both deliberately.  The olean records declaration
   source positions, so an end-of-file append shifts none of them; and a
   module-doc comment is stored IN the olean whereas a plain one is not.
   Measured on FsBracket, same source and toolchain: plain block comment
   29583046ed845886, bit-identical to a rebuild of the untouched source;
   module-doc comment 19890736562e5d6a, moved.

   This comment deliberately does NOT quote either block-comment delimiter.
   Lean NESTS block comments, so an inner opener would make the closer below
   close only the inner one and every directive after it would silently be
   commented out.  The first draft of this header did exactly that and the
   A1 assertion caught it on the positive control. -/
#print axioms GeneralCK.AgyE8SlopeRange.log_two_pos
#print axioms GeneralCK.AgyE8SlopeRange.two_div_log_two_pos

end


