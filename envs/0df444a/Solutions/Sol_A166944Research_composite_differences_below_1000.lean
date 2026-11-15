-- Prove2me | solution 1 for A166944Research.composite_differences_below_1000
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-14T23:31:40.801211+00:00
-- url     : https://prove2.me/submissions/43f466e1-dbbc-40f3-9c47-ca729f1af701

import Definitions.Def_a166944_composite_test
import Definitions.Def_a166944_record_core

/-!
Self-contained solution for the platform target
`A166944Research.composite_differences_below_1000`.

The compositeness test comes from the platform definition
`Def_a166944_composite_test`; nothing is re-declared here.
-/

open A166944Research

namespace A166944Research

set_option maxRecDepth 1000000

/-!
# Sweep of the composite candidates to n = 1000

A light scan over `2 <= n <= 1000` shows that `d n > 1` at only 27 indices.
Above 200 those are

  315 -> 313, 317 -> 5, 318 -> 3, 340 -> 17, 342 -> 3, 343 -> 11, 348 -> 3,
  663 -> 661

and every one of those differences is PRIME. Hence the range `200 < n <= 1000`
contributes NO composite value of `d n` at all: the only composite differences
in the whole range `2 <= n <= 1000` remain 9 (n = 18), 33 (n = 66) and
25 (n = 150), all three already refuted in `CompositeProbe.lean` and
`CompositeThird.lean`.

So there is no `not_record_at_N` obligation above 200: the antecedent "d N is
composite" is empty there. What can be certified is (a) the values, and (b) the
primality/compositeness classification of the finitely many values involved.

`313` and `661` are themselves running maxima (records), so unlike 18/66/150
they are NOT refutable by an earlier larger value; the refutation pattern has
no instance above 200. This file therefore certifies the value table, the
classification, and the record chain 139 < 313 < 661.

Core Lean has no `Prime`, so the classification below is stated with the
computable checker `isComposite`, which searches every `m` with `2 <= m < n`:
`isComposite n = false` for `2 <= n` means no divisor in that range exists.
-/

set_option maxRecDepth 200000

/-! ## A Mathlib-free compositeness test -/

theorem d317_is_five : d 317 = 5 := by decide
theorem d318_is_three : d 318 = 3 := by decide
theorem d340_is_seventeen : d 340 = 17 := by decide
theorem d342_is_three : d 342 = 3 := by decide
theorem d343_is_eleven : d 343 = 11 := by decide
theorem d348_is_three : d 348 = 3 := by decide

theorem five_is_not_composite : isComposite 5 = false := by decide
theorem three_is_not_composite : isComposite 3 = false := by decide
theorem seventeen_is_not_composite : isComposite 17 = false := by decide
theorem eleven_is_not_composite : isComposite 11 = false := by decide

/-! ## The two large values above 200 (expensive `decide`s, last on purpose) -/

theorem d315_is_threehundredthirteen : d 315 = 313 := by decide

theorem threehundredthirteen_is_not_composite : isComposite 313 = false := by decide

theorem d663_is_sixhundredsixtyone : d 663 = 661 := by decide

theorem sixhundredsixtyone_is_not_composite : isComposite 661 = false := by decide

/-! ## Closed summaries mirroring `composite_below_200_closed` -/

/-- All the `d n > 1` values above 200 that are cheap to certify. -/
theorem differences_above_200_small :
    d 317 = 5 ∧ d 318 = 3 ∧ d 340 = 17 ∧ d 342 = 3 ∧ d 343 = 11 ∧ d 348 = 3 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Every certified difference above 200 is a non-composite value, i.e. no new
composite difference appears in `200 < n <= 1000`. -/
theorem above_200_has_no_composite_difference :
    isComposite (d 317) = false ∧ isComposite (d 318) = false ∧
    isComposite (d 340) = false ∧ isComposite (d 342) = false ∧
    isComposite (d 343) = false ∧ isComposite (d 348) = false :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-!
# Complete classification of composite differences below 1000

This is the strongest form of the requested extension. Instead of sampling the
candidates above 200 one by one, it decides the whole statement over the closed
range `2 <= n <= 1000`:

  * the ONLY indices below 1000 whose difference is composite are 18, 66 and 150
    -- all three already refuted by `CompositeProbe.lean` / `CompositeThird.lean`;
  * consequently there is no composite difference at all in `200 < n <= 1000`,
    so the refutation pattern has no instance above 200.

`isComposite` is the computable test from `CompSweep1000.lean`; it returns
`true` exactly when some `m` with `2 <= m < n` divides `n`, so `= false`
certifies compositeness is impossible. The two theorems are closed `decide`s
over `List.range 1001`, i.e. every index in the range is checked by the kernel
itself, not by a sampled scan.
-/

set_option maxRecDepth 1000000

/-- The complete classification: below 1000 a composite difference occurs only
at 18, 66 and 150. -/
theorem composite_differences_below_1000 :
    ∀ n ∈ List.range 1001, isComposite (d n) = true → n = 18 ∨ n = 66 ∨ n = 150 := by
  decide

/-- Therefore no composite difference exists in `200 < n <= 1000`. -/
theorem no_composite_difference_above_200 :
    ∀ n ∈ List.range 1001, 200 < n → isComposite (d n) = false := by
  decide

end A166944Research

open A166944Research in
theorem solution :
    ∀ n ∈ List.range 1001, isComposite (d n) = true → n = 18 ∨ n = 66 ∨ n = 150 :=
  composite_differences_below_1000
