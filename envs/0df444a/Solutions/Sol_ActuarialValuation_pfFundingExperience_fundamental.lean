-- Prove2me | solution 1 for ActuarialValuation.pfFundingExperience_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:30:41.26114+00:00
-- url     : https://prove2.me/submissions/69abc5e8-d1c2-4f8f-9aef-78e1611eb8fb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfEntryRate
import Definitions.Def_actuarial_pfAttainedRate
import Definitions.Def_actuarial_pfAggregateRate
import Definitions.Def_actuarial_pfDeficit
import Definitions.Def_actuarial_pfModifiedRate
import Definitions.Def_actuarial_pfAssetsNext
import Definitions.Def_actuarial_pfLiabilitiesNext
import Definitions.Def_actuarial_pfSurplus
import Definitions.Def_actuarial_pfSurplusMovement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (entryBenefit entryPayroll totalPV pastPV futurePayroll assets normal deficitAnnuity a l c invest benefits expenses service interest lb assumptions : ℝ) (he : entryPayroll≠0) (hf : futurePayroll≠0) (ha : deficitAnnuity≠0) : (pfEntryRate entryBenefit entryPayroll*entryPayroll=entryBenefit) ∧ (pastPV+pfAttainedRate totalPV pastPV futurePayroll*futurePayroll=totalPV) ∧ (assets+pfAggregateRate totalPV assets futurePayroll*futurePayroll=totalPV) ∧ ((pfModifiedRate normal (pfDeficit totalPV assets) deficitAnnuity-normal)*deficitAnnuity=pfDeficit totalPV assets) ∧ (pfSurplus (pfAssetsNext a c invest benefits expenses) (pfLiabilitiesNext l service interest lb assumptions)=pfSurplus a l+pfSurplusMovement c invest benefits expenses service interest lb assumptions) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold pfEntryRate
    field_simp [he] <;> ring
  · unfold pfAttainedRate
    field_simp [hf] <;> ring
  · unfold pfAggregateRate
    field_simp [hf] <;> ring
  · unfold pfModifiedRate pfAmortisation pfDeficit
    field_simp [ha] <;> ring
  · unfold pfSurplus pfAssetsNext pfLiabilitiesNext pfSurplusMovement
    ring
