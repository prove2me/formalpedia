-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaExhaustion_F000
-- name    : LevyStochCalc_Ito_ItoFormulaExhaustion_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:01:15.493732+00:00
-- url     : https://prove2.me/theorems/0d79b53f-fcb8-454c-86ab-2f52d6fe20ad
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaExhaustion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaExhaustion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Transferring an identity along an exhausting family of events

An almost-everywhere identity that holds on each member of a family of events covering almost
every sample point holds outright. The family used to localise an Itô formula is the set of
sample points whose path stays inside a ball over a bounded window; a path that is bounded on
that window lies in one of them, so the family covers, and on the `m`-th member a function and
its cutoff at radius `m` agree along the path together with their first two derivatives.

## Main statements

* `LevyStochCalc.Brownian.Ito.ae_eq_of_ae_eq_on_exhausting` — the transfer.
* `LevyStochCalc.Brownian.Ito.boundedPathSet` — the sample points whose path stays in a ball.
* `LevyStochCalc.Brownian.Ito.ae_exists_mem_boundedPathSet` — a path bounded on the window lies
  in one member of the family.
* `LevyStochCalc.Brownian.Ito.cutoffFun_eq_on_boundedPathSet` — on the `m`-th member the cutoff
  at a strictly larger radius agrees with the function along the path, as do its first two
  derivatives.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory

universe u

section Transfer

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- An identity holding almost everywhere on each member of a family of events that covers almost
every sample point holds almost everywhere. -/
theorem ae_eq_of_ae_eq_on_exhausting {L R : Ω → ℝ} {S : ℕ → Set Ω}
    (hcover : ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ S m)
    (h : ∀ m : ℕ, ∀ᵐ ω ∂P, ω ∈ S m → L ω = R ω) :
    L =ᵐ[P] R := by
  have hall : ∀ᵐ ω ∂P, ∀ m : ℕ, ω ∈ S m → L ω = R ω := (MeasureTheory.ae_all_iff).2 h
  filter_upwards [hcover, hall] with ω hω hall'
  obtain ⟨m, hm⟩ := hω
  exact hall' m hm
end Transfer

section BoundedPaths

variable {Ω : Type u} {n : ℕ}

/-- The sample points whose path stays in the closed ball of radius `m` over `[0, T]`. -/
def boundedPathSet (X : ℝ → Ω → Fin n → ℝ) (T : ℝ) (m : ℕ) : Set Ω :=
  {ω : Ω | ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X s ω‖ ≤ (m : ℝ)}
theorem boundedPathSet_mono (X : ℝ → Ω → Fin n → ℝ) (T : ℝ) {m m' : ℕ} (h : m ≤ m') :
    boundedPathSet X T m ⊆ boundedPathSet X T m' := fun _ hω s hs =>
  (hω s hs).trans (by exact_mod_cast h)
/-- A path bounded on the window lies in one member of the family. -/
theorem exists_mem_boundedPathSet {X : ℝ → Ω → Fin n → ℝ} {T : ℝ} {ω : Ω}
    (h : ∃ M : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X s ω‖ ≤ M) :
    ∃ m : ℕ, ω ∈ boundedPathSet X T m := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨m, hm⟩ := exists_nat_ge M
  exact ⟨m, fun s hs => (hM s hs).trans hm⟩
/-- A continuous path is bounded on a bounded window, so it lies in one member of the family. -/
theorem exists_mem_boundedPathSet_of_continuous {X : ℝ → Ω → Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T)
    {ω : Ω} (hX : Continuous fun s => X s ω) :
    ∃ m : ℕ, ω ∈ boundedPathSet X T m := by
  obtain ⟨s₀, _, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMaxOn
    (Set.nonempty_Icc.2 hT) hX.norm.continuousOn
  exact exists_mem_boundedPathSet ⟨‖X s₀ ω‖, fun s hs => hmax hs⟩
variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- If almost every path is bounded on the window, the family covers almost every sample point. -/
theorem ae_exists_mem_boundedPathSet {X : ℝ → Ω → Fin n → ℝ} {T : ℝ}
    (h : ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X s ω‖ ≤ M) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ boundedPathSet X T m := by
  filter_upwards [h] with ω hω
  exact exists_mem_boundedPathSet hω
end BoundedPaths

section Cutoff

variable {Ω : Type u} {n : ℕ}

/-- On the `m`-th member of the family the cutoff at a strictly larger radius agrees with the
function along the path, together with its first two derivatives. -/
theorem cutoffFun_eq_on_boundedPathSet {f : (Fin n → ℝ) → ℝ}
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {X : ℝ → Ω → Fin n → ℝ} {T : ℝ} {m k : ℕ} (hmk : (m : ℝ) < (k : ℝ))
    {ω : Ω} (hω : ω ∈ boundedPathSet X T m) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    cutoffFun f (k : ℝ) (X s ω) = f (X s ω)
      ∧ fderiv ℝ (cutoffFun f (k : ℝ)) (X s ω) = f' (X s ω)
      ∧ fderiv ℝ (fderiv ℝ (cutoffFun f (k : ℝ))) (X s ω) = f'' (X s ω) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg m) hmk
  have hlt : ‖X s ω‖ < 3 * (k : ℝ) / 2 :=
    lt_of_lt_of_le (lt_of_le_of_lt (hω s hs) hmk) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · exact (cutoffFun_eventuallyEq hk0 hlt).self_of_nhds
  · rw [fderiv_cutoffFun hk0 hlt]
    exact (hf (X s ω)).fderiv
  · have hff : fderiv ℝ f = f' := funext fun z => (hf z).fderiv
    rw [fderiv_fderiv_cutoffFun hk0 hlt, hff]
    exact (hf' (X s ω)).fderiv
end Cutoff

end LevyStochCalc.Brownian.Ito


