-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDiffStepExpansion
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDiffStepExpansion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:47.765106+00:00
-- url     : https://prove2.me/theorems/900f1e3c-cf23-450d-83dc-529c0430df4b
-- title:
--   PDiff Step Expansion
-- statement:
--   Definitions and structural lemmas for PDiff Step Expansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDiffStepExpansion.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
namespace DiffStepExpansion
variable {K : Type}
lemma listSum_apply {α : Type} (l : List α) (F : α → (K → ℤ) → ℤ) (m : K → ℤ) :
    (l.map F).sum m = (l.map fun t => F t m).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp [ih]
def expand [DecidableEq K] (l : List ((K × (K → ℤ)) × ℤ)) (f : (K → ℤ) → ℤ) : (K → ℤ) → ℤ :=
  (l.map fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)).sum
lemma expand_apply [DecidableEq K] (l : List ((K × (K → ℤ)) × ℤ)) (f : (K → ℤ) → ℤ)
    (m : K → ℤ) :
    expand l f m = (l.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)).sum := by
  unfold expand
  rw [listSum_apply]
  rfl
def expandable (K : Type) [DecidableEq K] : AddSubgroup (K → ℤ) where
  carrier := {b | ∃ l : List ((K × (K → ℤ)) × ℤ), ∀ f, diffStep b f = expand l f}
  zero_mem' := ⟨[], fun f => by funext m; simp [diffStep, expand]⟩
  add_mem' := by
    rintro a c ⟨la, ha⟩ ⟨lc, hc⟩
    refine ⟨la ++ lc.map (fun t => ((t.1.1, t.1.2 + a), t.2)), fun f => ?_⟩
    funext m
    have h1 := congrFun (ha f) m
    have h2 := congrFun (hc f) (m - a)
    simp only [diffStep] at h1 h2 ⊢
    rw [expand_apply] at h1 h2
    rw [expand_apply, List.map_append, List.sum_append, List.map_map, ← h1]
    have h3 : (lc.map ((fun t : (K × (K → ℤ)) × ℤ =>
          t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)) ∘
          fun t => ((t.1.1, t.1.2 + a), t.2))).sum =
        (lc.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m - a - t.1.2)).sum := by
      congr 1
      apply List.map_congr_left
      intro t _
      simp only [Function.comp_apply]
      congr 2
      abel
    rw [h3, ← h2]
    have : m - (a + c) = m - a - c := by abel
    rw [this]
    ring
  neg_mem' := by
    rintro c ⟨lc, hc⟩
    refine ⟨lc.map (fun t => ((t.1.1, t.1.2 - c), -t.2)), fun f => ?_⟩
    funext m
    have h2 := congrFun (hc f) (m + c)
    simp only [diffStep] at h2 ⊢
    rw [expand_apply] at h2
    rw [expand_apply, List.map_map]
    have h3 : (lc.map ((fun t : (K × (K → ℤ)) × ℤ =>
          t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)) ∘
          fun t => ((t.1.1, t.1.2 - c), -t.2))).sum =
        -(lc.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m + c - t.1.2)).sum := by
      clear hc h2
      induction lc with
      | nil => simp
      | cons t l ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_apply] at ih ⊢
        have e : m - (t.1.2 - c) = m + c - t.1.2 := by abel
        rw [ih, e]
        ring
    rw [h3, ← h2]
    have e1 : m + c - c = m := by abel
    have e2 : m - -c = m + c := by abel
    rw [e1, e2]
    ring
end DiffStepExpansion
end
end GroundTheory.Heights₂.Heights.NumbersDVR


