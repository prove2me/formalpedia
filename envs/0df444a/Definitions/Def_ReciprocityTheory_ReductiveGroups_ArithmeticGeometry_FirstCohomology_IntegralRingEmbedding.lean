-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:44:07.200204+00:00
-- url     : https://prove2.me/theorems/2c7c157c-d5c2-479d-9254-b80973ce21ee
-- title:
--   Integral Ring Embedding
-- statement:
--   Definitions and structural lemmas for Integral Ring Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
open Module
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
lemma wt_inv_nonneg {a b : WithTop ℚ} (h : a + b = 0) (ha : a < 0) : 0 ≤ b := by
  have ha' : a ≠ ⊤ := ne_top_of_lt ha
  lift a to ℚ using ha'
  induction b using WithTop.recTopCoe with
  | top => exact le_top
  | coe q =>
    have h1 : (a : ℚ) + q = 0 := by exact_mod_cast h
    have h2 : (a : ℚ) < 0 := by exact_mod_cast ha
    exact_mod_cast (show (0 : ℚ) ≤ q by linarith)
def intRing : ValuationSubring F where
  carrier := {a | 0 ≤ v a}
  mul_mem' := fun {a b} ha hb => by
    show 0 ≤ v (a * b)
    rw [AddValuation.map_mul]; exact add_nonneg ha hb
  one_mem' := by show 0 ≤ v 1; rw [AddValuation.map_one]
  add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
  zero_mem' := by show 0 ≤ v 0; rw [AddValuation.map_zero]; exact le_top
  neg_mem' := fun {a} ha => by show 0 ≤ v (-a); rw [AddValuation.map_neg]; exact ha
  mem_or_inv_mem' := by
    intro a
    by_cases ha : 0 ≤ v a
    · exact Or.inl ha
    · right
      push Not at ha
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [AddValuation.map_zero] at ha; exact absurd ha (not_lt.mpr le_top)
      show 0 ≤ v a⁻¹
      have : v a + v a⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ ha0, AddValuation.map_one]
      exact wt_inv_nonneg this ha
section Core
variable {W : Type} [AddCommGroup W] [Module F W] {n : ℕ} (b : Fin n → W)
def emb : (Fin n → intRing v) →+ W where
  toFun c := ∑ i, ((c i : intRing v) : F) • b i
  map_zero' := by simp
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
end Core
end ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding


