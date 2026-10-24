-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part4
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:44:10.005056+00:00
-- url     : https://prove2.me/theorems/bd497188-98a5-4cbf-852c-bd8fd8ab08f0
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part4
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iterations_steps_le_mul
    (entries : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesOuterIterationsSteps entries ≤
      entries.length *
        (70 * ((encodeIndexedOccurrenceEntries entries).length + 1) ^ 2) := by
  induction entries with
  | nil => simp [compatibilityEdgesOuterIterationsSteps]
  | cons current priors ih =>
      have hfirst := outer_iteration_steps_le current priors
      have hencoding :
          (encodeIndexedOccurrenceEntries priors).length ≤
            (encodeIndexedOccurrenceEntries (current :: priors)).length := by
        simp [encodeIndexedOccurrenceEntries]
      have hpow :
          ((encodeIndexedOccurrenceEntries priors).length + 1) ^ 2 ≤
            ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.add_le_add_right hencoding 1) 2
      have hrest : compatibilityEdgesOuterIterationsSteps priors ≤
          priors.length *
            (70 * ((encodeIndexedOccurrenceEntries
              (current :: priors)).length + 1) ^ 2) :=
        ih.trans (Nat.mul_le_mul_left priors.length
          (Nat.mul_le_mul_left 70 hpow))
      simp only [compatibilityEdgesOuterIterationsSteps, List.length_cons]
      nlinarith
end CLRS.Chapter34.Turing.TMClique


