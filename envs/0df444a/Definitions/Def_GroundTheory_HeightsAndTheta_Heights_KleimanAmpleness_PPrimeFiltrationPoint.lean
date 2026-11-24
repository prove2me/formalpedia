-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:13.981424+00:00
-- url     : https://prove2.me/theorems/aed1effe-c3a0-4b6b-9af9-1b31d8ec3514
-- title:
--   PPrime Filtration Point
-- statement:
--   Definitions and structural lemmas for PPrime Filtration Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
section PointLemmas
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}
variable (x) in

def chartPrimeIdeal (hj : x j ≠ 0) (pp : Ideal (Poly S N)) :
    Ideal (chartRing S x (singleChart hj)) where
  carrier := {a | ∃ (f s : Poly S N) (e : ℕ), f ∈ pp ∧ s ∈ monos {j} ∧ f.IsHomogeneous e ∧
    s.IsHomogeneous e ∧ (a : Ω) = aeval x f / aeval x s}
  zero_mem' := ⟨0, 1, 0, pp.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _,
    by simp⟩
  add_mem' := by
    rintro a b ⟨f, s, e, hf, hs, hfe, hse, ha⟩ ⟨g, t, d, hg, ht, hgd, htd, hb⟩
    refine ⟨f * t + s * g, s * t, e + d, pp.add_mem (pp.mul_mem_right t hf) (pp.mul_mem_left s hg),
      mul_mem hs ht, (hfe.mul htd).add (hse.mul hgd), hse.mul htd, ?_⟩
    rw [Subalgebra.coe_add, ha, hb, div_add_div _ _ (eval_ne_zero_of_mem_monos (singleChart hj) hs)
      (eval_ne_zero_of_mem_monos (singleChart hj) ht)]
    simp only [map_add, map_mul]
  smul_mem' := by
    rintro c a ⟨g, t, d, hg, ht, hgd, htd, ha⟩
    obtain ⟨f, s, e, hs, hfe, hse, hc⟩ := c.2
    refine ⟨f * g, s * t, e + d, pp.mul_mem_left f hg, mul_mem hs ht, hfe.mul hgd, hse.mul htd, ?_⟩
    change (c : Ω) * (a : Ω) = _
    rw [hc, ha, map_mul, map_mul, div_mul_div_comm]
end PointLemmas
end
end GroundTheory.Heights₂.Heights.Kleiman


