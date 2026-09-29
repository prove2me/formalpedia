-- Prove2me | solution 1 for AlgebraicCurve.Divisor.degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/49b9107c-86a8-5a89-8dad-1bd287af928f

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one

set_option autoImplicit false

open AlgebraicCurve

namespace FibreDegree

def tmass {X : Type*} (D : X →₀ ℤ) : ℤ := D.sum fun _ m => m

theorem tmass_add {X : Type*} (D₁ D₂ : X →₀ ℤ) : tmass (D₁ + D₂) = tmass D₁ + tmass D₂ :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem tmass_mapDomain {X Y : Type*} (r : X → Y) (D : X →₀ ℤ) :
    tmass (Finsupp.mapDomain r D) = tmass D :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem degree_eq_tmass {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    (h : ∀ v : Place K₀ F₀, v.deg = 1) (D : Divisor K₀ F₀) : D.degree = tmass D := by
  induction D using Finsupp.induction_linear with
  | zero =>
    unfold tmass
    rw [map_zero, Finsupp.sum_zero_index]
  | add f g hf hg => rw [map_add, tmass_add, hf, hg]
  | single v n =>
    unfold tmass
    rw [Divisor.degree_single, h v, Nat.cast_one, mul_one, Finsupp.sum_single_index rfl]

end FibreDegree

theorem solution
    {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F'] [Algebra K' F']
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K' F', w.deg = 1)
    (r₁ r₂ : Place K F → Place K' F') (p₁ p₂ : Place K F → Prop) [DecidablePred p₁] [DecidablePred p₂]
    (hdisj : ∀ V, p₁ V → ¬ p₂ V)
    (E : Divisor K F) (hE : ∀ V ∈ E.support, p₁ V ∨ p₂ V) :
    Divisor.degree (Finsupp.mapDomain r₁ (E.filter p₁)) + Divisor.degree (Finsupp.mapDomain r₂ (E.filter p₂)) = E.degree := by
  classical
  rw [FibreDegree.degree_eq_tmass hdeg', FibreDegree.degree_eq_tmass hdeg', FibreDegree.degree_eq_tmass hdeg,
    FibreDegree.tmass_mapDomain, FibreDegree.tmass_mapDomain, ← FibreDegree.tmass_add]
  congr 1
  ext V
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.filter_apply]
  by_cases hV : E V = 0
  · simp [hV]
  · rcases hE V (Finsupp.mem_support_iff.mpr hV) with h | h
    · rw [if_pos h, if_neg (hdisj V h), add_zero]
    · rw [if_neg (fun h' => hdisj V h' h), if_pos h, zero_add]

end S_AlgebraicCurve_Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one (solution)
