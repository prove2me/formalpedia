-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:12:23.146925+00:00
-- url     : https://prove2.me/theorems/49ac9339-bbec-54ef-aae4-9a640ac81a38
-- title:
--   Twist Bundle To Sub System
-- statement:
--   Definitions and structural lemmas for Twist Bundle To Sub System, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
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
universe u w
section Twist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem SubSystem.twist_sub_eq_mul_sub (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩
def LineBundle.tensor (L L' : LineBundle S x) : LineBundle S x where
  toSubSystem := L.toSubSystem.twist L'.toSubSystem
  mem_iff I J h y := by
    constructor
    · intro hy
      refine Submodule.span_induction (p := fun y _ => ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
        (a : Ω) • y ∈ (L.toSubSystem.twist L'.toSubSystem).sub I) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨q, hq, z, hz, rfl⟩
        obtain ⟨a, ha, haq⟩ := (L'.mem_iff I J h q).mp hq
        obtain ⟨b, hb, hbz⟩ := (L.mem_iff I J h z).mp hz
        refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
        refine Submodule.subset_span ⟨(a : Ω) • q, haq, (b : Ω) • z, hbz, ?_⟩
        simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
      · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
      · rintro y₁ y₂ - - ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
        have : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
            a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
          simp only [smul_eq_mul, chartRing_smul_def, Subalgebra.coe_mul]; ring
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
      · rintro c y - ⟨a, ha, hay⟩
        obtain ⟨d, hd, hdc⟩ := exists_isUnit_mul_mem h c
        refine ⟨d * a, by rw [map_mul]; exact hd.mul ha, ?_⟩
        have : ((d * a : chartRing S x I) : Ω) • (c • y) =
            (⟨_, hdc⟩ : chartRing S x I) • ((a : Ω) • y) := by
          simp only [smul_eq_mul, chartRing_smul_def, Subalgebra.coe_mul]; ring
        rw [this]
        exact Submodule.smul_mem _ _ hay
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ := (L.toSubSystem.twist L'.toSubSystem).mono I J h _ hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ
  fg I := by
    rw [SubSystem.twist_sub_eq_mul_sub]
    exact (L'.fg I).mul (L.fg I)
  invertible I := by
    obtain ⟨P, hP⟩ := L.invertible I
    obtain ⟨P', hP'⟩ := L'.invertible I
    refine ⟨P' * P, ?_⟩
    rw [SubSystem.twist_sub_eq_mul_sub, mul_mul_mul_comm, hP', hP, one_mul]
def LineBundle.tpow (L : LineBundle S x) : ℕ → LineBundle S x
  | 0 => twistBundle S x 0
  | n + 1 => (L.tpow n).tensor L
end Twist
section Section
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
end Section
section Dim
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
end Dim
end
end GroundTheory.Heights₂.Heights.Kleiman


