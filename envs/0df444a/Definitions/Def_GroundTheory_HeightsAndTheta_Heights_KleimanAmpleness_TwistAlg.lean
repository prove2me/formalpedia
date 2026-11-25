-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:52:24.776474+00:00
-- url     : https://prove2.me/theorems/249eb845-da61-5005-a138-65f94a11a9f5
-- title:
--   Twist Alg
-- statement:
--   Definitions and structural lemmas for Twist Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace SubSystem
theorem twist_sub_eq_mul_of_line (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact Set.mul_mem_mul hq hy
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨q, hq, y, hy, rfl⟩
end SubSystem
namespace LineBundle
def tensorProd (P Q : LineBundle S x) : LineBundle S x where
  toSubSystem := P.toSubSystem.twist Q.toSubSystem
  mem_iff I J h y := by
    constructor
    · intro hy
      have hy' : y ∈ Submodule.span (chartRing S x J)
          {z | ∃ q ∈ Q.sub J, ∃ p ∈ P.sub J, z = q • p} := hy
      refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I,
        IsUnit (chartIncl h a) ∧ (a : Ω) • z ∈ (P.toSubSystem.twist Q.toSubSystem).sub I)
        ?_ ?_ ?_ ?_ hy'
      · rintro _ ⟨q, hq, p, hp, rfl⟩
        obtain ⟨a, ha, haq⟩ := (Q.mem_iff I J h q).mp hq
        obtain ⟨b, hb, hbp⟩ := (P.mem_iff I J h p).mp hp
        refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
        have : ((a * b : chartRing S x I) : Ω) • (q • p) = ((a : Ω) • q) • ((b : Ω) • p) := by
          simp only [smul_eq_mul, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.subset_span ⟨_, haq, _, hbp, rfl⟩
      · exact ⟨1, by simp, by simp⟩
      · rintro y₁ y₂ - - ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
        have : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
            a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
          simp only [smul_eq_mul, chartRing_smul_def, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
      · rintro c z - ⟨a, ha, hz⟩
        obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem h c
        refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
        have : ((a' * a : chartRing S x I) : Ω) • (c • z) =
            (⟨_, hc⟩ : chartRing S x I) • ((a : Ω) • z) := by
          simp only [smul_eq_mul, chartRing_smul_def, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.smul_mem _ _ hz
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ := (P.toSubSystem.twist Q.toSubSystem).mono I J h _ hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ
  fg I := by
    rw [SubSystem.twist_sub_eq_mul_of_line]
    exact (Q.fg I).mul (P.fg I)
  invertible I := by
    obtain ⟨P', hP⟩ := P.invertible I
    obtain ⟨Q', hQ⟩ := Q.invertible I
    refine ⟨P' * Q', ?_⟩
    rw [SubSystem.twist_sub_eq_mul_of_line,
      show Q.sub I * P.sub I * (P' * Q') = (P.sub I * P') * (Q.sub I * Q') by ring, hP, hQ, one_mul]
def powBundle (Q : LineBundle S x) : ℕ → LineBundle S x
  | 0 => twistBundle S x 0
  | n + 1 => (Q.powBundle n).tensorProd Q
end LineBundle
end
end GroundTheory.Heights₂.Heights.Kleiman


