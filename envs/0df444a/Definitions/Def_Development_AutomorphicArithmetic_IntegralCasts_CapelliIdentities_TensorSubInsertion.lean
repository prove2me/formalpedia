-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TensorSubInsertion
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TensorSubInsertion
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T07:08:51.837826+00:00
-- url     : https://prove2.me/theorems/12fdd00f-8fce-5e4d-8b2c-e2da1f2f2c67
-- title:
--   Tensor Sub Insertion
-- statement:
--   Definitions and structural lemmas for Tensor Sub Insertion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TensorSubInsertion.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StCutRestrLenExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.SlopeTestRemainingChoices
open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial Filter
noncomputable section
universe u w
section Tensor
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem twist_sub_eq_mul (A B : SubSystem S x Ω) (I : Chart x) :
    (A.twist B).sub I = A.sub I * B.sub I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [smul_eq_mul, mul_comm q y]
    exact Submodule.mul_mem_mul hy hq
  · refine Submodule.mul_le.mpr fun y hy q hq => ?_
    exact Submodule.subset_span ⟨q, hq, y, hy, by rw [smul_eq_mul, mul_comm]⟩
theorem mem_of_unit {F : SubSystem S x Ω} {I J : Chart x} (h : I.1 ⊆ J.1)
    (a : chartRing S x I) (ha : IsUnit (chartIncl h a)) {y : Ω} (hay : (a : Ω) • y ∈ F.sub I) :
    y ∈ F.sub J := by
  obtain ⟨u, hu⟩ := ha
  have hJ := F.mono I J h _ hay
  have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
    have := congrArg Subtype.val (Units.inv_mul u)
    rw [hu] at this
    exact this
  have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
    rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
  rw [hy]
  exact Submodule.smul_mem _ _ hJ
theorem tens_mem (A B : LineBundle S x) (I J : Chart x) (h : I.1 ⊆ J.1) (y : Ω)
    (hy : y ∈ (A.toSubSystem.twist B.toSubSystem).sub J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
      (a : Ω) • y ∈ (A.toSubSystem.twist B.toSubSystem).sub I := by
  refine Submodule.span_induction (p := fun y _ => ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
      (a : Ω) • y ∈ (A.toSubSystem.twist B.toSubSystem).sub I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨q, hq, z, hz, rfl⟩
    obtain ⟨a₁, h₁, hq₁⟩ := (B.mem_iff I J h q).mp hq
    obtain ⟨a₂, h₂, hz₂⟩ := (A.mem_iff I J h z).mp hz
    refine ⟨a₁ * a₂, by rw [map_mul]; exact h₁.mul h₂, ?_⟩
    refine Submodule.subset_span ⟨_, hq₁, _, hz₂, ?_⟩
    simp only [smul_eq_mul, Subalgebra.coe_mul]
    ring
  · exact ⟨1, by simp, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro y₁ y₂ _ _ ⟨a₁, h₁, hy₁⟩ ⟨a₂, h₂, hy₂⟩
    refine ⟨a₁ * a₂, by rw [map_mul]; exact h₁.mul h₂, ?_⟩
    have e : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
        a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
      simp only [chartRing_smul_def, smul_eq_mul, Subalgebra.coe_mul]
      ring
    rw [e]
    exact add_mem (Submodule.smul_mem _ _ hy₁) (Submodule.smul_mem _ _ hy₂)
  · rintro b z _ ⟨a₂, h₂, hz⟩
    obtain ⟨a₁, h₁, hb⟩ := exists_isUnit_mul_mem h b
    refine ⟨a₁ * a₂, by rw [map_mul]; exact h₁.mul h₂, ?_⟩
    have e : ((a₁ * a₂ : chartRing S x I) : Ω) • (b • z) =
        (⟨_, hb⟩ : chartRing S x I) • ((a₂ : Ω) • z) := by
      simp only [chartRing_smul_def, smul_eq_mul, Subalgebra.coe_mul]
      ring
    rw [e]
    exact Submodule.smul_mem _ _ hz
def tens (A B : LineBundle S x) : LineBundle S x :=
  { A.toSubSystem.twist B.toSubSystem with
    mem_iff := fun I J h y =>
      ⟨tens_mem A B I J h y, fun ⟨a, ha, hay⟩ => mem_of_unit h a ha hay⟩
    fg := fun I => by
      change ((A.toSubSystem.twist B.toSubSystem).sub I).FG
      rw [twist_sub_eq_mul]
      exact (A.fg I).mul (B.fg I)
    invertible := fun I => by
      obtain ⟨A', hA⟩ := A.invertible I
      obtain ⟨B', hB⟩ := B.invertible I
      refine ⟨A' * B', ?_⟩
      change (A.toSubSystem.twist B.toSubSystem).sub I * _ = 1
      rw [twist_sub_eq_mul, mul_mul_mul_comm]
      change A.sub I * A' * (B.sub I * B') = 1
      rw [hA, hB, one_mul] }
end Tensor
section Form
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
end Form
section Mixed
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
end Mixed
section Final
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
end Final
end
end UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.SlopeTestRemainingChoices


