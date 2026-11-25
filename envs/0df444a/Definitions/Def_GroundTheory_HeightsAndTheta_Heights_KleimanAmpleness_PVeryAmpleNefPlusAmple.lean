-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:32:51.771082+00:00
-- url     : https://prove2.me/theorems/5a8b3a31-a3e9-4774-b60a-e032cb62b9d5
-- title:
--   PVery Ample Nef Plus Ample
-- statement:
--   Definitions and structural lemmas for PVery Ample Nef Plus Ample, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
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
section Algebra
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem KThm.sub_twist (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩
def KThm.lbTwist (F Q : LineBundle S x) : LineBundle S x :=
  { F.toSubSystem.twist Q.toSubSystem with
    mem_iff := fun I J h y => by
      constructor
      · intro hy
        change y ∈ Submodule.span _ {z | ∃ q ∈ Q.sub J, ∃ y ∈ F.sub J, z = q • y} at hy
        induction hy using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨q, hq, f, hf, rfl⟩ := hz
          obtain ⟨a, ha, haf⟩ := (F.mem_iff I J h f).mp hf
          obtain ⟨b, hb, hbq⟩ := (Q.mem_iff I J h q).mp hq
          refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
          have e : ((a * b : chartRing S x I) : Ω) • (q • f) = ((b : Ω) • q) • ((a : Ω) • f) := by
            simp only [smul_eq_mul, Subalgebra.coe_mul]; ring_nf
          rw [e]
          exact Submodule.subset_span ⟨_, hbq, _, haf, rfl⟩
        | zero => exact ⟨1, by simp, by simp⟩
        | add y₁ y₂ _ _ h₁ h₂ =>
          obtain ⟨a, ha, h1⟩ := h₁
          obtain ⟨b, hb, h2⟩ := h₂
          refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
          have e : ((a * b : chartRing S x I) : Ω) • (y₁ + y₂) = b • ((a : Ω) • y₁) + a • ((b : Ω) • y₂) := by
            simp only [smul_eq_mul, chartRing_smul_def, Subalgebra.coe_mul]; ring_nf
          rw [e]
          exact Submodule.add_mem _ (Submodule.smul_mem _ b h1) (Submodule.smul_mem _ a h2)
        | smul c y _ hy =>
          obtain ⟨a, ha, hay⟩ := hy
          obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem h c
          refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
          have e : ((a' * a : chartRing S x I) : Ω) • (c • y) =
              (⟨(a' : Ω) * c, hc⟩ : chartRing S x I) • ((a : Ω) • y) := by
            simp only [smul_eq_mul, chartRing_smul_def, Subalgebra.coe_mul]; ring_nf
          rw [e]
          exact Submodule.smul_mem _ _ hay
      · rintro ⟨a, ⟨u, hu⟩, hay⟩
        have hJ := (F.toSubSystem.twist Q.toSubSystem).mono I J h _ hay
        have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
          have := congrArg Subtype.val (Units.inv_mul u)
          rw [hu] at this
          exact this
        have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
          rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
        rw [hy]
        exact Submodule.smul_mem _ _ hJ
    fg := fun I => by
      rw [KThm.sub_twist]
      exact (Q.fg I).mul (F.fg I)
    invertible := fun I => by
      obtain ⟨F', hF'⟩ := F.invertible I
      obtain ⟨Q', hQ'⟩ := Q.invertible I
      refine ⟨Q' * F', ?_⟩
      change (F.toSubSystem.twist Q.toSubSystem).sub I * _ = 1
      rw [KThm.sub_twist, mul_mul_mul_comm]
      change Q.sub I * Q' * (F.sub I * F') = 1
      rw [hF', hQ', one_mul] }
def KThm.lbPow (Q : LineBundle S x) : ℕ → LineBundle S x
  | 0 => twistBundle S x 0
  | n + 1 => KThm.lbTwist (KThm.lbPow Q n) Q
end Algebra
section Upward
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
end Upward
end
end GroundTheory.Heights₂.Heights.Kleiman


