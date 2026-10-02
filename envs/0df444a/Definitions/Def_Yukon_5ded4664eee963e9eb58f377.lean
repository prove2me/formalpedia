-- Prove2me | Definitions.Def_Yukon_5ded4664eee963e9eb58f377
-- name    : Yukon_5ded4664eee963e9eb58f377
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T10:37:49.098761+00:00
-- url     : https://prove2.me/theorems/335f0a23-c91c-416b-9e18-1e0f792396e0
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WeightedZeroMass6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WeightedZeroMass6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WeightedZeroMass6807.lean
--
--   yukon-proof-operation:foundation-direct-b265277b906583aeee3eb39c372955d8724ad65d68466e7236957cbfa8ff296d-parser-retry
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZWYzOTMzOTA0N2VlOWU4ZDgxN2UwNWZkOWFkZmI1Mzk2YTVlYmJhNmE4MzZkNTg4ZjFmOTkyZWRhYzVlODg1ZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWIyNjUyNzdiOTA2NTgzYWVlZTNlYjM5YzM3Mjk1NWQ4NzI0YWQ2NWQ2ODQ2NmU3MjM2OTU3Y2JmYThmZjI5NmQtcGFyc2VyLXJldHJ5IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fNWRlZDQ2NjRlZWU5NjNlOWViNThmMzc3IiwidiI6Mn0]

/-
UNCOMPILED. Weighted zero/pole counting at the pinned actual model places.
The multiplicity sum is retained throughout. The product formula is applied to
a nonzero rational function, and all of its finite and infinite places remain.
-/
import Definitions.Def_Yukon_7ac04eb8d9104a96b1b2bba0












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.WeightedZeroMass6807
open scoped Classical BigOperators WithZero
open RCN026
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

/-- An injective indexed family of places pays its actual positive weights.
The positivity premise is used only to put those places into placesFor. -/
theorem weighted_places_le_poleMass {I : Type*} [Fintype I]
    (x : L) (hx : x ≠ 0) (place : I → Place K L)
    (hinj : Function.Injective place) (mu : I → ℕ)
    (hmu : ∀ i, 1 ≤ mu i)
    (horder : ∀ i, (mu i : ℤ) ≤ order K L (place i) x) :
    (∑ i, (mu i : ℤ)) ≤
      ∑ v ∈ placesFor K L x hx, RCN346.poleOrder K L v x := by
  classical
  let U : Finset (Place K L) := Finset.univ.image place
  have hsub : U ⊆ placesFor K L x hx := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    apply placesFor_covers K L x hx (place i)
    have hi := horder i
    have hm : (1 : ℤ) ≤ (mu i : ℤ) := by exact_mod_cast hmu i
    omega
  calc
    (∑ i, (mu i : ℤ)) ≤ ∑ i, zeroOrder K L (place i) x := by
      apply Finset.sum_le_sum
      intro i _
      exact (horder i).trans (le_max_right _ _)
    _ = ∑ v ∈ U, zeroOrder K L v x := by
      dsimp only [U]
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    _ ≤ ∑ v ∈ placesFor K L x hx, zeroOrder K L v x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro v _ _
      exact zeroOrder_nonneg K L v x
    _ = _ := sum_placesFor_zero_eq_pole K L x hx

section Affine
variable (A : Type*) [CommRing A] [IsDomain A]
  [Algebra K A] [Algebra A L] [IsFractionRing A L]
  [Algebra (Polynomial K) A]
  [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
  [IsScalarTower (Polynomial K) A L]

/-- Fully concrete affine-model version. The only point data are distinct
K-algebra evaluations, their ideal-power memberships, and nonzero denominators. -/
theorem weighted_affine_points_le_poleMass {I : Type*} [Fintype I]
    (phi : I → (A →ₐ[K] K)) (hinj : Function.Injective phi)
    (mu : I → ℕ) (hmu : ∀ i, 1 ≤ mu i) (a b : A)
    (ha : ∀ i, a ∈ (RingHom.ker (phi i).toRingHom)^(mu i))
    (hb : ∀ i, phi i b ≠ 0)
    (hx : algebraMap A L a / algebraMap A L b ≠ 0) :
    (∑ i, (mu i : ℤ)) ≤
      ∑ v ∈ placesFor K L (algebraMap A L a / algebraMap A L b) hx,
        RCN346.poleOrder K L v (algebraMap A L a / algebraMap A L b) := by
  apply weighted_places_le_poleMass K L _ hx
    (fun i => RCN344.modelPlace K L A (phi i))
    ((RCN344.modelPlace_injective K L A).comp hinj) mu hmu
  intro i
  exact WeightedPlaceOrder6807.actual_normalized_order_ge_pow K A L
    (phi i) (mu i) a b (ha i) (hb i) hx

/-- Useful final interface for one slice component: a local rational pole
bound, not a global intersection bound, pays all embedded old multiplicities. -/
theorem weighted_affine_points_scaled {I : Type*} [Fintype I]
    (phi : I → (A →ₐ[K] K)) (hinj : Function.Injective phi)
    (mu : I → ℕ) (hmu : ∀ i, 1 ≤ mu i) (a b : A)
    (ha : ∀ i, a ∈ (RingHom.ker (phi i).toRingHom)^(mu i))
    (hb : ∀ i, phi i b ≠ 0)
    (hx : algebraMap A L a / algebraMap A L b ≠ 0)
    (d cost : ℕ)
    (hpole : ∀ W : Finset (Place K L),
      (d : ℤ) * (∑ v ∈ W,
        RCN346.poleOrder K L v (algebraMap A L a / algebraMap A L b)) ≤ cost) :
    d * (∑ i, mu i) ≤ cost := by
  have hm := weighted_affine_points_le_poleMass K L A phi hinj mu hmu a b ha hb hx
  have hs := (mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg d)).trans
    (hpole (placesFor K L _ hx))
  exact_mod_cast hs

end Affine
end
end ProximityPrize.SubmissionLower.WeightedZeroMass6807


