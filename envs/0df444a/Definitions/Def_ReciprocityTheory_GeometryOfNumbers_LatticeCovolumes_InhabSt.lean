-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
-- name    : ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:01.021367+00:00
-- url     : https://prove2.me/theorems/8094cefe-8a3b-4aa7-b464-3eb86d1b6d70
-- title:
--   Inhab St
-- statement:
--   Definitions and structural lemmas for Inhab St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/InhabSt.lean

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable (K : Type*) [Field K] [NumberField K]
theorem standardHermitian_gram_posDef (σ : K →+* ℂ) {m n : ℕ} (v : Fin n → Fin m → K)
    (hv : LinearIndependent K v) :
    (Matrix.of fun i j => ∑ k, starRingEnd ℂ (σ (v i k)) * σ (v j k)).PosDef := by
  classical

  let Vt : Matrix (Fin m) (Fin n) K := Matrix.of fun k j => v j k
  let B : Matrix (Fin m) (Fin n) ℂ := Vt.map σ
  have hker : LinearMap.ker (Matrix.toLin' Vt) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have h0 : ∑ j, g j • v j = 0 := by
      ext k
      have := congrFun hg k
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Vt, Matrix.of_apply,
        Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    funext j
    exact Fintype.linearIndependent_iff.1 hv g h0 j
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hW : LinearMap.toMatrix' g * Vt = 1 := by
    rw [← LinearMap.toMatrix'_toLin' Vt, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hB : (LinearMap.toMatrix' g).map σ * B = 1 := by
    simp only [B]
    rw [← Matrix.map_mul, hW, Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hinj : Function.Injective B.mulVec := by
    intro x y hxy
    have := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
    simp only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] at this
    exact this
  convert Matrix.PosDef.conjTranspose_mul_self B hinj using 1
  ext i j
  simp [Matrix.mul_apply, B, Vt]
def stdHerm (m : ℕ) : HermFam K (Fin m → K) where
  form σ x y := ∑ k, starRingEnd ℂ (σ (x k)) * σ (y k)
  add_right σ x y z := by
    simp [mul_add, Finset.sum_add_distrib]
  smul_right σ a x y := by
    simp [Finset.mul_sum, mul_left_comm]
  conj_symm σ x y := by
    simp [mul_comm]
  posDef σ n v hv := standardHermitian_gram_posDef K σ v hv
def stdLat (m : ℕ) : Submodule (𝓞 K) (Fin m → K) :=
  Submodule.span (𝓞 K) (Set.range fun i : Fin m => (Pi.single i 1 : Fin m → K))
end ReciprocityTheory.GeometryOfNumbersTheory


