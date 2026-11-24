-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:35.408098+00:00
-- url     : https://prove2.me/theorems/74ffe56a-23a1-4867-8e43-6cbe53b44fb4
-- title:
--   POrbit Conj Sum Lemmas
-- statement:
--   Definitions and structural lemmas for POrbit Conj Sum Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitConjSumLemmas.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
namespace OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
theorem map_aeval_int {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {κ : Type*}
    (w : κ → A) (f : MvPolynomial κ ℤ) : φ (aeval w f) = aeval (fun p ↦ φ (w p)) f := by
  rw [aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _
theorem eval_map_int {κ : Type*} (z : κ → ℂ) (f : MvPolynomial κ ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]
omit [Fintype ι] [DecidableEq ι] in

theorem aeval_eq_zero_of_mem (x : Cone n (AlgebraicClosure ℚ)) {f : MvPolynomial (Coord n) ℤ}
    (hmem : f ∈ orbitIdeal x) : aeval (flatCone x) f = 0 := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at hmem
  have h : ∀ f : MvPolynomial (Coord n) ℤ, aeval (flatCone x) f =
      eval (fun _ : ι ↦ (1 : AlgebraicClosure ℚ))
        (Geo.mConeMap (ι := blockIdx n) (flatCone x) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f p hf => simp only [map_mul, hf, aeval_X, eval_X, Geo.mConeMap, eval_C, mul_one]
  rw [h, hmem, map_zero]
omit [Fintype ι] [DecidableEq ι] in

theorem conj_mem (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (σ : coordField x →+* ℂ) :
    (fun p : Coord n ↦ σ (coordVec x p.1 p.2)) ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x) := by
  refine ⟨fun k ↦ ?_, fun f hf ↦ ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
    exact ⟨i, (map_ne_zero σ).mpr fun h ↦ hi (congrArg Subtype.val h)⟩
  · have h0 : aeval (fun p : Coord n ↦ coordVec x p.1 p.2) f = 0 := by
      apply Subtype.val_injective
      have := map_aeval_int (coordField x).val.toRingHom (fun p : Coord n ↦ coordVec x p.1 p.2) f
      exact this.trans (aeval_eq_zero_of_mem x hf)
    rw [eval_map_int, ← map_aeval_int σ]
    exact (congrArg σ h0).trans (map_zero σ)
def chartHomog (c : (k : ι) → Fin (n k + 1)) (P : MvPolynomial (Coord n) ℤ) :
    MvPolynomial (Coord n) ℤ :=
  ∑ m ∈ P.support, monomial m (P.coeff m) * chartMonomial c (fun k ↦ P.totalDegree - ∑ i, m ⟨k, i⟩)
def ratio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) (p : Coord n) :
    coordField x :=
  coordVec x p.1 p.2 / coordVec x p.1 (c p.1)
def ratioField (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    IntermediateField ℚ (coordField x) :=
  IntermediateField.adjoin ℚ (Set.range (ratio x c))
instance (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    NumberField (ratioField x c) := {}
instance (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    FiniteDimensional (ratioField x c) (coordField x) :=
  FiniteDimensional.right ℚ (ratioField x c) (coordField x)
def conjPt (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x) (σ : coordField x →+* ℂ) :
    projPts (ι := blockIdx n) (orbitIdeal x) :=
  Quot.mk _ ⟨_, conj_mem x hx σ⟩
end OrbitConjSum
end
end GroundTheory.Heights₂.Heights


