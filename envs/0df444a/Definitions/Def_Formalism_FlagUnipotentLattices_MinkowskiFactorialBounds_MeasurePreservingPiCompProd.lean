-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:55.370111+00:00
-- url     : https://prove2.me/theorems/3e36e4a3-a263-4ecd-a1f9-71b8645089f7
-- title:
--   Measure Preserving Pi Comp Prod
-- statement:
--   Definitions and structural lemmas for Measure Preserving Pi Comp Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLatticeCounting.P
section homRestrict
open Module
variable {O : Type} [CommRing O] [IsDedekindDomain O]
end homRestrict
section hermConj
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
section herm
variable {F K : Type} [Field F] [CommRing K] [StarRing K] [Algebra F K]
lemma s5b7_conj_mem {n : Type} [Fintype n] [DecidableEq n]
    (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c) (g : Matrix n n K) :
    ∀ A ∈ hermSub F K n hF, conjMap F g A ∈ hermSub F K n hF := by
  intro A hA
  have hA' : Aᴴ = A := hA
  change (g * (A * gᴴ))ᴴ = g * (A * gᴴ)
  simp [Matrix.conjTranspose_mul, hA', Matrix.mul_assoc]
noncomputable def congruenceRestrict {n : Type} [Fintype n] [DecidableEq n]
    (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c) (g : Matrix n n K) :
    hermSub F K n hF →ₗ[F] hermSub F K n hF :=
  (conjMap F g).restrict (s5b7_conj_mem hF g)
def s5b7_Q {n : Type} [Fintype n] [DecidableEq n]
    (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c) (g : Matrix n n K) : Prop :=
  algebraMap F K (LinearMap.det (congruenceRestrict hF g)) = (g.det * star g.det) ^ Fintype.card n
variable {n : Type} [Fintype n] [DecidableEq n]
noncomputable def borderedHermitian (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c) :
    (hermSub F K n hF × (n → K) × F) →ₗ[F] Matrix (n ⊕ Unit) (n ⊕ Unit) K where
  toFun x := fromBlocks (x.1 : Matrix n n K) (replicateCol Unit x.2.1)
    (replicateRow Unit (star x.2.1)) (Matrix.of fun _ _ => algebraMap F K x.2.2)
  map_add' x y := by
    ext (i | i) (j | j) <;> simp
  map_smul' c x := by
    ext (i | i) (j | j)
    · simp
    · simp
    · simp [Algebra.smul_def, hF]
    · simp [Algebra.smul_def]
lemma borderedHermitian_apply (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c)
    (x : hermSub F K n hF × (n → K) × F) :
    borderedHermitian hF x = fromBlocks (x.1 : Matrix n n K) (replicateCol Unit x.2.1)
    (replicateRow Unit (star x.2.1)) (Matrix.of fun _ _ => algebraMap F K x.2.2) := rfl
lemma borderedHermitian_mem (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c)
    (x : hermSub F K n hF × (n → K) × F) : borderedHermitian hF x ∈ hermSub F K (n ⊕ Unit) hF := by
  have h1 : (x.1 : Matrix n n K)ᴴ = x.1 := x.1.2
  change (borderedHermitian hF x)ᴴ = borderedHermitian hF x
  rw [borderedHermitian_apply, fromBlocks_conjTranspose, h1]
  rw [fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [conjTranspose_replicateRow]
  · simp [conjTranspose_replicateCol]
  · ext i j
    simp [hF]
noncomputable def s5b7_Psi (hF : ∀ c : F, star (algebraMap F K c) = algebraMap F K c)
    (hfix : ∀ x : K, star x = x → x ∈ Set.range (algebraMap F K)) [Nontrivial K] :
    (hermSub F K n hF × (n → K) × F) ≃ₗ[F] hermSub F K (n ⊕ Unit) hF :=
  LinearEquiv.ofBijective ((borderedHermitian hF).codRestrict _ (borderedHermitian_mem hF)) (by
    constructor
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      change borderedHermitian hF x = borderedHermitian hF y at h
      rw [borderedHermitian_apply, borderedHermitian_apply, fromBlocks_inj] at h
      obtain ⟨h1, h2, -, h4⟩ := h
      have h2' : x.2.1 = y.2.1 := by
        funext i
        simpa using congrFun (congrFun h2 i) ()
      have h4' : x.2.2 = y.2.2 := by
        have := congrFun (congrFun h4 ()) ()
        exact (algebraMap F K).injective this
      exact Prod.ext (Subtype.ext h1) (Prod.ext h2' h4')
    · rintro ⟨X, hX⟩
      have hX' : Xᴴ = X := hX
      rw [← fromBlocks_toBlocks X, fromBlocks_conjTranspose, fromBlocks_inj] at hX'
      obtain ⟨h1, h2, h3, h4⟩ := hX'
      obtain ⟨f, hf⟩ := hfix (X.toBlocks₂₂ () ()) (by
        simpa using congrFun (congrFun h4 ()) ())
      refine ⟨(⟨X.toBlocks₁₁, h1⟩, fun i => X.toBlocks₁₂ i (), f), ?_⟩
      apply Subtype.ext
      change borderedHermitian hF _ = X
      rw [borderedHermitian_apply]
      conv_rhs => rw [← fromBlocks_toBlocks X]
      rw [fromBlocks_inj]
      refine ⟨rfl, ?_, ?_, ?_⟩
      · ext i j
        rfl
      · rw [← h3]
        ext i j
        rfl
      · ext i j
        exact hf)
end herm
end hermConj
section volume
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
def s5b7_A (R : ℝ) (d r : ℕ) (t : ℝ) : Set (Fin r → EuclideanSpace ℂ (Fin d)) :=
  {a | (∀ b, ‖a b‖ ≤ R) ∧ Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ t}
end volume
end Formalism.HermitianLatticeCounting.P


