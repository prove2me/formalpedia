-- Prove2me | solution 1 for AlgebraicGeometry.GrpObj.isogeny_degree_eq_natCard_ker_mul_finInsepDegree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T15:01:42.878267+00:00
-- url     : https://prove2.me/submissions/887df01a-28e8-45fb-abe5-c67588742353

import Mathlib
import Definitions.Def_RPLib_F2_018

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj

namespace UploadIsogDegSW34

open RamanujanPetersson.IsogDegA

/-- `deg = sepdeg * insepdeg` for a dominant morphism of integral schemes. -/
theorem degDom_eq_sep_mul_insep {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] :
    letI := ffAlgebra f
    degDom f = Field.finSepDegree Y.functionField X.functionField *
      Field.finInsepDegree Y.functionField X.functionField := by
  letI := ffAlgebra f
  rw [Field.finSepDegree_mul_finInsepDegree]
  rfl

/-- The inseparable degree of a finite function-field extension is a power of the exponential
characteristic. -/
theorem finInsepDegree_ffAlgebra_eq_pow {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] [IsDominant f] (q : ℕ) [ExpChar Y.functionField q] :
    letI := ffAlgebra f
    FiniteDimensional Y.functionField X.functionField →
      ∃ n, Field.finInsepDegree Y.functionField X.functionField = q ^ n := by
  letI := ffAlgebra f
  intro _
  exact _root_.finInsepDegree_eq_pow _ _ q

end UploadIsogDegSW34

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [IsIntegral A.left]
    (ff : (A ⟶ A) → (A.left.functionField →+* A.left.functionField))
    (hff : ∀ (ψ : A ⟶ A) (h : ψ.left (genericPoint A.left) = genericPoint A.left),
      ff ψ = (A.left.presheaf.stalkSpecializes (specializes_of_eq h) ≫
        ψ.left.stalkMap (genericPoint A.left)).hom)
    (deg : (A ⟶ A) → ℕ)
    (hdeg : ∀ ψ : A ⟶ A, ψ.left (genericPoint A.left) = genericPoint A.left →
      deg ψ = @Module.finrank _ _ _ _ (ff ψ).toAlgebra.toModule)
    (hdeg0 : ∀ ψ : A ⟶ A, ψ.left (genericPoint A.left) ≠ genericPoint A.left → deg ψ = 0)
    (φ : A ⟶ A) [IsMonHom φ] :
    (IsDominant φ.left ↔ Finite {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1}) ∧
    (deg φ = 0 ↔ ¬ IsDominant φ.left) ∧
    (∀ (ψ : A ⟶ A) [IsMonHom ψ], deg (ψ ≫ φ) = deg φ * deg ψ) ∧
    (IsDominant φ.left →
      IsFinite φ.left ∧ Function.Surjective φ.left ∧
      Nat.card {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1} =
        @Field.finSepDegree _ _ _ _ (ff φ).toAlgebra ∧
      (∀ y : A.left, IsClosed ({y} : Set A.left) →
        Nat.card (φ.left ⁻¹' {y}) = Nat.card {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1}) ∧
      deg φ = @Field.finSepDegree _ _ _ _ (ff φ).toAlgebra *
        @Field.finInsepDegree _ _ _ _ (ff φ).toAlgebra ∧
      ∃ n : ℕ, @Field.finInsepDegree _ _ _ _ (ff φ).toAlgebra = ringExpChar k ^ n) := by
  classical
  -- dominance of an endomorphism of the irreducible scheme `A.left` = it fixes the generic point
  have hdom : ∀ ψ : A ⟶ A,
      ψ.left (genericPoint A.left) = genericPoint A.left → IsDominant ψ.left := by
    intro ψ h
    refine ⟨?_⟩
    have hd : Dense ({genericPoint A.left} : Set A.left) :=
      dense_iff_closure_eq.2 ((genericPoint_spec A.left).trans Set.top_eq_univ)
    exact hd.mono (Set.singleton_subset_iff.2 ⟨_, h⟩)
  -- `deg` is the library's `degree`
  have hdeg_eq : ∀ ψ : A ⟶ A, deg ψ = RamanujanPetersson.IsogDegA.degree ψ.left := by
    intro ψ
    by_cases h : ψ.left (genericPoint A.left) = genericPoint A.left
    · have := hdom ψ h
      rw [hdeg ψ h, hff ψ h, RamanujanPetersson.IsogDegA.degree_of_isDominant]
      rfl
    · have hnd : ¬ IsDominant ψ.left := fun hd ↦
        h (RamanujanPetersson.IsogDegA.map_genericPoint ψ.left)
      rw [hdeg0 ψ h, RamanujanPetersson.IsogDegA.degree_of_not_isDominant _ hnd]
  have hff_eq : ∀ (ψ : A ⟶ A) [IsDominant ψ.left],
      ff ψ = (RamanujanPetersson.IsogDegA.ffMap ψ.left).hom := fun ψ _ ↦
    hff ψ (RamanujanPetersson.IsogDegA.map_genericPoint ψ.left)
  refine ⟨RamanujanPetersson.IsogDegB.isDominant_iff_finite_ker φ, ?_, ?_, ?_⟩
  · rw [hdeg_eq, RamanujanPetersson.IsogDegB.degree_eq_zero_iff,
      RamanujanPetersson.IsogDegB.isDominant_iff_finite_ker, not_finite_iff_infinite]
  · intro ψ _
    rw [hdeg_eq, hdeg_eq, hdeg_eq]
    rw [RamanujanPetersson.IsogDegA.degree_comp_left' A ψ φ]
  · intro hd
    obtain ⟨-, hcard, hfib⟩ := RamanujanPetersson.IsogDegA.card_kerPts A φ
    obtain ⟨-, hfin, hsurj⟩ := RamanujanPetersson.IsogDegA.isogDeg_L24 A φ
    have : ExpChar A.left.functionField (ringExpChar k) :=
      expChar_of_injective_ringHom (RamanujanPetersson.IsogDegA.kMap A).injective _
    obtain ⟨n, hn⟩ := UploadIsogDegSW34.finInsepDegree_ffAlgebra_eq_pow φ.left (ringExpChar k)
      (RamanujanPetersson.IsogDegA.ffMap_finite A φ)
    have h25 := UploadIsogDegSW34.degDom_eq_sep_mul_insep φ.left
    rw [← RamanujanPetersson.IsogDegA.degree_of_isDominant] at h25
    rw [hff_eq φ]
    exact ⟨hfin, hsurj, hcard, hfib, (hdeg_eq φ).trans h25, n, hn⟩

