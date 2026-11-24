-- Prove2me | solution 1 for AlgebraicGeometry.exists_grpObj_of_strictBirationalGroupLaw
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-24T23:21:21.492942+00:00
-- url     : https://prove2.me/submissions/46ebe3c4-4edb-4b1c-942b-2cdaddaf545d

import Mathlib
import Definitions.Def_RPLib_S4_CDPack35

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsSeparated sX] [LocallyOfFiniteType sX] [GeometricallyReduced sX]
    (Ω : (pullback sX sX).Opens) (m : Ω.toScheme ⟶ X)
    (Φ : Ω.toScheme ⟶ pullback sX sX) (hΦ₁ : Φ ≫ pullback.fst sX sX = Ω.ι ≫ pullback.fst sX sX)
    (hΦ₂ : Φ ≫ pullback.snd sX sX = m) (hΦ : IsOpenImmersion Φ)
    (Ψ : Ω.toScheme ⟶ pullback sX sX) (hΨ₁ : Ψ ≫ pullback.fst sX sX = m)
    (hΨ₂ : Ψ ≫ pullback.snd sX sX = Ω.ι ≫ pullback.snd sX sX) (hΨ : IsOpenImmersion Ψ)
    (hleft : ∀ a : X, IsClosed ({a} : Set X) →
      ∃ z ∈ Ω, IsClosed ({z} : Set (pullback sX sX : Scheme.{0})) ∧ pullback.fst sX sX z = a)
    (hright : ∀ b : X, IsClosed ({b} : Set X) →
      ∃ z ∈ Ω, IsClosed ({z} : Set (pullback sX sX : Scheme.{0})) ∧ pullback.snd sX sX z = b)
    (hassoc : ∀ z₁ z₂ z₃ z₄ : Ω, IsClosed {z₁.1} → IsClosed {z₂.1} → IsClosed {z₃.1} → IsClosed {z₄.1} →
      pullback.snd sX sX z₁.1 = pullback.fst sX sX z₂.1 →
      pullback.fst sX sX z₃.1 = m z₁ → pullback.snd sX sX z₃.1 = pullback.snd sX sX z₂.1 →
      pullback.fst sX sX z₄.1 = pullback.fst sX sX z₁.1 → pullback.snd sX sX z₄.1 = m z₂ →
      m z₃ = m z₄) :
    ∃ (G : Over (Spec (.of k))) (_ : GrpObj G) (j : X ⟶ G.left) (hj : j ≫ G.hom = sX),
      Smooth G.hom ∧ IsSeparated G.hom ∧ LocallyOfFiniteType G.hom ∧ IsIntegral G.left ∧
      IsOpenImmersion j ∧ DenseRange j ∧
      Ω.ι ≫ pullback.map sX sX G.hom G.hom j j (𝟙 _) (by rw [hj, Category.comp_id])
          (by rw [hj, Category.comp_id]) ≫ (MonObj.mul : G ⊗ G ⟶ G).left = m ≫ j ∧
      ∀ (G' : Over (Spec (.of k))) [GrpObj G'] [LocallyOfFiniteType G'.hom] [IsSeparated G'.hom]
        [IsIntegral G'.left] (j' : X ⟶ G'.left) (hj' : j' ≫ G'.hom = sX), IsOpenImmersion j' →
        Ω.ι ≫ pullback.map sX sX G'.hom G'.hom j' j' (𝟙 _) (by rw [hj', Category.comp_id])
            (by rw [hj', Category.comp_id]) ≫ (MonObj.mul : G' ⊗ G' ⟶ G').left = m ≫ j' →
        ∃! e : G.left ≅ G'.left, e.hom ≫ G'.hom = G.hom ∧ j ≫ e.hom = j' := by
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  haveI : IsSeparated (X ↘ Spec (.of k)) := ‹IsSeparated sX›
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType sX›
  haveI : GeometricallyReduced (X ↘ Spec (.of k)) := ‹GeometricallyReduced sX›
  haveI : X.IsSeparated :=
    ⟨by rw [terminal.hom_ext (terminal.from X) (sX ≫ terminal.from _)]; infer_instance⟩
  let C : RamanujanPetersson.JacChunk.StrictChunk (X ↘ Spec (.of k)) :=
    { Ω := Ω, m := m, Φ := Φ, Φ_fst := hΦ₁, Φ_snd := hΦ₂, isOpenImmersion_Φ := hΦ, Ψ := Ψ,
      Ψ_fst := hΨ₁, Ψ_snd := hΨ₂, isOpenImmersion_Ψ := hΨ, fib_left := hleft, fib_right := hright,
      assoc := hassoc }
  letI := C.grpObj
  refine ⟨C.GO, C.grpObj, RamanujanPetersson.JacChunk.ι C.H 1, RamanujanPetersson.JacChunk.ι_sG C.H 1,
    C.smooth_sG, C.isSeparated_sG,
    (inferInstance : LocallyOfFiniteType (RamanujanPetersson.JacChunk.sG C.H)),
    isIntegral_of_irreducibleSpace_of_isReduced (RamanujanPetersson.JacChunk.G C.H), inferInstance, C.denseRange_ι1,
    C.mu_ι1, ?_⟩
  intro G' _ _ _ _ j' hj' _ hjm
  exact C.existsUnique_iso G' j' hj' hjm
