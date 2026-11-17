-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_sigma_binary_operation
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:10.980201+00:00
-- url     : https://prove2.me/submissions/5b6dc379-16d0-451d-ad9f-10f88442acf7

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.Scheme

/-- Assemble componentwise binary operations by the finite-coproduct
distributivity isomorphism. No connectedness assumption on test schemes is used. -/
theorem _root_.solution
    {ι : Type} [Finite ι] {S : Scheme.{0}} (X : ι → Scheme.{0})
    (f : ∀ i, X i ⟶ S) (k : ι → ι → ι)
    (m : ∀ i j, pullback (f i) (f j) ⟶ X (k i j))
    (hm : ∀ i j, m i j ≫ f (k i j) = pullback.fst (f i) (f j) ≫ f i) :
    ∃ μ : SchemeHomOver
        (pullback.fst (Sigma.desc f) (Sigma.desc f) ≫ Sigma.desc f) (Sigma.desc f),
      ∀ i j,
        pullback.map (f i) (f j) (Sigma.desc f) (Sigma.desc f)
            (Sigma.ι X i) (Sigma.ι X j) (𝟙 S) (by simp) (by simp) ≫ μ.1 =
          m i j ≫ Sigma.ι X (k i j) := by
  let P : ι × ι → Scheme.{0} := fun p => pullback (f p.1) (f p.2)
  let q : ∀ p, P p ⟶ pullback (Sigma.desc f) (Sigma.desc f) := fun p =>
    pullback.map (f p.1) (f p.2) (Sigma.desc f) (Sigma.desc f)
      (Sigma.ι X p.1) (Sigma.ι X p.2) (𝟙 S) (by simp) (by simp)
  let d := Sigma.desc q
  haveI : IsIso d := FinitaryPreExtensive.isIso_sigmaDesc_map f f
  let v : (∐ P) ⟶ ∐ X := Sigma.desc fun p => m p.1 p.2 ≫ Sigma.ι X (k p.1 p.2)
  have hd : d ≫ inv d ≫ v = v := by simp
  have hv : v ≫ Sigma.desc f =
      d ≫ pullback.fst (Sigma.desc f) (Sigma.desc f) ≫ Sigma.desc f := by
    apply Sigma.hom_ext
    intro p
    simp only [v, d, Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
    dsimp [q]
    rw [hm]
    simp only [pullback.map, pullback.lift_fst_assoc, Category.assoc, Sigma.ι_desc]
  refine ⟨⟨inv d ≫ v, ?_⟩, ?_⟩
  · rw [Category.assoc, hv]
    simp
  · intro i j
    have h := congrArg (fun h => Sigma.ι P (i, j) ≫ h) hd
    simpa only [d, v, ← Category.assoc, Sigma.ι_desc, q] using h

end AlgebraicGeometry.Scheme
