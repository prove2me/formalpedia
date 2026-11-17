-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.finite_fibre_pointProjectivization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:56.0828+00:00
-- url     : https://prove2.me/submissions/17348f9d-2b92-4fa0-87bc-8907b5a99798

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_finite_schemeHomOver_of_isFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- A finite projective presentation has finite fibres on rational points. -/
theorem _root_.solution {K : Type} [Field K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : ℕ} (P : M.ProjPresentation f N)
    (hfin : IsFinite P.toProj) (z : Projectivization K (Fin (N + 1) → K)) :
    {x : Scheme.KPoint f | P.pointProjectivization x = z}.Finite := by
  let y := (ProjSpace.kPointEquivProjectivization K N).symm z
  letI : IsFinite P.toProj := hfin
  letI : Finite (SchemeHomOver y.1 P.toProj) :=
    finite_schemeHomOver_of_isFinite P.toProj K y.1
  let g : {x : Scheme.KPoint f // P.pointProjectivization x = z} →
      SchemeHomOver y.1 P.toProj := fun x => ⟨x.1.1, by
    have h : (⟨x.1.1 ≫ P.toProj, by
        rw [Category.assoc, P.toProj_π]
        exact x.1.2⟩ : Scheme.KPoint (ProjSpace.π K N)) = y := by
      apply (ProjSpace.kPointEquivProjectivization K N).injective
      simpa only [pointProjectivization, y, Equiv.apply_symm_apply] using x.2
    exact congrArg Subtype.val h⟩
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun p : SchemeHomOver y.1 P.toProj => p.1) h
  have hfinite : Finite {x : Scheme.KPoint f // P.pointProjectivization x = z} :=
    Finite.of_injective g hg
  exact @Set.toFinite _ _ hfinite

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
