-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_iso_pointLogHeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:07.734402+00:00
-- url     : https://prove2.me/submissions/3b4e4c94-6440-438e-a7a9-0f5c28b65e73

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- Transporting the sections through a module isomorphism retains the projective map. -/
theorem _root_.solution
    {K : Type} [Field K] [NumberField K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M T : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) (e : M ≅ T) :
    ∃ Q : T.ProjPresentation f N, Q.toProj = P.toProj ∧
      ∀ x : Scheme.KPoint f, Q.pointLogHeight x = P.pointLogHeight x := by
  have hn (U : X.Opens) (i : Fin (N + 1)) :
      T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (e.hom.app ⊤ (P.σ i)) =
        e.hom.app U (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (P.σ i)) := by
    have h := e.hom.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op
    exact (congrFun (congrArg
      (fun t => (ConcreteCategory.hom t : Γ(M, ⊤) → Γ(T, U))) h) (P.σ i)).symm
  let Q : T.ProjPresentation f N :=
    { σ := fun i => e.hom.app ⊤ (P.σ i)
      toProj := P.toProj
      toProj_π := P.toProj_π
      frame := fun i V hV => by
        have hb : Function.Bijective (e.hom.app V : Γ(M, V) → Γ(T, V)) := by
          refine Function.bijective_iff_has_inverse.mpr ⟨e.inv.app V, ?_, ?_⟩
          · intro x
            change (e.hom.app V ≫ e.inv.app V) x = x
            rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
            rfl
          · intro y
            change (e.inv.app V ≫ e.hom.app V) y = y
            rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
            rfl
        have hf := hb.comp (P.frame i V hV)
        change Function.Bijective (fun g : Γ(X, V) => e.hom.app V
          (g • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (P.σ i))) at hf
        simpa only [hn, Scheme.Modules.Hom.app_smul] using hf
      app_ratio_smul := fun i j => by
        simp only [hn]
        rw [← Scheme.Modules.Hom.app_smul, P.app_ratio_smul i j] }
  exact ⟨Q, rfl, fun _ => rfl⟩

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
