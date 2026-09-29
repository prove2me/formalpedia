-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b75095b4-1f4f-577b-95f9-5e3234138eb9

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial

universe u

set_option autoImplicit false
section cechflat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace CechFlatSol

theorem isAffineOpen_inter {V : Scheme.{u}} [V.IsSeparated] (K : V.OrderedAffineCover) :
    ∀ (n : ℕ) (s : K.Idx n), IsAffineOpen (K.inter s) := by
  intro n
  induction n with
  | zero =>
    intro s
    have : K.inter s = K.U (s.1 0) := by
      apply le_antisymm (K.inter_le s 0)
      exact le_iInf fun j => by rw [Subsingleton.elim (α := Fin 1) j 0]
    rw [this]
    exact K.isAffineOpen _
  | succ n ih =>
    intro s
    have : K.inter s = K.U (s.1 0) ⊓ K.inter (K.face s 0) := by
      apply le_antisymm
      · exact le_inf (K.inter_le s 0) (K.inter_le_inter_face s 0)
      · refine le_iInf fun j => ?_
        refine Fin.cases ?_ (fun k => ?_) j
        · exact inf_le_left
        · exact inf_le_right.trans (by
            have := K.inter_le (K.face s 0) k
            rw [K.face_val] at this
            simpa [Fin.succAbove_zero] using this)
    rw [this]
    exact (K.isAffineOpen _).inf (ih _)

end CechFlatSol

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [Flat π] [IsSeparated π] (M : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (K : V.OrderedAffineCover) (i : ℕ) :
    Module.Flat R ((OModulePresheaf.ofModules π M).cochain K i) := by
  classical
  haveI : V.IsSeparated := by
    constructor
    rw [show terminal.from V = π ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  haveI : ∀ s : K.Idx i, Module.Flat R ((OModulePresheaf.ofModules π M).obj (K.inter s)) := fun s => by
    have haff : IsAffineOpen (K.inter s) := CechFlatSol.isAffineOpen_inter K i s
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π (K.inter s)
    haveI : Module.Flat R Γ(V, K.inter s) := Scheme.TwoAffineOpenCover.flat_sections_of_flat π _ haff
    haveI : Module.Projective Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s)) :=
      Scheme.Modules.projective_sections_of_locallyTrivial M htriv ⟨K.inter s, haff⟩
    haveI : Module.Flat Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s)) :=
      Module.Flat.of_projective
    exact Module.Flat.trans R Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s))
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype R (K.Idx i) fun s => (OModulePresheaf.ofModules π M).obj (K.inter s)).symm

end cechflat

end S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial (solution)
