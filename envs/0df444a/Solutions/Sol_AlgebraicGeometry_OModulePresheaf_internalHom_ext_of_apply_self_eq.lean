-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.internalHom_ext_of_apply_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0a4e7d15-9b58-5fbe-85b1-1728ee69347c

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace HomCohAux

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}

abbrev Dbelow (U : V.affineOpens) (f : Γ(V, U.1)) : OModulePresheaf.AffBelow U.1 :=
  ⟨⟨V.basicOpen f, U.2.basicOpen f⟩, V.basicOpen_le f⟩

lemma apply_basicOpen_eq (hFq : F.IsQuasicoherent) (U : V.affineOpens)
    (φ ψ : (OModulePresheaf.internalHom F G).obj U.1)
    (h : ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = ψ.1 ⟨U, le_rfl⟩ x)
    (f : Γ(V, U.1)) (v : F.obj (V.basicOpen f)) :
    φ.1 (Dbelow U f) v = ψ.1 (Dbelow U f) v := by
  obtain ⟨N, y, hy⟩ := (hFq U f).1 v
  have hφ := φ.2.2 (Dbelow U f) ⟨U, le_rfl⟩ (V.basicOpen_le f) y
  have hψ := ψ.2.2 (Dbelow U f) ⟨U, le_rfl⟩ (V.basicOpen_le f) y
  change φ.1 (Dbelow U f) (F.res (V.basicOpen_le f) y) = G.res (V.basicOpen_le f) (φ.1 ⟨U, le_rfl⟩ y) at hφ
  change ψ.1 (Dbelow U f) (F.res (V.basicOpen_le f) y) = G.res (V.basicOpen_le f) (ψ.1 ⟨U, le_rfl⟩ y) at hψ
  rw [hy, φ.2.1 (Dbelow U f), h y] at hφ
  rw [hy, ψ.2.1 (Dbelow U f)] at hψ
  have hunit : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ N)) := by
    rw [map_pow]
    exact (RingedSpace.isUnit_res_basicOpen (X := V.toLocallyRingedSpace.toRingedSpace) f).pow N
  exact (hunit.smul_left_cancel).mp (hφ.trans hψ.symm)

lemma exists_finite_basicOpen_cover (U : V.affineOpens) (W : OModulePresheaf.AffBelow U.1) :
    ∃ (n : ℕ) (f : Fin n → Γ(V, U.1)),
      (∀ j, V.basicOpen (f j) ≤ W.1.1) ∧ W.1.1 ≤ ⨆ j, V.basicOpen (f j) := by
  classical

  have hpt : ∀ x : W.1.1, ∃ r : Γ(V, U.1), V.basicOpen r ≤ W.1.1 ∧ (x : V) ∈ V.basicOpen r :=
    fun x => U.2.exists_basicOpen_le x (W.2 x.2)
  choose r hrW hxr using hpt
  have hcov : (W.1.1 : Set V) ⊆ ⋃ x : W.1.1, (V.basicOpen (r x) : Set V) :=
    fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxr ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := W.1.2.isCompact.elim_finite_subcover (fun x : W.1.1 => (V.basicOpen (r x) : Set V))
    (fun x => (V.basicOpen (r x)).isOpen) hcov
  refine ⟨t.card, fun j => r (t.equivFin.symm j), fun j => hrW _, fun y hy => ?_⟩
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht hy)
  obtain ⟨hxt, hyx⟩ := Set.mem_iUnion.mp hx
  refine Opens.mem_iSup.mpr ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
  simpa using hyx

theorem internalHom_ext_of_apply_eq (hFq : F.IsQuasicoherent) (hGq : G.IsQuasicoherent) (U : V.affineOpens)
    (φ ψ : (OModulePresheaf.internalHom F G).obj U.1)
    (h : ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = ψ.1 ⟨U, le_rfl⟩ x) : φ = ψ := by
  refine Subtype.ext (funext fun W => LinearMap.ext fun x => ?_)
  obtain ⟨n, f, hfW, hcov⟩ := exists_finite_basicOpen_cover U W

  let g : Fin n → Γ(V, W.1.1) := fun j => (V.presheaf.map (homOfLE W.2).op).hom (f j)
  have hg : ∀ j, V.basicOpen (g j) = V.basicOpen (f j) := fun j =>
    (V.basicOpen_res (f j) (homOfLE W.2).op).trans (inf_eq_right.mpr (hfW j))
  have hcov' : W.1.1 ≤ ⨆ j, V.basicOpen (g j) := by
    refine hcov.trans (iSup_le fun j => ?_)
    rw [← hg j]
    exact le_iSup (fun j => V.basicOpen (g j)) j
  rw [← sub_eq_zero]
  refine AlgebraicGeometry.OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero hGq W.1 g hcov' _ fun j => ?_

  have e1 : V.basicOpen (g j) ≤ V.basicOpen (f j) := (hg j).le
  rw [show G.res (V.basicOpen_le (g j)) = G.res e1 ∘ₗ G.res (hfW j) from G.res_comp e1 (hfW j),
    LinearMap.comp_apply, map_sub]
  have hφ := φ.2.2 (Dbelow U (f j)) W (hfW j) x
  have hψ := ψ.2.2 (Dbelow U (f j)) W (hfW j) x
  change φ.1 (Dbelow U (f j)) (F.res (hfW j) x) = G.res (hfW j) (φ.1 W x) at hφ
  change ψ.1 (Dbelow U (f j)) (F.res (hfW j) x) = G.res (hfW j) (ψ.1 W x) at hψ
  rw [← hφ, ← hψ, apply_basicOpen_eq hFq U φ ψ h (f j), sub_self, map_zero]

theorem internalHom_eval_unique (hFq : F.IsQuasicoherent) (hGq : G.IsQuasicoherent) (U : V.affineOpens)
    (f : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1)
    (φ ψ : (OModulePresheaf.internalHom F G).obj U.1)
    (hφ : ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = f x) (hψ : ∀ x : F.obj U.1, ψ.1 ⟨U, le_rfl⟩ x = f x) :
    φ = ψ :=
  internalHom_ext_of_apply_eq hFq hGq U φ ψ fun x => (hφ x).trans (hψ x).symm

end HomCohAux

end

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
    (hFq : F.IsQuasicoherent) (hGq : G.IsQuasicoherent) (U : V.affineOpens)
    (φ ψ : (OModulePresheaf.internalHom F G).obj U.1)
    (h : ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = ψ.1 ⟨U, le_rfl⟩ x) : φ = ψ :=
  HomCohAux.internalHom_ext_of_apply_eq hFq hGq U φ ψ h

end S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq (solution)
