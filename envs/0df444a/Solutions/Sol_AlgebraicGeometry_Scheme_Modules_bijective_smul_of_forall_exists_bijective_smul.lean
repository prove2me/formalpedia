-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0a0d27cc-c603-5084-9ff1-96c6e05e8892

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FrameLocalSol

variable {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤))

noncomputable abbrev res (W : X.Opens) : Γ(M, W) := M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ

theorem res_map {W W' : X.Opens} (i : W' ⟶ W) : M.presheaf.map i.op (res M σ W) = res M σ W' := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem smul_res {W W' : X.Opens} (i : W' ⟶ W) (g : Γ(X, W)) :
    M.presheaf.map i.op (g • res M σ W) = X.presheaf.map i.op g • res M σ W' := by
  rw [Scheme.Modules.map_smul, res_map]

noncomputable def abSheaf : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

theorem main (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • res M σ W) :
    Function.Bijective fun g : Γ(X, V) => g • res M σ V := by
  classical
  choose U hxU hU using fun x : V => h x.1 x.2
  let W : V → X.Opens := fun x => V ⊓ U x
  have hWV : ∀ x, W x ≤ V := fun x => inf_le_left
  have hWU : ∀ x, W x ≤ U x := fun x => inf_le_right
  have hcover : V ≤ iSup W := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, ⟨hy, hxU ⟨y, hy⟩⟩⟩
  constructor
  · intro g₁ g₂ hg
    have hg' : g₁ • res M σ V = g₂ • res M σ V := hg
    apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf W V (fun x => homOfLE (hWV x)) hcover
    intro x
    apply (hU x (W x) (hWU x)).1
    show X.presheaf.map (homOfLE (hWV x)).op g₁ • res M σ (W x) =
      X.presheaf.map (homOfLE (hWV x)).op g₂ • res M σ (W x)
    rw [← smul_res, ← smul_res, hg']
  · intro s
    have hloc : ∀ x, ∃! g : Γ(X, W x), g • res M σ (W x) = M.presheaf.map (homOfLE (hWV x)).op s :=
      fun x => (Function.bijective_iff_existsUnique _).1 (hU x (W x) (hWU x)) _
    choose gx hgx hgx_uniq using hloc
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W gx := by
      intro x y
      apply (hU x (W x ⊓ W y) (inf_le_left.trans (hWU x))).1
      show X.presheaf.map (Opens.infLELeft (W x) (W y)).op (gx x) • res M σ (W x ⊓ W y) =
        X.presheaf.map (Opens.infLERight (W x) (W y)).op (gx y) • res M σ (W x ⊓ W y)
      rw [← smul_res M σ (Opens.infLELeft (W x) (W y)), hgx x, ← smul_res M σ (Opens.infLERight (W x) (W y)),
        hgx y, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, ← op_comp, ← op_comp]
      rfl
    obtain ⟨g, hg, -⟩ : ∃! g : Γ(X, V), ∀ x, X.presheaf.map (homOfLE (hWV x)).op g = gx x :=
      TopCat.Sheaf.existsUnique_gluing' X.sheaf W V (fun x => homOfLE (hWV x)) hcover gx hcompat
    refine ⟨g, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' (abSheaf M) W V (fun x => homOfLE (hWV x)) hcover
    intro x
    show M.presheaf.map (homOfLE (hWV x)).op (g • res M σ V) = M.presheaf.map (homOfLE (hWV x)).op s
    rw [smul_res, ← hgx x]
    exact congrArg (· • res M σ (W x)) (hg x)

end FrameLocalSol

theorem solution
    {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : Γ(M, W))) :
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ : Γ(M, V)) :=
  FrameLocalSol.main M σ V h

end S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul (solution)
