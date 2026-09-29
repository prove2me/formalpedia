-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.connectedSpace_of_forall_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ec6a35ec-c1e1-57e1-b0fd-3323952291f3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_connectedSpace_of_forall_isIdempotentElem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace E160GC

open TopologicalSpace Opposite

theorem section_eq_of_forall_not_mem {X : Scheme.{u}} (W : X.Opens) (hW : ∀ x : X, x ∉ W)
    (s t : X.presheaf.obj (op W)) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf W s t (fun x hx => absurd hx (hW x))

theorem exists_isIdempotentElem_of_isClopen {X : Scheme.{u}} {U : Set X} (hU : IsClopen U) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      (∀ x : X, x ∈ U → X.presheaf.germ ⊤ x trivial e = 1) ∧
      (∀ x : X, x ∉ U → X.presheaf.germ ⊤ x trivial e = 0) := by
  let U' : X.Opens := ⟨U, hU.isOpen⟩
  let V' : X.Opens := ⟨Uᶜ, hU.compl.isOpen⟩
  have hUV : ∀ x : X, x ∉ U' ⊓ V' := by
    intro x hx
    exact hx.2 hx.1
  have htop : (⊤ : X.Opens) ≤ U' ⊔ V' := by
    intro x _
    by_cases hx : x ∈ U
    · exact Or.inl hx
    · exact Or.inr hx

  let p : RingHom.eqLocus
      (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_left : U' ⊓ V' ⟶ U').op).hom
        (RingHom.fst (X.sheaf.obj.obj <| op U') (X.sheaf.obj.obj <| op V')))
      (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_right : U' ⊓ V' ⟶ V').op).hom
        (RingHom.snd (X.sheaf.obj.obj <| op U') (X.sheaf.obj.obj <| op V'))) :=
    ⟨(1, 0), section_eq_of_forall_not_mem (U' ⊓ V') hUV _ _⟩
  let s : X.presheaf.obj (op (U' ⊔ V')) := (X.sheaf.objSupIsoProdEqLocus U' V').inv p
  have hsU : X.presheaf.map (homOfLE (le_sup_left : U' ≤ U' ⊔ V')).op s = 1 :=
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf U' V' p
  have hsV : X.presheaf.map (homOfLE (le_sup_right : V' ≤ U' ⊔ V')).op s = 0 :=
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf U' V' p
  let e : Γ(X, ⊤) := X.presheaf.map (homOfLE htop).op s
  have he1 : ∀ x : X, x ∈ U → X.presheaf.germ ⊤ x trivial e = 1 := by
    intro x hx
    have h1 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE htop) x trivial s
    have h2 := TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE (le_sup_left : U' ≤ U' ⊔ V')) x (show x ∈ U' from hx) s
    rw [hsU, map_one] at h2
    simp only [e]
    rw [h1, ← h2]
  have he0 : ∀ x : X, x ∉ U → X.presheaf.germ ⊤ x trivial e = 0 := by
    intro x hx
    have h1 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE htop) x trivial s
    have h2 := TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE (le_sup_right : V' ≤ U' ⊔ V')) x (show x ∈ V' from hx) s
    rw [hsV, map_zero] at h2
    simp only [e]
    rw [h1, ← h2]
  refine ⟨e, ?_, he1, he0⟩

  show e * e = e
  apply TopCat.Presheaf.section_ext X.sheaf ⊤ (e * e) e
  intro x hx
  have hm : X.presheaf.germ ⊤ x hx (e * e) =
      X.presheaf.germ ⊤ x hx e * X.presheaf.germ ⊤ x hx e := map_mul _ _ _
  change X.presheaf.germ ⊤ x hx (e * e) = X.presheaf.germ ⊤ x hx e
  rw [hm]
  by_cases hxU : x ∈ U
  · rw [he1 x hxU, mul_one]
  · rw [he0 x hxU, mul_zero]

theorem germ_one_ne_zero {X : Scheme.{u}} (x : X) :
    X.presheaf.germ ⊤ x trivial (1 : Γ(X, ⊤)) ≠ X.presheaf.germ ⊤ x trivial 0 := by
  rw [map_one, map_zero]
  exact one_ne_zero

end E160GC

theorem solution
    (X : Scheme.{u}) [Nonempty X]
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) :
    ConnectedSpace X := by
  have hpre : PreconnectedSpace X := by
    rw [preconnectedSpace_iff_clopen]
    intro U hU
    obtain ⟨e, he, he1, he0⟩ := E160GC.exists_isIdempotentElem_of_isClopen hU
    rcases h e he with h0 | h1
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have := he1 x hx
      rw [h0, map_zero] at this
      exact zero_ne_one this
    · right
      apply Set.eq_univ_iff_forall.mpr
      intro x
      by_contra hx
      have := he0 x hx
      rw [h1, map_one] at this
      exact one_ne_zero this
  haveI := hpre
  exact ⟨inferInstance⟩

end S_AlgebraicGeometry_Scheme_connectedSpace_of_forall_isIdempotentElem
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_connectedSpace_of_forall_isIdempotentElem (solution)
