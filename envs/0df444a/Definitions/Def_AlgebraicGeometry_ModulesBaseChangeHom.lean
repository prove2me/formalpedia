-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
-- name    : AlgebraicGeometry_ModulesBaseChangeHom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/f61eceb4-3d92-54ce-98ac-3d00807d4885
-- title:
--   Degree-zero base-change morphism for sheaves of modules
-- statement:
--   Fix a commutative square of schemes: morphisms $\pi\colon X\to T$, $\psi\colon T'\to T$, $\pi'\colon X'\to T'$, $g'\colon X'\to X$ together with a proof $h$ of $g' \gg \pi = \pi' \gg \psi$ (that is, $\pi\circ g'=\psi\circ\pi'$). Three definitions are made, all for sheaves of modules on schemes in the sense of `Scheme.Modules`, with its pullback and pushforward functors and the adjunction `pullbackPushforwardAdjunction` ($\pi^{*}\dashv\pi_{*}$).
--
--   First, `pullbackTwoSquare h` is the canonical invertible $2$-cell filling the square of pullback functors, namely the composite of the comparison isomorphism for $(\pi'\gg\psi)^{*}$, the isomorphism transporting pullback along the equality of morphisms given by $h$, and the inverse of the comparison isomorphism for $(g'\gg\pi)^{*}$; in other words the standard identification $\pi'^{*}\psi^{*}\cong(\psi\pi')^{*}=(\pi g')^{*}\cong g'^{*}\pi^{*}$, packaged as a `TwoSquare`. Second, `baseChangeNatTrans h` is its mate across the adjunctions $\pi^{*}\dashv\pi_{*}$ and $\pi'^{*}\dashv\pi'_{*}$, a $2$-cell from $\pi_{*}$ followed by $\psi^{*}$ to $g'^{*}$ followed by $\pi'_{*}$. Third, `baseChangeHom h F`, for a sheaf of modules $F$ on $X$, is its component at $F$: the morphism $\psi^{*}\pi_{*}F\to\pi'_{*}g'^{*}F$.
--
--   The accompanying theorems record: that the component of the $2$-cell is this morphism; naturality in $F$; the two transposed descriptions obtained from the mate calculus, one in terms of the counit of $\pi'^{*}\dashv\pi'_{*}$ and one in terms of the unit of $\pi^{*}\dashv\pi_{*}$; computations of the conjugate transformations of the pullback comparison and transport isomorphisms, culminating in the identification of the conjugate of `pullbackTwoSquare h` with the corresponding composite $\pi_{*}g'_{*}\cong(\pi g')_{*}=(\psi\pi')_{*}\cong\psi_{*}\pi'_{*}$ of pushforward isomorphisms; the adjoint description, that under $\psi^{*}\dashv\psi_{*}$ the morphism corresponds to $\pi_{*}$ of the unit $F\to g'_{*}g'^{*}F$ followed by that composite; and finally the explicit form on sections: for an open $U\subseteq T$, the unit component at $U$ followed by the base-change morphism over $\psi^{-1}U$ equals the unit of $g'^{*}\dashv g'_{*}$ at $\pi^{-1}U$ followed by the restriction along the equality of opens $(\pi'\gg\psi)^{-1}U=(g'\gg\pi)^{-1}U$.
--
--   **Relation to Mathlib.** The categories `Scheme.Modules`, the pullback and pushforward functors with their adjunction and composition isomorphisms, and the mate and conjugate calculus for `TwoSquare` (`mateEquiv`, `conjugateEquiv`, `mateEquiv_counit`, `unit_mateEquiv`) are Mathlib's; the base-change $2$-cell and morphism assembled from them are the project's own.
--
--   **Where it is used.** This supplies the degree-zero comparison morphism of cohomology and base change in the scheme-theoretic layer of the development, available to the many modules that compare pushforward along a morphism with pushforward after a base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesBaseChangeHom.lean

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Mates

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X T X' T' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}

def pullbackTwoSquare (h : g' ≫ π = π' ≫ ψ) :
    TwoSquare (pullback ψ) (pullback π) (pullback π') (pullback g') :=
  (pullbackComp π' ψ).hom ≫ (pullbackCongr h.symm).hom ≫ (pullbackComp g' π).inv

def baseChangeNatTrans (h : g' ≫ π = π' ≫ ψ) :
    TwoSquare (pushforward π) (pullback g') (pullback ψ) (pushforward π') :=
  mateEquiv (pullbackPushforwardAdjunction π) (pullbackPushforwardAdjunction π') (pullbackTwoSquare h)

def baseChangeHom (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (pullback ψ).obj ((pushforward π).obj F) ⟶ (pushforward π').obj ((pullback g').obj F) :=
  (baseChangeNatTrans h).natTrans.app F

theorem baseChangeNatTrans_app (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (baseChangeNatTrans h).natTrans.app F = baseChangeHom h F := rfl

theorem baseChangeHom_naturality (h : g' ≫ π = π' ≫ ψ) {F G : X.Modules} (φ : F ⟶ G) :
    (pullback ψ).map ((pushforward π).map φ) ≫ baseChangeHom h G =
      baseChangeHom h F ≫ (pushforward π').map ((pullback g').map φ) :=
  (baseChangeNatTrans h).natTrans.naturality φ

theorem baseChangeHom_counit (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (pullback π').map (baseChangeHom h F) ≫
        (pullbackPushforwardAdjunction π').counit.app ((pullback g').obj F) =
      (pullbackTwoSquare h).natTrans.app ((pushforward π).obj F) ≫
        (pullback g').map ((pullbackPushforwardAdjunction π).counit.app F) :=
  mateEquiv_counit (pullbackPushforwardAdjunction π) (pullbackPushforwardAdjunction π') (pullbackTwoSquare h) F

theorem unit_baseChangeHom (h : g' ≫ π = π' ≫ ψ) (M : T.Modules) :
    (pullback ψ).map ((pullbackPushforwardAdjunction π).unit.app M) ≫ baseChangeHom h ((pullback π).obj M) =
      (pullbackPushforwardAdjunction π').unit.app ((pullback ψ).obj M) ≫
        (pushforward π').map ((pullbackTwoSquare h).natTrans.app M) :=
  unit_mateEquiv (pullbackPushforwardAdjunction π) (pullbackPushforwardAdjunction π') (pullbackTwoSquare h) M

section adjoint

variable (π ψ π' g')

theorem conjugateEquiv_pullbackCongr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (e : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f) (pullbackCongr e).hom =
      (pushforwardCongr e).inv := by
  subst e
  have h1 : (pullbackCongr (rfl : f = f)).hom = 𝟙 _ := by simp [pullbackCongr]
  rw [h1, conjugateEquiv_id]
  ext M U : 3
  simp [pushforwardCongr_inv_app_app]

theorem pushforwardCongr_symm_inv {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (e : f = g) :
    (pushforwardCongr e.symm).inv = (pushforwardCongr e).hom := by
  ext M U : 3
  simp [pushforwardCongr_inv_app_app, pushforwardCongr_hom_app_app]

theorem conjugateEquiv_pullbackComp_hom {W Y Z : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
        ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)) (pullbackComp f g).hom =
      (pushforwardComp f g).inv := by
  rw [← Iso.hom_comp_eq_id]
  rw [← conjugateEquiv_pullbackComp_inv f g]
  exact conjugateEquiv_comm _ _ (pullbackComp f g).hom_inv_id

theorem conjugateEquiv_pullbackTwoSquare (h : g' ≫ π = π' ≫ ψ) :
    conjugateEquiv ((pullbackPushforwardAdjunction π).comp (pullbackPushforwardAdjunction g'))
        ((pullbackPushforwardAdjunction ψ).comp (pullbackPushforwardAdjunction π'))
        (pullbackTwoSquare h).natTrans =
      (pushforwardComp g' π).hom ≫ (pushforwardCongr h).hom ≫ (pushforwardComp π' ψ).inv := by
  change conjugateEquiv _ _ ((pullbackComp π' ψ).hom ≫ (pullbackCongr h.symm).hom ≫ (pullbackComp g' π).inv) = _
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (π' ≫ ψ)),
    ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (g' ≫ π)),
    conjugateEquiv_pullbackComp_inv, conjugateEquiv_pullbackCongr_hom, pushforwardCongr_symm_inv,
    conjugateEquiv_pullbackComp_hom, Category.assoc]

theorem pullbackPushforwardAdjunction_homEquiv_baseChangeHom (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (pullbackPushforwardAdjunction ψ).homEquiv _ _ (baseChangeHom h F) =
      (pushforward π).map ((pullbackPushforwardAdjunction g').unit.app F) ≫
        (pushforwardComp g' π).hom.app _ ≫ (pushforwardCongr h).hom.app _ ≫ (pushforwardComp π' ψ).inv.app _ := by
  have key := unit_mateEquiv (pullbackPushforwardAdjunction g') (pullbackPushforwardAdjunction ψ)
    (baseChangeNatTrans h) F
  have it := iterated_mateEquiv_conjugateEquiv (pullbackPushforwardAdjunction π)
    (pullbackPushforwardAdjunction π') (pullbackPushforwardAdjunction ψ) (pullbackPushforwardAdjunction g')
    (pullbackTwoSquare h)
  rw [conjugateEquiv_pullbackTwoSquare] at it
  have it' := NatTrans.congr_app it ((pullback g').obj F)
  simp only [NatTrans.comp_app] at it'
  rw [Adjunction.homEquiv_unit]
  have key' : (pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F) ≫
      (pushforward ψ).map ((baseChangeNatTrans h).natTrans.app F) =
      (pushforward π).map ((pullbackPushforwardAdjunction g').unit.app F) ≫
        (mateEquiv (pullbackPushforwardAdjunction g') (pullbackPushforwardAdjunction ψ)
          (baseChangeNatTrans h)).app ((pullback g').obj F) := key.symm
  change (pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F) ≫
      (pushforward ψ).map ((baseChangeNatTrans h).natTrans.app F) = _
  rw [key']
  exact congrArg (fun t => (pushforward π).map ((pullbackPushforwardAdjunction g').unit.app F) ≫ t) it'

theorem unit_app_app_comp_baseChangeHom_app (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) (U : T.Opens) :
    ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫
        (baseChangeHom h F).app (ψ ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫
        ((pullback g').obj F).presheaf.map
          (eqToHom (show (π' ≫ ψ) ⁻¹ᵁ U = (g' ≫ π) ⁻¹ᵁ U by rw [h])).op := by
  have e := congrArg (fun t => Scheme.Modules.Hom.app t U) (pullbackPushforwardAdjunction_homEquiv_baseChangeHom π ψ π' g' h F)
  simp only [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app] at e

  exact e

end adjoint

end AlgebraicGeometry.Scheme.Modules

end


