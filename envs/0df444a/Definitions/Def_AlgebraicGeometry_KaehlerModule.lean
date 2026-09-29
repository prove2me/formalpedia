-- Prove2me | Definitions.Def_AlgebraicGeometry_KaehlerModule
-- name    : AlgebraicGeometry_KaehlerModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/94421984-e2e3-5988-af93-193c0a76b481
-- title:
--   Relative Kähler differentials and top-degree differentials of a scheme over an affine base
-- statement:
--   Throughout, $A$ is a commutative ring, $X$ a scheme and $f : X \to \operatorname{Spec} A$ a morphism of schemes. The first construction, `constToPresheaf`, is the morphism of presheaves of commutative rings on $X$ from the constant presheaf with value $A$ to $\mathcal O_X$ whose component at an open $U$ is the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism followed by $f$'s map on sections $\Gamma(\operatorname{Spec} A, \top) \to \Gamma(X, U)$; `sectionsAlgebra` repackages this component as an $A$-algebra structure on $\Gamma(X, U)$. Applying Mathlib's relative-differentials construction for a morphism of presheaves of rings to `constToPresheaf` gives `kaehlerPresheaf`, the presheaf of $\mathcal O_X$-modules with $U \mapsto \Omega_{\Gamma(X,U)/A}$, as recorded objectwise by `kaehlerPresheaf_obj`. Its sheafification (for the identity morphism of the structure sheaf of rings) is `kaehler`, an object of the category of sheaves of $\mathcal O_X$-modules, playing the role of $\Omega^1_{X/A}$. For $d : \mathbb N$, `topDifferentials d` is `Scheme.Modules.det d` of `kaehler`, i.e. the sheafification of the sectionwise $d$-th exterior power of the underlying presheaf of modules of $\Omega^1_{X/A}$; separately, `topPresheaf d` is the sectionwise $d$-th exterior power of the presheaf `kaehlerPresheaf` itself, before any sheafification.
--
--   Two comparison maps are provided: `kaehlerToSectionsₗ U` is the component at $U$ of the unit of the sheafification adjunction, a $\Gamma(X,U)$-linear map $\Omega_{\Gamma(X,U)/A} \to \Gamma(\Omega^1_{X/A}, U)$, with `kaehlerToSections` its underlying function; and `topToSections d U` sends an element of $\bigwedge^d_{\Gamma(X,U)} \Omega_{\Gamma(X,U)/A}$ first through the $d$-th exterior power of `kaehlerToSectionsₗ U` and then through the unit at the exterior-power presheaf, landing in $\Gamma(\omega^d_{X/A}, U)$. Two small results accompany the definitions: `kaehlerToSections_add` states additivity of the comparison map, and `kaehlerPresheaf_nontrivial_polynomial` states that for a nontrivial commutative ring $A$ the presheaf of differentials of $\operatorname{Spec} A[t] \to \operatorname{Spec} A$ has a nontrivial module of global sections, deduced from surjectivity of the base-change map of Kähler differentials along the identification of global sections of $\operatorname{Spec} A[t]$ with $A[t]$ together with nontriviality of $\Omega_{A[t]/A}$.
--
--   **Relation to Mathlib.** The presheaf of differentials is Mathlib's relative-differentials construction for a morphism of presheaves of rings, and the passage to a sheaf of modules is Mathlib's sheafification; the exterior power used for the top-degree differentials is the project's own sectionwise exterior-power functor on presheaves of modules.
--
--   **Where it is used.** These objects provide the vocabulary of relative and top-degree differentials for a scheme over an affine base, as needed for invariant differentials on smooth group schemes and for the theory of Néron and minimal models of elliptic curves that enters the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_KaehlerModule.lean

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of A) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]

@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra A Γ(X, U) :=
  (f.constToPresheaf.app (op U)).hom.toAlgebra

def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' f.constToPresheaf

def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj f.kaehlerPresheaf

def topDifferentials (d : ℕ) : X.Modules :=
  Scheme.Modules.det d f.kaehler

abbrev topPresheaf (d : ℕ) : X.PresheafOfModules :=
  (Scheme.Modules.presheafExteriorPower X d).obj f.kaehlerPresheaf

@[simp] lemma kaehlerPresheaf_obj (U : (X.Opens)ᵒᵖ) :
    f.kaehlerPresheaf.obj U = CommRingCat.KaehlerDifferential (f.constToPresheaf.app U) := rfl

def kaehlerToSections (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U) : Type u) → (Γ(f.kaehler, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf).app (op U)).hom s

def kaehlerToSectionsₗ (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U)) →ₗ[Γ(X, U)] (Γ(f.kaehler, U) : Type u) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf).app (op U)).hom

def topToSections (d : ℕ) (U : X.Opens) :
    (⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U)) : Type u) → (Γ(f.topDifferentials d, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom
    (exteriorPower.map d (f.kaehlerToSectionsₗ U) s)

theorem kaehlerToSections_add (U : X.Opens) (s t : f.kaehlerPresheaf.obj (op U)) :
    f.kaehlerToSections U (s + t) = f.kaehlerToSections U s + f.kaehlerToSections U t :=
  map_add (f.kaehlerToSectionsₗ U) s t

theorem kaehlerPresheaf_nontrivial_polynomial (A : Type u) [CommRing A] [Nontrivial A] :
    letI f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    Nontrivial (f.kaehlerPresheaf.obj (op ⊤)) := by
  set f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A))) with hf

  let Γ' : Type u := Γ(Spec (CommRingCat.of (Polynomial A)), ⊤)
  letI algA : Algebra A Γ' := f.sectionsAlgebra ⊤
  let e : Γ' ≃+* Polynomial A := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).commRingCatIsoToRingEquiv
  letI : Algebra Γ' (Polynomial A) := e.toRingHom.toAlgebra

  have hcomp : (algebraMap Γ' (Polynomial A)).comp (algebraMap A Γ') = algebraMap A (Polynomial A) := by
    refine RingHom.ext fun a => ?_
    change (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).hom.hom
      ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = algebraMap A (Polynomial A) a
    have h1 : f.appLE ⊤ ⊤ le_top = f.appTop := by
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    rw [h1]
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    rw [← hf] at h2
    have h3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) h2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
    rw [h3]
    change algebraMap A (Polynomial A) (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom a) = _
    rw [Iso.inv_hom_id]; rfl
  haveI : IsScalarTower A Γ' (Polynomial A) := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hsurj : Function.Surjective (KaehlerDifferential.map A A Γ' (Polynomial A)) :=
    KaehlerDifferential.map_surjective_of_surjective A A (h := e.surjective)
  haveI : Nontrivial (Ω[Polynomial A⁄A]) :=
    (KaehlerDifferential.polynomialEquiv A).toEquiv.nontrivial
  exact hsurj.nontrivial

end AlgebraicGeometry.Scheme.Hom

end

/-- info: 'AlgebraicGeometry.Scheme.Hom.kaehlerToSections_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.Scheme.Hom.kaehlerToSections_add

/--
info: 'AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_nontrivial_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_nontrivial_polynomial


