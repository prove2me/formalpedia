-- Prove2me | Definitions.Def_AlgebraicGeometry_SymmRootFunctor
-- name    : AlgebraicGeometry_SymmRootFunctor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/89882617-a615-53e5-aaf2-4988e7dada20
-- title:
--   Classes of rigidified line bundles; symmetric square-root predicate
-- statement:
--   Throughout, $S$ is a commutative ring, $c\colon C\to\operatorname{Spec}S$ a scheme over $\operatorname{Spec}S$, $\varepsilon$ a section of $c$ (an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) c`, i.e. a morphism $\operatorname{Spec}S\to C$ with $\varepsilon\circ$-composite equal to the identity), and $R_0$ an $S$-algebra. For an object $B$ of `Under (CommRingCat.of R₀)`, i.e. a commutative ring with a ring map from $R_0$, `algS` makes $B$ an $S$-algebra through $S\to R_0\to B$, `ι` is the induced $\operatorname{Spec}B\to\operatorname{Spec}S$, and for $\varphi\colon B\to B'$ the morphism `ψ` is $\operatorname{Spec}\varphi$ viewed as a morphism over $\operatorname{Spec}S$; `comp_algebraMap`, `ψ_val`, `ψ_id`, `ψ_comp` record that this is unital and reverses composition. A `StablePred c ε R₀` is a structure with a field `P` assigning to each $B$ a predicate on $\mathcal O$-modules on $C_B=C\times_{\operatorname{Spec}S}\operatorname{Spec}B$, and a second field asserting that `P` is preserved under pulling back an $\varepsilon$-rigidified line bundle along `ψ φ`; the stability statement is thus carried as data. An `Elem B` is a `RigidifiedLineBundle c ε (ι B)` — a module on $C_B$ that is locally isomorphic to the unit module and whose restriction along the rigidifying section is isomorphic to the unit — together with a proof of `P B` for its underlying module. The setoid identifies two elements whenever their underlying modules are isomorphic (neither rigidification nor the property entering the relation), and `classFunctor` is the resulting covariant functor `Under (CommRingCat.of R₀) ⥤ Type (u+1)`, $B\mapsto$ the quotient, $\varphi\mapsto$ pullback along `baseChangeSnd` of `ψ φ`; the identity and composition laws hold only after passage to classes, via the pullback comparison isomorphisms (`baseChangeSnd_ψ_id`, `baseChangeSnd_ψ_comp`). The helpers `mk`, `mk_surjective`, `mk_eq_mk_iff`, `map_mk`, `classFunctor_obj` describe the quotient map, and `truePred` is the always-true predicate.
--
--   In the final section $f\colon A\to\operatorname{Spec}S$ carries a `RelativeGroupLaw` $L$ and $\mathcal L$ is a module on $A$. For $B$ and a module $M$ on $A_B=A\times_{\operatorname{Spec}S}\operatorname{Spec}B$, `symmRootPred` is the conjunction of two conditions, both of the form `LocIsoOnBase` over $\operatorname{Spec}B$ (for each point of $\operatorname{Spec}B$ there is an open neighbourhood $U$ such that the two modules become isomorphic after restriction to the preimage of $U$): first, $M$ is symmetric for the base-changed group law $L_B$, i.e. the pullback of $M$ along the inversion morphism of $L_B$ is locally on $\operatorname{Spec}B$ isomorphic to $M$; second, the pullback of $\mathcal L$ along $A_B\to A$ is locally on $\operatorname{Spec}B$ isomorphic to $M\otimes[-1]^*M$. So the predicate asks only for isomorphisms locally over the base, on the chosen modules, rather than a global isomorphism. `symmRootPred_iff` is the unfolding, and `symmRootStablePred` takes the required stability statement as an explicit hypothesis and packages `symmRootPred` into a `StablePred f (L.one (𝟙 _)) R₀`, the rigidifying section being the unit section of the group law.
--
--   **Relation to Mathlib.** Mathlib has no relative Picard functor, no rigidified line bundles and no notion of symmetric square root of a line bundle on an abelian scheme; these are the project's own notions, built on Mathlib's sheaves of modules on schemes, their pullback functors and monoidal structure, scheme pullbacks, and the `Under` category of a commutative ring.
--
--   **Where it is used.** The functor constructed here is the shape of test objects (affine algebras over an intermediate ring $R_0$, covariantly) used in the representability arguments for symmetric square roots of a line bundle on an abelian scheme, which in turn feed the polarisation and Rosati material for Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SymmRootFunctor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

namespace AlgebraicGeometry.SymmRoot

section base
variable (S : Type u) [CommRing S] (R₀ : Type u) [CommRing R₀] [Algebra S R₀]

abbrev algS (B : Under (CommRingCat.of R₀)) : Algebra S B.right := (B.hom.hom.comp (algebraMap S R₀)).toAlgebra

abbrev ι (B : Under (CommRingCat.of R₀)) : Spec (CommRingCat.of B.right) ⟶ Spec (CommRingCat.of S) :=
  letI := algS S R₀ B
  Spec.map (CommRingCat.ofHom (algebraMap S B.right))

theorem comp_algebraMap {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') :
    letI := algS S R₀ B; letI := algS S R₀ B'
    φ.right.hom.comp (algebraMap S B.right) = algebraMap S B'.right := by
  ext x
  change φ.right.hom (B.hom.hom (algebraMap S R₀ x)) = B'.hom.hom (algebraMap S R₀ x)
  rw [← Under.w φ]
  rfl

def ψ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') : SchemeHomOver (ι S R₀ B') (ι S R₀ B) :=
  ⟨Spec.map φ.right, by
    letI := algS S R₀ B; letI := algS S R₀ B'
    change Spec.map (CommRingCat.ofHom φ.right.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap S B.right)) =
      Spec.map (CommRingCat.ofHom (algebraMap S B'.right))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, comp_algebraMap]⟩

@[simp] theorem ψ_val {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') : (ψ S R₀ φ).1 = Spec.map φ.right := rfl

theorem ψ_id (B : Under (CommRingCat.of R₀)) : (ψ S R₀ (𝟙 B)).1 = 𝟙 _ := by
  rw [ψ_val]; exact Spec.map_id _

theorem ψ_comp {B B' B'' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (χ : B' ⟶ B'') :
    (ψ S R₀ (φ ≫ χ)).1 = (ψ S R₀ χ).1 ≫ (ψ S R₀ φ).1 := by
  simp only [ψ_val, Under.comp_right, Spec.map_comp]

end base

section functor
variable {S : Type u} [CommRing S] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of S))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) c) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]

structure StablePred where

  P : ∀ (B : Under (CommRingCat.of R₀)), (pullback c (ι S R₀ B)).Modules → Prop

  of_pullbackAlong : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (M : RigidifiedLineBundle c ε (ι S R₀ B)),
    P B M.L → P B' (M.pullbackAlong (ψ S R₀ φ)).L

variable (P : StablePred c ε R₀)

structure Elem (B : Under (CommRingCat.of R₀)) where

  M : RigidifiedLineBundle c ε (ι S R₀ B)
  prop : P.P B M.L

instance setoid (B : Under (CommRingCat.of R₀)) : Setoid (Elem c ε R₀ P B) where
  r x y := Nonempty (x.M.L ≅ y.M.L)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i ≪≫ j⟩⟩

def Elem.map {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (x : Elem c ε R₀ P B) : Elem c ε R₀ P B' :=
  ⟨x.M.pullbackAlong (ψ S R₀ φ), P.of_pullbackAlong φ x.M x.prop⟩

@[simp] theorem Elem.map_M {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (x : Elem c ε R₀ P B) :
    (x.map c ε R₀ P φ).M = x.M.pullbackAlong (ψ S R₀ φ) := rfl

theorem baseChangeSnd_ψ_id (B : Under (CommRingCat.of R₀)) : baseChangeSnd c (ψ S R₀ (𝟙 B)) = 𝟙 _ := by
  rw [← baseChangeSnd_id c (ι S R₀ B)]
  unfold baseChangeSnd
  congr 1
  exact ψ_id S R₀ B

theorem baseChangeSnd_ψ_comp {B B' B'' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (χ : B' ⟶ B'') :
    baseChangeSnd c (ψ S R₀ (φ ≫ χ)) = baseChangeSnd c (ψ S R₀ χ) ≫ baseChangeSnd c (ψ S R₀ φ) := by
  rw [baseChangeSnd_comp]
  congr 1
  exact Subtype.ext (ψ_comp S R₀ φ χ)

def classFunctor : Under (CommRingCat.of R₀) ⥤ Type (u + 1) where
  obj B := Quotient (setoid c ε R₀ P B)
  map {B B'} φ := TypeCat.ofHom
    (Quotient.map (Elem.map c ε R₀ P φ) (fun x y h => RigidifiedLineBundle.pullbackAlong_congr _ h))
  map_id B := TypeCat.homEquiv.injective (funext fun x => by
    induction x using Quotient.ind with
    | _ r =>
      exact Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_ψ_id c R₀ B)).app r.M.L ≪≫ (Scheme.Modules.pullbackId _).app r.M.L⟩)
  map_comp {B B' B''} φ χ := TypeCat.homEquiv.injective (funext fun x => by
    induction x using Quotient.ind with
    | _ r =>
      exact Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_ψ_comp c R₀ φ χ)).app r.M.L ≪≫
          ((Scheme.Modules.pullbackComp _ _).app r.M.L).symm⟩)

abbrev mk {B : Under (CommRingCat.of R₀)} (x : Elem c ε R₀ P B) : (classFunctor c ε R₀ P).obj B := Quotient.mk _ x

theorem mk_surjective (B : Under (CommRingCat.of R₀)) : Function.Surjective (mk c ε R₀ P (B := B)) :=
  Quotient.mk_surjective

theorem mk_eq_mk_iff {B : Under (CommRingCat.of R₀)} (x y : Elem c ε R₀ P B) :
    mk c ε R₀ P x = mk c ε R₀ P y ↔ Nonempty (x.M.L ≅ y.M.L) :=
  Quotient.eq

@[simp] theorem map_mk {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (x : Elem c ε R₀ P B) :
    (classFunctor c ε R₀ P).map φ (mk c ε R₀ P x) = mk c ε R₀ P (x.map c ε R₀ P φ) := rfl

@[simp] theorem classFunctor_obj (B : Under (CommRingCat.of R₀)) :
    (classFunctor c ε R₀ P).obj B = Quotient (setoid c ε R₀ P B) := rfl

example (B : Under (CommRingCat.of R₀)) (x : (classFunctor c ε R₀ P).obj B) :
    (classFunctor c ε R₀ P).map (𝟙 B) x = x := by
  rw [(classFunctor c ε R₀ P).map_id]; rfl

def truePred : StablePred c ε R₀ := ⟨fun _ _ => True, fun _ _ _ => trivial⟩

example (B : Under (CommRingCat.of R₀)) : (classFunctor c ε R₀ (truePred c ε R₀)).obj B :=
  mk c ε R₀ (truePred c ε R₀) ⟨RigidifiedLineBundle.unit (ι S R₀ B), trivial⟩

example {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') :
    (classFunctor c ε R₀ (truePred c ε R₀)).map φ
        (mk c ε R₀ (truePred c ε R₀) ⟨RigidifiedLineBundle.unit (ι S R₀ B), trivial⟩) =
      mk c ε R₀ (truePred c ε R₀) ⟨RigidifiedLineBundle.unit (ι S R₀ B'), trivial⟩ := by
  rw [map_mk, mk_eq_mk_iff]
  exact ⟨Scheme.Modules.pullbackUnitIso _⟩

end functor

section symmRoot
variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (𝓛 : A.Modules) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]

def symmRootPred (B : Under (CommRingCat.of R₀)) (M : (pullback f (ι S R₀ B)).Modules) : Prop :=
  IsSymmetric (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)) M ∧
  LocIsoOnBase (pullback.snd f (ι S R₀ B))
    ((Scheme.Modules.pullback (pullback.fst f (ι S R₀ B))).obj 𝓛)
    (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)))).obj M)

theorem symmRootPred_iff (B : Under (CommRingCat.of R₀)) (M : (pullback f (ι S R₀ B)).Modules) :
    symmRootPred L 𝓛 R₀ B M ↔
      IsSymmetric (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)) M ∧
      LocIsoOnBase (pullback.snd f (ι S R₀ B))
        ((Scheme.Modules.pullback (pullback.fst f (ι S R₀ B))).obj 𝓛)
        (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)))).obj M) :=
  Iff.rfl

abbrev symmRootStablePred
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (M : RigidifiedLineBundle f (L.one (𝟙 _)) (ι S R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (ψ S R₀ φ)).L) :
    StablePred f (L.one (𝟙 _)) R₀ :=
  ⟨symmRootPred L 𝓛 R₀, h⟩

end symmRoot

end AlgebraicGeometry.SymmRoot

end


