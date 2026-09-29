-- Prove2me | Definitions.Def_AlgebraicGeometry_PolarisationRosati
-- name    : AlgebraicGeometry_PolarisationRosati
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/deb03f11-cac4-5231-ab7a-202ec3f00be9
-- title:
--   Mumford bundle, symmetry, kernel and Rosati conditions
-- statement:
--   Throughout, $S$ is a commutative ring, $f : A \to \operatorname{Spec} S$ a morphism of schemes, and $L$ a relative group law on $f$, so that for each $t : T \to \operatorname{Spec} S$ the points of $A$ over $t$ — pairs consisting of a morphism $T \to A$ together with a proof that composing it with $f$ gives $t$ — carry a multiplication `L.mul`, a unit `L.one` and an inversion `L.inv`.
--
--   Two morphisms are extracted from $L$: `negMor`, the morphism $A \to A$ underlying the inverse of the tautological point $\mathrm{id}_A$ of $A$ over $f$, and `addMor`, the morphism $A \times_S A \to A$ underlying the product of the two projections regarded as points over $\mathrm{pr}_1 \circ f$; `negMor_over` and `addMor_over` record that these lie over $f$ and over $\mathrm{pr}_1 \circ f$ respectively.
--
--   `LocIsoOnBase g M M'`, for $g : X \to \operatorname{Spec} S'$ and two modules on $X$, asserts that every point $s$ of $\operatorname{Spec} S'$ has an open neighbourhood $U$ such that the restrictions of $M$ and $M'$ to $g^{-1}(U)$ admit an isomorphism (existence only, no chosen isomorphism); it is a Zariski-local condition on the base. `IsSymmetric` $\mathcal L$ is `LocIsoOnBase` for $f$ applied to `negMor`$^{*}\mathcal L$ and $\mathcal L$. The `mumfordBundle` of $\mathcal L$ is the module $\mathrm{addMor}^{*}\mathcal L \otimes (\mathrm{pr}_1^{*}\mathcal L^{\vee} \otimes \mathrm{pr}_2^{*}\mathcal L^{\vee})$ on $A \times_S A$, tensor, unit and dual being those of the symmetric monoidal closed structure on modules (the dual is the internal hom into the unit). `sliceAt` sends a point $x$ of $A$ over $t$ to the morphism $A \times_S T \to A \times_S A$ with components $\mathrm{pr}_1$ and $\mathrm{pr}_2$ followed by $x$.
--
--   For affine test bases $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and points $x$ of $A$ over $t$, `KernelTrivial` $\mathcal L$ requires that local triviality over $\operatorname{Spec} R$ of $\mathrm{sliceAt}(x)^{*}\Lambda(\mathcal L)$ — local isomorphy with the unit module, the base morphism being $\mathrm{pr}_2$ — forces $x$ to be the unit point; `KernelIsTwoTorsion` $\mathcal L$ demands the equivalence of that local triviality with $x \cdot x = 1$. Finally, given a family $\iota : I \to (A \to A)$ of morphisms over $f$ and a map $\star : I \to I$ of the index set (no involutivity or additivity being required), `RosatiCompatible` asserts for each $b$ that $(1 \times \iota(b))^{*}\Lambda(\mathcal L)$ and $(\iota(b^{\star}) \times 1)^{*}\Lambda(\mathcal L)$ are isomorphic Zariski-locally on $\operatorname{Spec} S$. All five of these are predicates on $\mathcal L$ and the given data; nothing is asserted to hold.
--
--   **Relation to Mathlib.** Mathlib has no abelian schemes, Mumford bundles, dual abelian schemes or Rosati involutions; these are the project's own predicates, formulated through the functor of points of a relative group law. The tensor product, unit and dual used are those of the monoidal closed structure on a scheme's sheaves of modules developed in this project on top of Mathlib's `SheafOfModules`.
--
--   **Where it is used.** These predicates supply the polarisation data in functor-of-points form: symmetry and the kernel conditions single out the line bundles whose associated Mumford bundle defines a polarisation (principal, or with kernel the $2$-torsion), and Rosati compatibility expresses that a family of endomorphisms is adjoint to itself under $\star$ with respect to that polarisation. They are used for the canonical polarisation of abelian surfaces with quaternionic multiplication and for cutting out the corresponding locus in the moduli problem for polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_PolarisationRosati.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

def idPt : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩

def negMor : A ⟶ A := (L.inv f (idPt f)).1

theorem negMor_over : negMor f L ≫ f = f := (L.inv f (idPt f)).2

def addMor : pullback f f ⟶ A :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1

theorem addMor_over : addMor f L ≫ f = pullback.fst f f ≫ f :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2

def LocIsoOnBase {S' : Type u} [CommRing S'] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S')) (M M' : X.Modules) : Prop :=
  ∀ s : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, s ∈ U ∧
    Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M')

def IsSymmetric (𝓛 : A.Modules) : Prop :=
  LocIsoOnBase f ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) 𝓛

def mumfordBundle (𝓛 : A.Modules) : (pullback f f).Modules :=
  (Scheme.Modules.pullback (addMor f L)).obj 𝓛 ⊗
    ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛) ⊗
      (Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛))

def sliceAt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f) :
    pullback f t ⟶ pullback f f :=
  pullback.lift (pullback.fst f t) (pullback.snd f t ≫ x.1) (by rw [Category.assoc, x.2]; exact pullback.condition)

def KernelTrivial (𝓛 : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules)) →
      x = L.one t

def KernelIsTwoTorsion (𝓛 : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules)) ↔
      L.mul t x x = L.one t

def RosatiCompatible (𝓛 : A.Modules) {I : Type v} (ι : I → (A ⟶ A)) (hι : ∀ b, ι b ≫ f = f) (star : I → I) : Prop :=
  ∀ b : I,
    LocIsoOnBase (pullback.fst f f ≫ f)
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ ι b)
            (by rw [Category.assoc, hι]; exact pullback.condition))).obj (mumfordBundle f L 𝓛))
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f f ≫ ι (star b)) (pullback.snd f f)
            (by rw [Category.assoc, hι]; exact pullback.condition))).obj (mumfordBundle f L 𝓛))

end AlgebraicGeometry.Polarisation

end


