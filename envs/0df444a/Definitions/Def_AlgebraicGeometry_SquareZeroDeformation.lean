-- Prove2me | Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
-- name    : AlgebraicGeometry_SquareZeroDeformation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/a478c26d-090c-5aae-b4b7-79e9ea97d589
-- title:
--   Square-zero extensions, tangent points, deformations of the trivial bundle
-- statement:
--   Fix a field $K$ and a $K$-module $V$ (carried as a $K$-bimodule with central scalars, as Mathlib's `TrivSqZeroExt` requires). The ring $K \oplus V$ with $(a,v)(b,w) = (ab, aw+bv)$ is shown to be local: an element is a unit exactly when its first component is nonzero, and if that component vanishes then $1-$ the element is a unit. The scheme `SquareZero.spec K V` is $\operatorname{Spec}(K\oplus V)$; `toBase` is the morphism to $\operatorname{Spec} K$ induced by the structure map $K \to K\oplus V$, and `basePoint` the $K$-point induced by the projection $K\oplus V \to K$, so that `basePoint` followed by `toBase` is the identity — `basePointOver` records this point as an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase K V)`. A $K$-linear $\varphi : V \to W$ induces the $K$-algebra map $K\oplus V \to K\oplus W$ and hence `specMap K φ : spec K W ⟶ spec K V`, compatible with `toBase` and with the base points, contravariantly functorial in $\varphi$ ($\mathrm{id}$ to the identity, $\psi \circ \varphi$ to `specMap K φ` preceded by `specMap K ψ`), and also packaged as a morphism over $\operatorname{Spec} K$.
--
--   For a scheme $X$ with a morphism $x : X \to \operatorname{Spec} K$ and a morphism $pt : \operatorname{Spec} K \to X$, `TangentPoints x pt V` is the subtype of morphisms $v : \operatorname{Spec}(K\oplus V) \to X$ satisfying $v$ followed by $x$ equals `toBase K V` and `basePoint K V` followed by $v$ equals $pt$; it is extensional in the underlying morphism and covariantly functorial in $V$ by precomposition with `specMap K φ`.
--
--   For $c : C \to \operatorname{Spec} K$ with a section $\varepsilon$, `TrivialModDeformations c ε V` is the subtype of those rigidified line bundles on $C \times_{\operatorname{Spec} K} \operatorname{Spec}(K \oplus V)$ — invertible modules, trivialised along the section cut out by $\varepsilon$ — whose pullback along `basePointOver K V` admits, on underlying modules only, an isomorphism with the unit module of `RigidifiedLineBundle.unit (𝟙 (Spec (CommRingCat.of K)))`; the condition is the nonemptiness of a set of module isomorphisms, not a chosen one, and it ignores compatibility with the rigidifications. Functoriality in $V$ is given by pullback along `specMapOver K φ`, the required base-point identity being supplied by `postComp_specMapOver_basePointOver`.
--
--   **Relation to Mathlib.** The algebra $K\oplus V$, its functoriality and the projection homomorphism are Mathlib's `TrivSqZeroExt`, `TrivSqZeroExt.map` and `TrivSqZeroExt.fstHom`; the local ring instance for it and all the scheme-level notions (the square-zero base, its points, $V$-valued tangent points, and deformations of the trivial rigidified line bundle) are the project's own, built on the project's relative Picard vocabulary.
--
--   **Where it is used.** These definitions supply the first-order (square-zero) test objects used when tangent spaces of the relative Picard functor and of related moduli of line bundles on curves over a field are analysed, in the Néron model and relative Picard infrastructure of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SquareZeroDeformation.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TrivSqZeroExt NeronModelInfra

namespace AlgebraicGeometry

namespace SquareZero

variable (K : Type u) [Field K]
variable (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

instance isLocalRing : IsLocalRing (TrivSqZeroExt K V) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : a.fst = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, h, sub_zero]
      exact isUnit_one
    · left
      exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (Ne.isUnit h)

instance isLocalRing' : IsLocalRing (CommRingCat.of (TrivSqZeroExt K V)) :=
  SquareZero.isLocalRing K V

abbrev spec : Scheme.{u} := Spec (CommRingCat.of (TrivSqZeroExt K V))

def toBase : spec K V ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K V)))

def basePoint : Spec (CommRingCat.of K) ⟶ spec K V :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K V).toRingHom)

@[reassoc (attr := simp)]
theorem basePoint_toBase : basePoint K V ≫ toBase K V = 𝟙 _ := by
  rw [basePoint, toBase, ← Spec.map_comp, ← Spec.map_id]
  congr 1

def basePointOver : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase K V) :=
  ⟨basePoint K V, basePoint_toBase K V⟩

@[simp] theorem basePointOver_coe : (basePointOver K V).1 = basePoint K V := rfl

variable {V}
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
variable {W' : Type u} [AddCommGroup W'] [Module K W'] [Module Kᵐᵒᵖ W'] [IsCentralScalar K W']

def specMap (φ : V →ₗ[K] W) : spec K W ⟶ spec K V :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map φ).toRingHom)

@[reassoc (attr := simp)]
theorem specMap_toBase (φ : V →ₗ[K] W) : specMap K φ ≫ toBase K V = toBase K W := by
  rw [specMap, toBase, toBase, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change TrivSqZeroExt.map φ (algebraMap K _ a) = algebraMap K _ a
  exact (TrivSqZeroExt.map φ).commutes a

@[reassoc (attr := simp)]
theorem basePoint_specMap (φ : V →ₗ[K] W) : basePoint K W ≫ specMap K φ = basePoint K V := by
  rw [specMap, basePoint, basePoint, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change (TrivSqZeroExt.map φ a).fst = a.fst
  exact TrivSqZeroExt.fst_map φ a

theorem specMap_id : specMap K (LinearMap.id : V →ₗ[K] V) = 𝟙 _ := by
  rw [specMap, TrivSqZeroExt.map_id, ← Spec.map_id]
  rfl

theorem specMap_comp (φ : V →ₗ[K] W) (ψ : W →ₗ[K] W') :
    specMap K (ψ ∘ₗ φ) = specMap K ψ ≫ specMap K φ := by
  rw [specMap, specMap, specMap, ← Spec.map_comp, TrivSqZeroExt.map_comp_map]
  rfl

def specMapOver (φ : V →ₗ[K] W) : SchemeHomOver (toBase K W) (toBase K V) :=
  ⟨specMap K φ, specMap_toBase K φ⟩

@[simp] theorem specMapOver_coe (φ : V →ₗ[K] W) : (specMapOver K φ).1 = specMap K φ := rfl

end SquareZero

section TangentPoints

variable {K : Type u} [Field K] {X : Scheme.{u}}

def TangentPoints (x : X ⟶ Spec (CommRingCat.of K)) (pt : Spec (CommRingCat.of K) ⟶ X)
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] : Type u :=
  { v : SquareZero.spec K V ⟶ X // v ≫ x = SquareZero.toBase K V ∧ SquareZero.basePoint K V ≫ v = pt }

namespace TangentPoints

variable {x : X ⟶ Spec (CommRingCat.of K)} {pt : Spec (CommRingCat.of K) ⟶ X}
variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

@[ext] theorem ext {v v' : TangentPoints x pt V} (h : v.1 = v'.1) : v = v' := Subtype.ext h

def map (φ : V →ₗ[K] W) (v : TangentPoints x pt V) : TangentPoints x pt W :=
  ⟨SquareZero.specMap K φ ≫ v.1, by rw [Category.assoc, v.2.1, SquareZero.specMap_toBase],
    by rw [SquareZero.basePoint_specMap_assoc, v.2.2]⟩

@[simp] theorem map_coe (φ : V →ₗ[K] W) (v : TangentPoints x pt V) :
    (v.map φ).1 = SquareZero.specMap K φ ≫ v.1 := rfl

end TangentPoints

end TangentPoints

namespace RelPicard

variable {K : Type u} [Field K] {C : Scheme.{u}}

def TrivialModDeformations (c : C ⟶ Spec (CommRingCat.of K))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] : Type (u + 1) :=
  { L : RigidifiedLineBundle c ε (SquareZero.toBase K V) //
      Nonempty ((L.pullbackAlong (SquareZero.basePointOver K V)).L ≅
        (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 (Spec (CommRingCat.of K)))).L) }

namespace TrivialModDeformations

variable {c : C ⟶ Spec (CommRingCat.of K)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

theorem postComp_specMapOver_basePointOver (φ : V →ₗ[K] W) :
    postComp (SquareZero.specMapOver K φ) (SquareZero.basePointOver K W) = SquareZero.basePointOver K V :=
  Subtype.ext (SquareZero.basePoint_specMap K φ)

def map (φ : V →ₗ[K] W) (L : TrivialModDeformations c ε V) : TrivialModDeformations c ε W :=
  ⟨L.1.pullbackAlong (SquareZero.specMapOver K φ),
    ⟨(Scheme.Modules.pullbackComp _ _).app L.1.L ≪≫
      (Scheme.Modules.pullbackCongr
        ((baseChangeSnd_comp c (SquareZero.specMapOver K φ) (SquareZero.basePointOver K W)).trans
          (by rw [postComp_specMapOver_basePointOver]))).app L.1.L ≪≫
      L.2.some⟩⟩

@[simp] theorem map_coe (φ : V →ₗ[K] W) (L : TrivialModDeformations c ε V) :
    (L.map φ).1 = L.1.pullbackAlong (SquareZero.specMapOver K φ) := rfl

end TrivialModDeformations

end RelPicard

end AlgebraicGeometry

end


