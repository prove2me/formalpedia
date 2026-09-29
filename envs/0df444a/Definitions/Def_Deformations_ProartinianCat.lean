-- Prove2me | Definitions.Def_Deformations_ProartinianCat
-- name    : Deformations_ProartinianCat
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/7f115e9b-1a82-5fdb-a72c-fc2c68520ad7
-- title:
--   The category of local pro-Artinian O-algebras
-- statement:
--   Over a commutative ring $\mathcal{O}$, the class [`Deformation.IsLocalProartinianAlgebra 𝓞 R`](../def/Deformations_ProartinianCat.html#L15) is imposed on a commutative ring $R$ carrying a topology and an $\mathcal{O}$-algebra structure; it bundles: $R$ is a topological ring and a local ring; [`IsProartinian R`](../def/Deformations_IsProartinian.html#L185), i.e. the topology is linear (a basis of neighbourhoods of $0$ by ideals), $T_0$, complete for the right uniformity, and $R/I$ is Artinian for every open ideal $I$; the structure map $\mathcal{O}\to R$ is a local homomorphism; and [`IsResidueAlgebra 𝓞 R`](../def/Deformations_IsResidueAlgebra.html#L15), i.e. $\mathcal{O}\to R/\mathfrak{m}_R$ is surjective. Two unnamed facts are recorded: such an $R$ forces $\mathcal{O}$ to be local, and if $\mathcal{O}$ is local with the $\mathfrak{m}_{\mathcal{O}}$-adic topology then $\mathcal{O}\to R$ is continuous.
--
--   [`Deformation.ProartinianCat 𝓞`](../def/Deformations_ProartinianCat.html#L44) is the structure bundling a carrier type in a fixed universe with these data. Morphisms `Hom A B` wrap the continuous $\mathcal{O}$-algebra homomorphisms $A \to_A[\mathcal{O}] B$, with identity and composition giving the category instance; every morphism is automatically local. The constructors `of`, `ofHom` and the lemmas `coe_of`, `hom_id`, `hom_comp`, `hom_ext`, `ofHom_comp` and companions relate bundled objects and morphisms to their underlying data; `ofEquiv` turns a continuous $\mathcal{O}$-algebra equivalence into a categorical isomorphism and [`CategoryTheory.Iso.toContinuousAlgEquiv`](../def/Deformations_ProartinianCat.html#L141) goes back.
--
--   Two distinguished objects are constructed. When $\mathcal{O}$ is local, Noetherian, $\mathfrak{m}_{\mathcal{O}}$-adically complete with finite residue field, `self` is $\mathcal{O}$ with its adic topology; `fromSelf` is the structure map, the hom-set out of `self` is a singleton, and `isInitialSelf` exhibits it as initial. When $\mathcal{O}$ is local, `residueField` is $\mathcal{O}/\mathfrak{m}_{\mathcal{O}}$ with the discrete topology; `toResidueField R` is $R \to R/\mathfrak{m}_R$ followed by the inverse of the induced isomorphism $\mathcal{O}/\mathfrak{m}_{\mathcal{O}} \cong R/\mathfrak{m}_R$. It is surjective with kernel $\mathfrak{m}_R$; `to_residueField_apply` shows any morphism to `residueField` sends $r$ to the residue of a chosen $a\in\mathcal{O}$ with $r-a\in\mathfrak{m}_R$, whence uniqueness and `isTerminalResidueField`.
--
--   **Relation to Mathlib.** Mathlib has no category of pro-Artinian local algebras; [`IsProartinian`](../def/Deformations_IsProartinian.html#L185), [`IsResidueAlgebra`](../def/Deformations_IsResidueAlgebra.html#L15) and [`IsLocalRing.IsAdicTopology`](../def/Patching_SystemTypes.html#L17) are the project's own predicates. The packaging (a carrier-plus-instances structure with `of`, `ofHom`, a wrapped `Hom` type and coercion lemmas) follows Mathlib's conventions for bundled concrete categories, and the morphisms are Mathlib's continuous algebra homomorphisms `→A[𝓞]`.
--
--   **Where it is used.** This is the base category on which deformation and lifting functors of a residual representation $\bar\rho \colon G \to \mathrm{GL}_n(k)$ are defined, so that representability statements for universal deformation rings can be formulated; the initial object $\mathcal{O}$ and the terminal residue field provide the coefficient ring and the reduction used throughout the deformation-theoretic input to modularity lifting.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Deformations/Categories.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Pietro Monticone). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_ProartinianCat.lean

import Mathlib
import Definitions.Def_Deformations_IsProartinian
import Definitions.Def_Deformations_IsResidueAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Function Limits IsLocalRing

namespace Deformation

variable (𝓞 : Type u) [CommRing 𝓞]

class IsLocalProartinianAlgebra
    (R : Type u) [CommRing R] [TopologicalSpace R] [Algebra 𝓞 R] : Prop extends
  IsTopologicalRing R, IsLocalRing R, IsProartinian R,
  IsLocalHom (algebraMap 𝓞 R), IsResidueAlgebra 𝓞 R

section 𝓞_is_local

example (𝓞 : Type u) [CommRing 𝓞]
    (R : Type u) [CommRing R] [TopologicalSpace R]
    [Algebra 𝓞 R] [IsLocalProartinianAlgebra 𝓞 R] : IsLocalRing 𝓞 := by
  let φ : 𝓞 →+* R := algebraMap 𝓞 R
  have hφ : IsLocalHom φ := IsLocalProartinianAlgebra.toIsLocalHom
  have hR : Nontrivial R := IsLocalRing.toNontrivial
  haveI : Nontrivial 𝓞 := RingHom.domain_nontrivial φ
  apply of_nonunits_add
  intros a b ha hb
  rw [mem_nonunits_iff, ← isUnit_map_iff φ, ← mem_nonunits_iff] at ha hb ⊢
  rw [map_add]

  exact Ideal.add_mem (IsLocalRing.maximalIdeal R) ha hb

example (𝓞 : Type u) [CommRing 𝓞] [TopologicalSpace 𝓞] [IsTopologicalRing 𝓞]
    [IsLocalRing 𝓞] [IsAdicTopology 𝓞]
    (R : Type u) [CommRing R] [TopologicalSpace R]
    [Algebra 𝓞 R] [IsLocalProartinianAlgebra 𝓞 R] : Continuous (algebraMap 𝓞 R) :=
  isContinuous_of_isProartinian_of_isLocalHom _

end 𝓞_is_local

structure ProartinianCat where

  carrier : Type u

  [commRing : CommRing carrier]

  [topologicalSpace : TopologicalSpace carrier]

  [algebra : Algebra 𝓞 carrier]
  [isLocalProartinianAlgebra : IsLocalProartinianAlgebra 𝓞 carrier]

local notation3:max "𝓒" 𝓞 => ProartinianCat 𝓞

namespace ProartinianCat

attribute [instance] commRing algebra topologicalSpace isLocalProartinianAlgebra

initialize_simps_projections ProartinianCat (-commRing, -algebra, -topologicalSpace)

instance : CoeSort (ProartinianCat 𝓞) (Type u) := ⟨carrier⟩

attribute [coe] ProartinianCat.carrier

abbrev of (X : Type u) [CommRing X] [Algebra 𝓞 X]
    [TopologicalSpace X] [IsLocalProartinianAlgebra 𝓞 X] :
    ProartinianCat 𝓞 :=
  ⟨X⟩

lemma coe_of (X : Type u) [CommRing X] [Algebra 𝓞 X] [TopologicalSpace X]
    [IsLocalProartinianAlgebra 𝓞 X] :
    of 𝓞 X = X := rfl

variable {𝓞} in

@[ext]
structure Hom (A B : ProartinianCat 𝓞) where

  hom : A →A[𝓞] B

instance : Category (ProartinianCat 𝓞) where
  Hom A B := Hom A B
  id A := ⟨ContinuousAlgHom.id 𝓞 A⟩
  comp f g := ⟨g.hom.comp f.hom⟩

instance (A B : ProartinianCat 𝓞) (f : A ⟶ B) : IsLocalHom f.hom := by
  convert isLocalHom_of_isContinuous_of_isProartinian f.hom.toRingHom f.hom.cont
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

variable {𝓞} in

abbrev ofHom {A B : Type u}
    [CommRing A] [Algebra 𝓞 A] [TopologicalSpace A] [IsLocalProartinianAlgebra 𝓞 A]
    [CommRing B] [Algebra 𝓞 B] [TopologicalSpace B] [IsLocalProartinianAlgebra 𝓞 B]
    (f : A →A[𝓞] B) :
    of 𝓞 A ⟶ of 𝓞 B := ⟨f⟩

variable {𝓞}

variable {X Y Z : Type u}
  [CommRing X] [Algebra 𝓞 X] [TopologicalSpace X] [IsLocalProartinianAlgebra 𝓞 X]
  [CommRing Y] [Algebra 𝓞 Y] [TopologicalSpace Y] [IsLocalProartinianAlgebra 𝓞 Y]
  [CommRing Z] [Algebra 𝓞 Z] [TopologicalSpace Z] [IsLocalProartinianAlgebra 𝓞 Z]

variable {A B C : ProartinianCat 𝓞}

@[simp]
lemma hom_id : (𝟙 A :).hom = ContinuousAlgHom.id 𝓞 A := rfl

lemma id_apply (x) : (𝟙 A :).hom x = x := rfl

@[simp]
lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (x) : (f ≫ g).hom x = g.hom (f.hom x) := rfl

@[ext]
lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

lemma hom_ofHom (f : X →A[𝓞] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom (f : A ⟶ B) : ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id : ofHom (ContinuousAlgHom.id 𝓞 X) = 𝟙 (of 𝓞 X) := rfl

@[simp]
lemma ofHom_comp (f : X →A[𝓞] Y) (g : Y →A[𝓞] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[simps]
def ofEquiv (e : X ≃A[𝓞] Y) : of 𝓞 X ≅ of 𝓞 Y where
  hom := ofHom (e : X →A[𝓞] Y)
  inv := ofHom (e.symm : Y →A[𝓞] X)

def _root_.CategoryTheory.Iso.toContinuousAlgEquiv (i : A ≅ B) : A ≃A[𝓞] B where
  __ := i.hom.hom
  invFun := i.inv.hom
  left_inv _ := by simp [← comp_apply]
  right_inv _ := by simp [← comp_apply]
  continuous_toFun := i.hom.hom.cont
  continuous_invFun := i.inv.hom.2

section self

variable [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
  [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]

def self : 𝓒 𝓞 where
  carrier := 𝓞
  topologicalSpace := (maximalIdeal 𝓞).adicTopology
  isLocalProartinianAlgebra :=
    letI := (maximalIdeal 𝓞).adicTopology
    letI : IsTopologicalRing 𝓞 := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
    letI : CompactSpace 𝓞 := compactSpace_of_finite_residueField
    ⟨⟩

instance : IsAdicTopology (self (𝓞 := 𝓞)) := ⟨rfl⟩

def fromSelf (R : ProartinianCat 𝓞) : self ⟶ R where
  hom :=
    letI := (maximalIdeal 𝓞).adicTopology
    letI : IsTopologicalRing 𝓞 := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
    letI : IsAdicTopology 𝓞 := ⟨rfl⟩
    ⟨Algebra.ofId _ _, isContinuous_of_isProartinian_of_isLocalHom (algebraMap 𝓞 R)⟩

instance (R : ProartinianCat 𝓞) : Unique (self ⟶ R) := by
  refine ⟨⟨fromSelf R⟩, fun f ↦ ?_⟩
  ext : 1
  apply ContinuousAlgHom.coe_inj.mp
  ext

def isInitialSelf : IsInitial (self (𝓞 := 𝓞)) := .ofUnique _

end self

section residueField

variable [IsLocalRing 𝓞]

set_option backward.isDefEq.respectTransparency false in

def residueField : 𝓒 𝓞 where
  carrier := ResidueField 𝓞
  topologicalSpace := ⊥
  isLocalProartinianAlgebra :=
    letI : TopologicalSpace (ResidueField 𝓞) := ⊥
    letI : DiscreteTopology (ResidueField 𝓞) := ⟨rfl⟩
    letI : IsResidueAlgebra 𝓞 (ResidueField 𝓞) := by delta ResidueField; infer_instance
    ⟨⟩

instance : DiscreteTopology (residueField (𝓞 := 𝓞)) := ⟨rfl⟩

noncomputable
instance : Field (residueField (𝓞 := 𝓞)) := inferInstanceAs (Field (ResidueField 𝓞))

set_option backward.isDefEq.respectTransparency false in

noncomputable
def toResidueField (R : ProartinianCat 𝓞) : R ⟶ residueField where
  hom := ⟨(IsResidueAlgebra.algEquiv 𝓞 R).symm.toAlgHom.comp (IsScalarTower.toAlgHom 𝓞 R _), by
    refine (RingHom.continuous_iff_isOpen_ker (β := residueField) (f := AlgHom.toRingHom _)).mpr ?_
    dsimp [residueField]
    rw [AlgHom.comp_toRingHom, RingHom.ker_comp_of_injective]
    · simp only [IsScalarTower.coe_toAlgHom, ResidueField.algebraMap_eq, residue]
      rw [Ideal.mk_ker]
      exact isOpen_maximalIdeal_of_isProartinian
    · exact (IsResidueAlgebra.algEquiv 𝓞 R).symm.injective⟩

lemma toResidueField_surjective (R : ProartinianCat 𝓞) :
    Function.Surjective (toResidueField R).hom :=
  (IsResidueAlgebra.algEquiv 𝓞 R).symm.surjective.comp Ideal.Quotient.mk_surjective

lemma ker_toResidueField (R : ProartinianCat 𝓞) :
    RingHom.ker (toResidueField R).hom = maximalIdeal R :=
  (RingHom.ker_comp_of_injective _ (f := (IsResidueAlgebra.algEquiv 𝓞 R).symm.toRingHom)
    (IsResidueAlgebra.algEquiv 𝓞 R).symm.injective).trans Ideal.mk_ker

lemma to_residueField_apply {R : 𝓒 𝓞} (f : R ⟶ residueField) (r : R.carrier) :
    f.hom r = residue _ (IsResidueAlgebra.preimage 𝓞 r)  := by
  trans f.hom (algebraMap _ _ (IsResidueAlgebra.preimage 𝓞 r))
  · rw [← sub_eq_zero, ← map_sub, ← not_ne_iff,
      ← @isUnit_iff_ne_zero _ _ (f.hom (r - (algebraMap 𝓞 ↑R) (IsResidueAlgebra.preimage 𝓞 r)))]
    change ¬IsUnit (f.hom.toRingHom _)
    rw [isUnit_map_iff f.hom.toRingHom, ← mem_nonunits_iff, ← mem_maximalIdeal]
    exact IsResidueAlgebra.preimage_spec _ _
  · erw [AlgHom.commutes]; rfl

noncomputable
instance (R : ProartinianCat 𝓞) : Unique (R ⟶ residueField) := by
  refine ⟨⟨toResidueField R⟩, fun f ↦ ?_⟩
  ext
  simp [to_residueField_apply]

noncomputable
def isTerminalResidueField : IsTerminal (residueField (𝓞 := 𝓞)) := .ofUnique _

end residueField

end ProartinianCat

end Deformation


