-- Prove2me | Definitions.Def_Mathlib_IsModuleTopology
-- name    : Mathlib_IsModuleTopology
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/acd3c00f-afcb-5922-885f-d82c4cb85923
-- title:
--   Module topologies: topological modules, scalar change, permanence properties
-- statement:
--   This module collects additions to the theory of the module topology. Two classes are introduced. First, [`IsTopologicalModule R M`](../def/Mathlib_IsModuleTopology.html#L10), for a ring $R$ with a topology and a topological $R$-module $M$, which simply bundles `ContinuousSMul R M` together with `ContinuousAdd M`; it is shown to be inherited along an inducing $R$-linear map ([`Topology.IsInducing.topologicalModule`](../def/Mathlib_IsModuleTopology.html#L14)), and instances are provided for submodules with the subspace topology and for products $\prod_i M_i$ with the product topology. Second, [`IsBiscalar R S f`](../def/Mathlib_IsModuleTopology.html#L37), a class on a map $f : A \to B$ between additive monoids each carrying both an $R$- and an $S$-module structure, asserting the two equations $f(r \cdot a) = r \cdot f(a)$ and $f(s \cdot a) = s \cdot f(a)$; from it, [`LinearMap.changeScalars`](../def/Mathlib_IsModuleTopology.html#L48), [`LinearEquiv.changeScalars`](../def/Mathlib_IsModuleTopology.html#L57), [`AlgHom.changeScalars`](../def/Mathlib_IsModuleTopology.html#L89) and [`AlgEquiv.changeScalars`](../def/Mathlib_IsModuleTopology.html#L98) re-read an $S$-linear (resp. $S$-algebra) map as an $S'$-linear (resp. $S'$-algebra) map with the same underlying function, and [`IsBiscalar.commutes`](../def/Mathlib_IsModuleTopology.html#L79) records that such an $f$ commutes with the structure maps from $S'$. Separately, [`AlgEquiv.extendScalars`](../def/Mathlib_IsModuleTopology.html#L69) turns an $A$-algebra equivalence $f : C \simeq_A D$, where $C$ is an algebra over an intermediate $A$-algebra $B$, into a $B$-algebra equivalence, $D$ being given the $B$-algebra structure transported along $f$ restricted to $B$.
--
--   The remaining declarations concern `IsModuleTopology`, the predicate that the given topology on $M$ coincides with the module topology `moduleTopology R M`; [`ModuleTopology.isModuleTopology`](../def/Mathlib_IsModuleTopology.html#L126) and [`ModuleTopology.iff`](../def/Mathlib_IsModuleTopology.html#L131) record the tautological instance and this characterisation. For a commutative topological ring $R$ and a module-topologised finite $R$-algebra $D$: multiplication is continuous and $D$ is a topological semiring, resp. topological ring (`continuous_mul'`, `continuous_mul`, `topologicalSemiring`, `Module.topologicalRing`), the underlying tool being continuity of an $R$-bilinear map on a finite free first factor. Further results: the module topology makes $M$ a topological module; for an $R$-algebra $S$ which is a topological ring, $S$ is a topological $R$-module exactly when $\mathrm{algebraMap}$ is continuous; comparison $\mathrm{moduleTopology}\,R\,M \le \mathrm{moduleTopology}\,S\,M$ and, when $S$ is a module-topologised finite $R$-algebra, equality of the two module topologies on an $S$-module $M$ with compatible $R$-action, hence `IsModuleTopology R M ↔ IsModuleTopology S M`; a criterion via a continuous open `algebraMap`; descent along linear quotient maps, open surjections and split continuous maps; automatic continuity of linear and algebra equivalences between module-topologised objects, including [`IsBiscalar`](../def/Mathlib_IsModuleTopology.html#L37) variants producing $A \simeq_L B$ and $A \simeq_A B$; Hausdorffness of free modules over a Hausdorff base with continuous addition and multiplication (and the field case); local compactness of finite modules over a locally compact topological ring; the homeomorphic coordinate isomorphism $R \simeq_L (\mathrm{Fin}\,(\dim_K R) \to K)$ for a finite-dimensional $K$-algebra; and second countability of finite modules over a second countable base.
--
--   **Relation to Mathlib.** Mathlib supplies `moduleTopology` and `IsModuleTopology`; this module adds further permanence and descent lemmas for them. The classes [`IsTopologicalModule`](../def/Mathlib_IsModuleTopology.html#L10) (a bundling of `ContinuousSMul` and `ContinuousAdd`, which Mathlib keeps separate) and [`IsBiscalar`](../def/Mathlib_IsModuleTopology.html#L37), together with the `changeScalars` constructions, are introduced here.
--
--   **Where it is used.** The module topology is the standard way to topologise finite algebras and their base changes — completions of number fields, finite-dimensional algebras over local fields and over the adeles, and tensor products $M \otimes_R A$ — so that they are automatically topological rings, Hausdorff, locally compact and second countable. These permanence properties are what make such objects usable as topological groups in the automorphic side of the argument.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean` — © 2024 Kevin Buzzard; authors: Kevin Buzzard, Pietro Monticone, Salvatore Mercuri, Matthew Jasper, Ruben Van de Velde, William Coram; `FLT/Mathlib/Algebra/Algebra/Tower.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard; `FLT/Deformations/ContinuousRepresentation/IsTopologicalModule.lean` — © 2025 Javier López-Contreras; authors: Javier López-Contreras). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_IsModuleTopology.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section IsTopologicalModuleDep

open Topology

variable (R : Type*) [Ring R] [TopologicalSpace R]
  (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M]

class IsTopologicalModule extends ContinuousSMul R M, ContinuousAdd M

variable [IsTopologicalModule R M]

protected theorem Topology.IsInducing.topologicalModule {F : Type*}
    (R : Type*) [Ring R] [TopologicalSpace R]
    {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalModule R M]
    {H : Type*} [AddCommGroup H] [Module R H] [TopologicalSpace H]
    [FunLike F H M] [LinearMapClass F R H M] (f : F) (hf : IsInducing ⇑f) :
    IsTopologicalModule R H where
  continuous_smul := (hf.continuousSMul continuous_id (by intro c x; exact map_smul f c x)).continuous_smul
  continuous_add := (hf.continuousAdd ..).continuous_add

instance Submodule.instIsTopologicalModuleSubtypeMem (S : Submodule R M) : IsTopologicalModule R S
    := IsInducing.subtypeVal.topologicalModule R S.subtypeL

instance Pi.instTopologicalModule {ι : Type*} (R : Type*) [Ring R] [TopologicalSpace R]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, IsTopologicalModule R (M i)] :
    IsTopologicalModule R ((i : ι) → M i) where
  continuous_smul := by apply continuous_smul
  continuous_add := by apply continuous_add

end IsTopologicalModuleDep

section

class IsBiscalar (R S : Type*) {A B : Type*} [Semiring R] [Semiring S] [AddCommMonoid A]
    [AddCommMonoid B] [Module R A] [Module R B] [Module S A] [Module S B] (f : A → B) where
  map_smul₁ : ∀ (r : R) (a : A), f (r • a) = r • f a
  map_smul₂ : ∀ (s : S) (a : A), f (s • a) = s • f a

section linear

variable {A B : Type*} (S' : Type*) {S : Type*}
    [Semiring S'] [Semiring S] [AddCommMonoid A] [AddCommMonoid B] [Module S A]
    [Module S B] [Module S' A] [Module S' B]

def LinearMap.changeScalars (f : A →ₗ[S] B) [IsBiscalar S S' f] :
    A →ₗ[S'] B where
  __ := f
  map_smul' s x := by simpa using IsBiscalar.map_smul₂ S s x

theorem LinearMap.changeScalars_apply (f : A →ₗ[S] B) [IsBiscalar S S' f] (a : A) :
    LinearMap.changeScalars S' f a = f a := by
  simp [changeScalars]

def LinearEquiv.changeScalars (f : A ≃ₗ[S] B) [IsBiscalar S S' f] :
    A ≃ₗ[S'] B where
  __ := LinearMap.changeScalars S' f.toLinearMap
  invFun := f.invFun
  left_inv (a : A) := by simp [LinearMap.changeScalars_apply]
  right_inv (b : B) := by simp [LinearMap.changeScalars_apply]

end linear

section algebra

@[simps! apply symm_apply]
def AlgEquiv.extendScalars {A C D : Type*} (B : Type*) [CommSemiring A] [CommSemiring C]
    [CommSemiring D] [Algebra A C] [Algebra A D] [CommSemiring B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] (f : C ≃ₐ[A] D) :
    letI := (f.toAlgHom.restrictDomain B).toRingHom.toAlgebra
    C ≃ₐ[B] D where
  __ := (f.toAlgHom.restrictDomain B).toRingHom.toAlgebra
  __ := f
  invFun := f.symm
  commutes' := fun _ => rfl

theorem IsBiscalar.commutes {S : Type*} (S' : Type*) {A B : Type*} [CommSemiring S']
    [CommSemiring S] [Semiring A] [Semiring B] [Algebra S' A] [Algebra S' B] [Algebra S A]
    [Algebra S B] (f : A →ₐ[S] B) [IsBiscalar S S' f] (s : S') :
    f (algebraMap S' A s) = algebraMap S' B s := by
  simpa [Algebra.algebraMap_eq_smul_one] using IsBiscalar.map_smul₂ (f := f) S s 1

variable {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B]

def AlgHom.changeScalars (f : A →ₐ[S] B) [IsBiscalar S S' f] :
    A →ₐ[S'] B where
  __ := f
  commutes' (r : _) := by simp [IsBiscalar.commutes]

theorem AlgHom.changeScalars_apply (f : A →ₐ[S] B) [IsBiscalar S S' f] (a : A) :
    changeScalars S' f a = f a := by
  simp [changeScalars]

def AlgEquiv.changeScalars (f : A ≃ₐ[S] B) [IsBiscalar S S' f.toAlgHom] :
    A ≃ₐ[S'] B where
  __ := AlgHom.changeScalars S' f.toAlgHom
  invFun := f.invFun
  left_inv (a : A) := by simp [AlgHom.changeScalars_apply]
  right_inv (b : B) := by simp [AlgHom.changeScalars_apply]
  commutes' := fun _ => by simp

end algebra

section diamond_checks

example {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) [IsBiscalar S S f] :
    AlgHom.changeScalars S f = f := rfl

example {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B] (f : A →ₐ[S] B) [IsBiscalar S S' f]
    [IsBiscalar S' S (AlgHom.changeScalars S' f)] :
    (AlgHom.changeScalars S' f).changeScalars S = f := rfl

end diamond_checks

end

section

theorem ModuleTopology.isModuleTopology (R : Type*) [TopologicalSpace R] (S : Type*) [Add S]
    [SMul R S] : @IsModuleTopology R _ S _ _ (moduleTopology R S) where
  __ := moduleTopology R S
  eq_moduleTopology' := rfl

lemma ModuleTopology.iff (R M : Type*) [Add M] [SMul R M] [TopologicalSpace R]
    [τ : TopologicalSpace M] : IsModuleTopology R M ↔ τ = moduleTopology R M :=
  ⟨fun m ↦ m.eq_moduleTopology', fun a ↦ { eq_moduleTopology' := a }⟩

namespace IsModuleTopology

open ModuleTopology

section semiring_bilinear

variable {R : Type*} [τR : TopologicalSpace R] [CommSemiring R]

variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommMonoid C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

theorem Module.continuous_bilinear_of_finite_free [IsTopologicalSemiring R] [Module.Finite R A]
    [Module.Free R A] (bil : A →ₗ[R] B →ₗ[R] C) :
    Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  let ι := Module.Free.ChooseBasisIndex R A
  let hι : Fintype ι := Module.Free.ChooseBasisIndex.fintype R A
  let b : Module.Basis ι R A := Module.Free.chooseBasis R A
  let elinear : A ≃ₗ[R] (ι → R) := b.equivFun
  let bil' : (ι → R) →ₗ[R] B →ₗ[R] C := bil.comp elinear.symm.toLinearMap
  have := continuous_bilinear_of_pi_fintype ι bil'
  have foo : (fun ab ↦ (bil ab.1) ab.2 : A × B → C) = (fun fb ↦ bil' fb.1 fb.2) ∘
    (fun ab ↦ (elinear ab.1, ab.2) : A × B → (ι → R) × B) := by
    ext ⟨a, b⟩
    simp [bil']
  rw [foo]
  apply Continuous.comp this
  apply Continuous.prodMk
  · exact continuous_of_linearMap (elinear.toLinearMap ∘ₗ (LinearMap.fst R A B))
  · fun_prop

end semiring_bilinear

section semiring_algebra

open scoped TensorProduct

variable (R) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

open scoped TensorProduct

@[continuity, fun_prop]
theorem continuous_mul'
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D] [TopologicalSpace D]
    [IsModuleTopology R D] : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) :=
  continuous_bilinear_of_finite_left (LinearMap.mul R D)

include R in
lemma topologicalSemiring : IsTopologicalSemiring D where
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul' R D

end semiring_algebra

section ring_algebra

variable (R) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

open scoped TensorProduct

include R in
@[continuity, fun_prop]
theorem continuous_mul : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) := by
  letI : TopologicalSpace (D ⊗[R] D) := moduleTopology R _
  haveI : IsModuleTopology R (D ⊗[R] D) := { eq_moduleTopology' := rfl }
  convert continuous_bilinear_of_finite_left <| (LinearMap.mul R D : D →ₗ[R] D →ₗ[R] D)
  exact (LinearMap.mul_apply' _ _).symm

include R in
lemma Module.topologicalRing : IsTopologicalRing D where
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul R D
  continuous_neg := continuous_neg R D

end ring_algebra

section algebra

variable (R S : Type*)
  [CommRing R] [TopologicalSpace R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]

lemma iff_Continuous_algebraMap :
    IsTopologicalModule R S ↔ Continuous (algebraMap R S) := by
  refine ⟨fun _ ↦ continuous_algebraMap R S, fun h ↦ ?_⟩
  have : Continuous (fun rs ↦ algebraMap R S rs.1 • rs.2 : R × S → S) := by fun_prop
  simp_rw [← algebra_compatible_smul S] at this
  have : ContinuousSMul R S := ⟨this⟩
  exact IsTopologicalModule.mk

end algebra

section trans

variable (R : Type*) [CommRing R] [TopologicalSpace R]

theorem isTopologicalModule
    (M : Type*) [AddCommGroup M] [TopologicalSpace M] [Module R M]
    [IsModuleTopology R M] : IsTopologicalModule R M where
      continuous_smul := eq_moduleTopology R M ▸ (continuousSMul R M).1
      continuous_add := eq_moduleTopology R M ▸ (continuousAdd R M).1

variable (S : Type*) [CommRing S] [TopologicalSpace S] [Algebra R S]

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

lemma _root_.Algebra.moduleTopology_le [IsTopologicalModule R S] :
    moduleTopology R M ≤ moduleTopology S M := by
  letI : TopologicalSpace M := moduleTopology S M
  haveI : ContinuousAdd M := continuousAdd S M
  have ⟨cts_smul⟩ : ContinuousSMul S M := continuousSMul S M
  suffices ContinuousSMul R M from _root_.moduleTopology_le R M
  constructor
  suffices Continuous (fun rm ↦ algebraMap R S rm.1 • rm.2 : R × M → M) by
    simpa [← algebra_compatible_smul S]
  fun_prop

lemma _root_.moduleTopology.trans [IsTopologicalRing R] [Module.Finite R S] [IsModuleTopology R S] :
    moduleTopology R M = moduleTopology S M := by
  have := IsModuleTopology.isTopologicalModule
  refine le_antisymm (Algebra.moduleTopology_le _ _ _) ?_
  letI : TopologicalSpace M := moduleTopology R M
  haveI : IsModuleTopology R M := isModuleTopology R M
  haveI : ContinuousAdd M := continuousAdd R M
  have ⟨cts_smul⟩ : ContinuousSMul R M := continuousSMul R M
  suffices ContinuousSMul S M from _root_.moduleTopology_le S M
  constructor
  let bil : S →ₗ[R] M →ₗ[R] M := {
    toFun s := {
      toFun m := s • m
      map_add' := DistribSMul.smul_add s
      map_smul' := smul_comm s
    }
    map_add' s t := by
      ext m
      exact Module.add_smul s t m
    map_smul' r s := by
      ext m
      exact IsScalarTower.smul_assoc r s m
  }
  exact continuous_bilinear_of_finite_left bil

lemma trans [IsTopologicalRing R] [Module.Finite R S] [IsModuleTopology R S]
    [τ : TopologicalSpace M] :
    IsModuleTopology R M ↔ IsModuleTopology S M := by
  simp [iff R M, iff S M, moduleTopology.trans R S]

end trans

section opensubring
variable (R S : Type*)
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra R S]

open scoped Topology in

theorem of_continuous_isOpenMap_algebraMap (hcont : Continuous (algebraMap R S))
    (hopen : IsOpenMap (algebraMap R S)) : IsModuleTopology R S where
  eq_moduleTopology' := by

    have : ContinuousSMul R S := continuousSMul_of_algebraMap R S hcont

    have hcont_id : Continuous[moduleTopology R S, _] id :=
      continuous_id_iff_le.2 <| moduleTopology_le _ _

    have hcont_alg : Continuous[_, moduleTopology R S] (Algebra.linearMap R S) :=

      letI := moduleTopology R S
      letI : ContinuousAdd S := ModuleTopology.continuousAdd _ _
      letI : ContinuousSMul R S := ModuleTopology.continuousSMul _ _
      IsModuleTopology.continuous_of_linearMap _

    have hopen_mpr {U : Set S} (h : IsOpen U) : IsOpen[moduleTopology R S] U :=
      @Continuous.isOpen_preimage S S (moduleTopology R S) _ id hcont_id U h

    have hopen_mp {U : Set S} (h : IsOpen[moduleTopology R S] U)
        (hUS : U ⊆ Set.range (algebraMap R S)) : IsOpen U :=
      Set.image_preimage_eq_of_subset hUS ▸ hopen _ <|
        @Continuous.isOpen_preimage R S _ (moduleTopology R S) _ hcont_alg U h

    rw [IsTopologicalRing.to_topologicalAddGroup.ext_iff <|

      @IsModuleTopology.topologicalAddGroup R _ _ S _ _ (moduleTopology R S) (isModuleTopology R S)]

    apply (nhds_basis_opens 0).ext (@nhds_basis_opens S (moduleTopology R S) 0)
    ·
      exact fun U hU => ⟨U, ⟨⟨hU.1, hopen_mpr hU.2⟩, by simp⟩⟩
    ·
      intro U hU

      refine ⟨Set.range (algebraMap R S) ∩ U, ⟨⟨⟨⟨0, by simp⟩, hU.1⟩, ?_⟩, by simp⟩⟩

      let hopen_range := hopen_mpr hopen.isOpen_range

      exact hopen_mp (@IsOpen.inter _ (moduleTopology R S) _ _ hopen_range hU.2) (by simp)

end opensubring

section quotientMap

variable {R M : Type*} [Ring R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  (N : Type*) [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]

theorem of_isQuotientMap (f : N →ₗ[R] M) (h : Topology.IsQuotientMap f) : IsModuleTopology R M := by
  rw [iff, eq_coinduced_of_surjective h.surjective, h.eq_coinduced]

variable [ContinuousAdd M] [ContinuousSMul R M]

theorem of_isOpenMap_surjective (f : N →ₗ[R] M) (h : IsOpenMap f) (hsurj : Function.Surjective f)
    : IsModuleTopology R M := by
  apply of_isQuotientMap N f
  refine IsOpenQuotientMap.isQuotientMap ⟨hsurj, continuous_of_linearMap f, h⟩

theorem of_inverse (f : N →ₗ[R] M) (g : M → N) (hc : Continuous g) (hi : Function.LeftInverse f g)
    : IsModuleTopology R M := by
  apply of_isQuotientMap N f
  exact Topology.IsQuotientMap.of_inverse hc (continuous_of_linearMap f) hi

end quotientMap

@[simps!]
def continuousLinearEquiv {A B R : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace R] [Semiring R] [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [IsModuleTopology R A] [IsModuleTopology R B]
    (e : A ≃ₗ[R] B) :
    A ≃L[R] B where
  toFun := e
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

def continuousLinearEquivOfIsBiscalar {A B : Type*} (S' : Type*) {S : Type*}
    [Semiring S'] [Semiring S] [AddCommMonoid A] [AddCommMonoid B] [Module S A]
    [Module S B] [Module S' A] [Module S' B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace S'] [IsModuleTopology S' A] [IsModuleTopology S' B] (e : A ≃ₗ[S] B)
    [IsBiscalar S S' e] :
    A ≃L[S] B where
  toLinearEquiv := e
  continuous_toFun := by
    change Continuous (e.changeScalars S')
    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (e.changeScalars S').symm
    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _

def continuousAlgEquivOfIsBiscalar {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S]
    [Algebra S A] [Algebra S B] [Algebra S' A] [Algebra S' B] [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace S'] [IsModuleTopology S' A]
    [IsModuleTopology S' B] (e : A ≃ₐ[S] B) [IsBiscalar S S' e.toAlgHom] :
    A ≃A[S] B where
  toAlgEquiv := e
  continuous_toFun := by

    change Continuous (e.changeScalars S').toLinearEquiv

    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (e.changeScalars S').toLinearEquiv.symm
    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _

@[simp]
theorem continuousAlgEquivOfIsBiscalar_apply {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S]
    [Algebra S A] [Algebra S B] [Algebra S' A] [Algebra S' B]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace S'] [IsModuleTopology S' A]
    [IsModuleTopology S' B] (e : A ≃ₐ[S] B) [IsBiscalar S S' e.toAlgHom] (a : A) :
    continuousAlgEquivOfIsBiscalar S' e a = e a :=
  rfl

def continuousAlgEquivOfAlgEquiv {A B R : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace R] [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [IsModuleTopology R A] [IsModuleTopology R B]
    (e : A ≃ₐ[R] B) :
    A ≃A[R] B where
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

theorem t2Space (R : Type*) {M : Type*} [Semiring R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [TopologicalSpace R] [TopologicalSpace M] [T2Space R]
    [ContinuousAdd R] [ContinuousMul R] [IsModuleTopology R M]
    : T2Space M := by
  have := IsModuleTopology.topologicalAddGroup R M
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
  let f := (Module.Free.chooseBasis R M).repr |>.toLinearMap
  let g : (Module.Free.ChooseBasisIndex R M →₀ R) →ₗ[R] (Module.Free.ChooseBasisIndex R M → R) := {
    __ := Finsupp.coeFnAddHom
    map_smul' _ _ := rfl
  }
  suffices hpre : (g.comp f) ⁻¹' {0} = {0}  by
    rw [← hpre]
    apply IsClosed.preimage <| IsModuleTopology.continuous_of_linearMap (g.comp f)
    exact isClosed_singleton
  ext x
  simp [map_eq_zero_iff g DFunLike.coe_injective,
    map_eq_zero_iff f (Module.Free.chooseBasis R M).repr.injective]

theorem t2Space' {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [TopologicalSpace K] [TopologicalSpace V] [T2Space K]
    [ContinuousAdd K] [ContinuousMul K] [mt : IsModuleTopology K V]
    : T2Space V := by
  apply t2Space (R := K)

section locally_compact

variable (R : Type*) [τR : TopologicalSpace R] [Ring R] [IsTopologicalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]

theorem locallyCompactSpaceOfFinite [LocallyCompactSpace R] [Module.Finite R M] :
    LocallyCompactSpace M := by

  obtain ⟨n, φ, h⟩ := Module.Finite.exists_fin (R := R) (M := M)

  exact IsOpenQuotientMap.locallyCompactSpace <|

    AddMonoidHom.isOpenQuotientMap_of_isQuotientMap <|

    isQuotientMap_of_surjective <|
    LinearMap.range_eq_top.mp <|
    h ▸ Fintype.range_linearCombination R φ

end locally_compact

section ModuleFinite

@[simps!]
noncomputable
def Module.Basis.equivFun_homeo (K R : Type*) [Field K] [Ring R] [Module K R]
    [Module.Finite K R] [TopologicalSpace K] [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalRing K] [IsModuleTopology K R] : R ≃L[K] (Fin (Module.finrank K R) → K) where
  __ := Module.Basis.equivFun (Module.finBasisOfFinrankEq K R (rfl))
  continuous_toFun :=
    IsModuleTopology.continuous_of_linearMap
      (Module.Basis.equivFun (Module.finBasisOfFinrankEq K R (rfl))).toLinearMap
  continuous_invFun :=
    IsModuleTopology.continuous_of_linearMap
      (Module.Basis.equivFun (Module.finBasisOfFinrankEq K R (rfl))).symm.toLinearMap

end ModuleFinite

section SecondCountableTopology

lemma _root_.Module.Finite.secondCountabletopology (R M : Type*)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [TopologicalSpace M]
    [IsModuleTopology R M] : SecondCountableTopology M := by
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
  have := isQuotientMap_of_surjective hφ
  apply Topology.IsQuotientMap.secondCountableTopology <| isQuotientMap_of_surjective hφ
  exact isOpenMap_of_surjective hφ

end SecondCountableTopology

end IsModuleTopology

end


