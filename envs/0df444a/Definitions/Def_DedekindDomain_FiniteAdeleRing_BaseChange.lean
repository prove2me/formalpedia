-- Prove2me | Definitions.Def_DedekindDomain_FiniteAdeleRing_BaseChange
-- name    : DedekindDomain_FiniteAdeleRing_BaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/bcb378b7-4b01-5597-b740-def200c51d36
-- title:
--   Finite adele rings: base change along an AKLB extension
-- statement:
--   The module is organised in three layers. First, [`ContinuousSemialgHom φ A B`](../def/DedekindDomain_FiniteAdeleRing_BaseChange.html#L10) (notation `A →SA[φ] B`) is a semialgebra homomorphism along a ring map $\varphi : R \to S$ — additive, multiplicative, unital, and satisfying $\psi(r \cdot a) = \varphi(r) \cdot \psi(a)$ — together with a continuity field; the accompanying class [`ContinuousSemialgHomClass`](../def/DedekindDomain_FiniteAdeleRing_BaseChange.html#L22), the `FunLike` and coercion instances, [`ContinuousSemialgHom.commutes`](../def/DedekindDomain_FiniteAdeleRing_BaseChange.html#L79) ($\psi \circ \mathrm{algebraMap} = \mathrm{algebraMap} \circ \varphi$), and the products `prod`, `prodMap` complete the bundled-morphism API. Second, for a family of rings $R_i$ with subring-like subobjects $B_i$ and modules $M_i$ with subgroups $C_i$ stable under $B_i$, the restricted product $\prod'_i (R_i,B_i)$ acts componentwise on $\prod'_i (M_i,C_i)$, making the latter a module over the former; a linear map between such restricted products is shown to be determined by its components $M_i \to M_{2,i}$ (`linearMap_component`, obtained by evaluating at `single`), from which openness criteria (`isOpenMap_linearMap_of_surjective`), the identification $\prod'_i (n \to R_i, \ \prod_n B_i) \cong n \to \prod'_i(R_i,B_i)$ as a continuous linear equivalence, and the statement that a finitely generated restricted-product module carries the module topology ([`RestrictedProduct.isModuleTopology`](../def/DedekindDomain_FiniteAdeleRing_BaseChange.html#L285)) are derived. The classes [`Pi.FiberwiseSMul`](../def/DedekindDomain_FiniteAdeleRing_BaseChange.html#L312), [`Prod.IsProdSMul`](../def/DedekindDomain_FiniteAdeleRing_BaseChange.html#L336) and [`RestrictedProduct.FiberwiseSMul`](../def/DedekindDomain_FiniteAdeleRing_BaseChange.html#L349) record that a given scalar action on a product, a binary product, or a restricted product is computed coordinatewise along a map of index sets. Third, in the AKLB situation ($A$ a Dedekind domain with fraction field $K$, $B$ a Dedekind domain finite over $A$ with fraction field $L$, compatible towers), `mapRingHom` and `mapSemialgHom` assemble the local maps $K_v \to L_w$ for $w$ above $v$ into a continuous semialgebra homomorphism $\mathbb{A}^f_K \to \mathbb{A}^f_L$ along $K \to L$. Under a fixed $\mathbb{A}^f_K$-algebra structure on $\mathbb{A}^f_L$ whose action is fibrewise (`ComapFiberwiseSMul`) and with $L/K$ finite, a chain of linear equivalences $L \otimes_K \mathbb{A}^f_K \cong B \otimes_A \mathbb{A}^f_K \cong \prod'_v (B \otimes_A K_v) \cong \prod'_v \prod_{w \mid v} L_w \cong \mathbb{A}^f_L$ yields bijectivity of the base-changed map and hence the algebra isomorphisms `baseChangeAlgEquiv` (over $L$) and `baseChangeAdeleAlgEquiv` (over $\mathbb{A}^f_K$); $\mathbb{A}^f_L$ is then a finite $\mathbb{A}^f_K$-module carrying the module topology, and the isomorphisms are upgraded to continuous algebra isomorphisms `baseChangeAdeleContinuousAlgEquiv` and `baseChangeContinuousAlgEquiv`.
--
--   **Relation to Mathlib.** Mathlib supplies [`SemialgHom`](../def/Mathlib_Algebra_Algebra_Hom.html#L11), the restricted product `Πʳ` and `IsDedekindDomain.FiniteAdeleRing`; the continuous variant [`ContinuousSemialgHom`](../def/DedekindDomain_FiniteAdeleRing_BaseChange.html#L10) with its morphism class, the module structure of a restricted product of modules over a restricted product of rings, and the adelic base-change equivalences are the project's own additions.
--
--   **Where it is used.** The identification $L \otimes_K \mathbb{A}^f_K \cong \mathbb{A}^f_L$, as a topological algebra isomorphism over both $L$ and $\mathbb{A}^f_K$, is what allows adelic automorphic objects over a base field to be compared with those over a finite extension, as needed when automorphic forms on quaternion algebras over totally real fields are set up in the modularity-lifting part of the argument.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file: `FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean` — commit 8387d589 (2026-05-27); © 2025 Kevin Buzzard; authors: Kevin Buzzard, Matthew Jasper (see §5); `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Module.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper; `FLT/Mathlib/Topology/Algebra/Algebra/Hom.lean` — © 2026 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard; `FLT/Mathlib/LinearAlgebra/Pi.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard; `FLT/Mathlib/Algebra/Algebra/Hom.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri; `FLT/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_DedekindDomain_FiniteAdeleRing_BaseChange.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_DedekindDomain_FiniteAdeleRing_TensorRestrictedProduct
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxSynthPendingDepth 3
set_option Elab.async false

/-- A `SemialgHom` (i.e., `ψ` such that `ψ (r • a) = φ r • ψ a` for some `φ : R →+* S`) that
is also continuous. -/
structure ContinuousSemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (A B : Type*) [TopologicalSpace A] [TopologicalSpace B]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends SemialgHom φ A B where
  continuous_toFun : Continuous toFun

@[inherit_doc ContinuousSemialgHom]
infixr:25 " →SA " => ContinuousSemialgHom _

@[inherit_doc]
notation:25 A " →SA[" φ:25 "] " B:0 => ContinuousSemialgHom φ A B

class ContinuousSemialgHomClass (F : Type*) {R S : outParam Type*}
    [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [TopologicalSpace A] [TopologicalSpace B]
    [FunLike F A B] extends SemialgHomClass F φ A B where continuous_toFun (f : F) : Continuous f

namespace ContinuousSemialgHom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [TopologicalSpace A] [TopologicalSpace B]

instance instFunLike : FunLike (A →SA[φ] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

instance : CoeOut (A →SA[φ] B) (A →ₛₐ[φ] B) :=
  ⟨fun f => f.toSemialgHom⟩

variable (F : Type*) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [TopologicalSpace A] [TopologicalSpace B] [ContinuousSemialgHomClass F φ A B]

instance : ContinuousSemialgHomClass (A →SA[φ] B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero
  continuous_toFun ψ := ψ.continuous_toFun

variable {F} {φ} {A} {B} in

def _root_.ContinuousSemialgHomClass.toContinuousSemialgHom (f : F) : A →SA[φ] B :=
  { (f : A →ₛₐ[φ] B) with continuous_toFun := ContinuousSemialgHomClass.continuous_toFun f }

instance : CoeTC F (A →SA[φ] B) :=
  ⟨ContinuousSemialgHomClass.toContinuousSemialgHom⟩

@[simp]
theorem coe_coe (f : F) : ⇑(f : A →SA[φ] B) = f :=
  rfl

theorem toSemialgHom_eq_coe (f : A →SA[φ] B) : f.toSemialgHom = f :=
  rfl

@[simp]
theorem toLinearMap_eq_coe (f : A →SA[φ] B) : f.toLinearMap = f := by
  rfl

@[simp]
theorem toRingHom_eq_coe (f : A →SA[φ] B) : f.toRingHom = f :=
  rfl

theorem commutes (ψ : A →SA[φ] B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) :=
  ψ.toSemialgHom.commutes r

def prod {C : Type*} [Semiring C] [Algebra S C] [TopologicalSpace C] (f : A →SA[φ] B)
    (g : A →SA[φ] C) :
    A →SA[φ] B × C where
  __ := f.toSemialgHom.prod g.toSemialgHom
  continuous_toFun := f.continuous_toFun.prodMk g.continuous_toFun

variable {φ A B} in

def prodMap {C D : Type*} [Semiring C] [Semiring D] [Algebra S C] [Algebra S D]
    [TopologicalSpace C] [TopologicalSpace D] [Algebra R B] (f : A →SA[φ] C) (g : B →SA[φ] D) :
    A × B →SA[φ] C × D where
  __ := SemialgHom.prodMap f g
  continuous_toFun := Continuous.prodMap f.continuous_toFun g.continuous_toFun

end ContinuousSemialgHom

section

namespace RestrictedProduct

variable {ι : Type*}
variable {R : ι → Type*} [Π i, Ring (R i)]
variable {S : ι → Type*}
variable [Π i, SetLike (S i) (R i)] [∀ i, SubringClass (S i) (R i)]
variable {B : Π i, S i}
variable {ℱ : Filter ι}

variable {M : ι → Type*} [Π i, AddCommGroup (M i)] [Π i, Module (R i) (M i)]
variable {N : ι → Type*}
variable [Π i, SetLike (N i) (M i)] [∀ i, AddSubgroupClass (N i) (M i)]
variable [∀ i, SMulMemClass (N i) (B i) (M i)]
variable {C : Π i, N i}

instance : SMul (Πʳ i, [R i, B i]_[ℱ]) (Πʳ i, [M i, C i]_[ℱ]) where
  smul r m := ⟨fun i ↦ (r i) • (m i), by
    filter_upwards [r.prop, m.prop] with i hr hm using SMulMemClass.smul_mem ⟨r i, hr⟩ hm⟩

omit [Π i, AddSubgroupClass (N i) (M i)] in
@[simp]
lemma smul_apply' (r : Πʳ i, [R i, B i]_[ℱ]) (m : Πʳ i, [M i, C i]_[ℱ]) (i : ι) :
    (r • m) i = r i • m i :=
  rfl

instance instModuleCoe_fLT : Module (Πʳ i, [R i, B i]_[ℱ]) (Πʳ i, [M i, C i]_[ℱ]) where
  zero_smul m := by ext; simp
  smul_zero r := by ext; simp
  one_smul m := by ext; simp
  add_smul r s m:= by ext; simp [add_smul]
  smul_add r m n := by ext; simp
  mul_smul r s m := by ext; simp [mul_smul]

@[simp]
lemma single_smul [DecidableEq ι] (i : ι) (r : R i) (m : Πʳ i, [M i, C i]) :
    single B i r • m = single C i (r • m i) := by
  ext j
  obtain (rfl | hi) := em (i = j)
  · simp
  · simp [single_eq_of_ne' _ _ hi]

@[simp]
lemma smul_single [DecidableEq ι] (i : ι) (r : Πʳ i, [R i, B i]) (m : M i) :
    r • single C i m = single C i (r i • m) := by
  ext j
  obtain (rfl | hi) := em (i = j)
  · simp
  · simp [single_eq_of_ne' _ _ hi]

lemma single_eq_smul [DecidableEq ι] (i : ι) (m : Πʳ i, [M i, C i]) :
    single B i 1 • m = single C i (m i) := by
  simp

variable {M₂ : ι → Type*} [Π i, AddCommGroup (M₂ i)] [Π i, Module (R i) (M₂ i)]
variable {N₂ : ι → Type*}
variable [Π i, SetLike (N₂ i) (M₂ i)] [∀ i, AddSubgroupClass (N₂ i) (M₂ i)]
variable [∀ i, SMulMemClass (N₂ i) (B i) (M₂ i)]
variable {C₂ : Π i, N₂ i}

section components

variable [DecidableEq ι]

noncomputable def linearMap_component
    (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i]) (i : ι) : M i →ₗ[R i] M₂ i where
  toFun x :=
    f (single C i x) i
  map_add' x y := by
    simp [single_add]
  map_smul' r m := by
    let r' := single B i r
    have hr : r = r' i := by simp [r']
    rw [hr, ← smul_single, map_smul, smul_apply', RingHom.id_apply]

lemma linearMap_component_apply (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i])
    (i : ι) (x : M i) : linearMap_component f i x = f (single C i x) i :=
  rfl

lemma linearMap_apply_eq_component (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i])
    (x : Πʳ i, [M i, C i]) (i : ι) : f x i = (linearMap_component f i) (x i):= by
  rw [linearMap_component_apply, ← single_eq_smul, map_smul, single_smul, single_eq_same, one_smul]

end components

variable [Π i, TopologicalSpace (R i)] [Π i, TopologicalSpace (M i)]

section continuous_smul

variable [∀ i, ContinuousSMul (R i) (M i)] (T : Set ι)

open scoped Filter in
instance : ContinuousSMul (Πʳ i, [R i, B i]_[𝓟 T]) (Πʳ i, [M i, C i]_[𝓟 T]) :=
  isEmbedding_coe_of_principal.continuousSMul isEmbedding_coe_of_principal.continuous
    (fun {c x} ↦ by ext; rfl)

variable [hBopen : Fact (∀ i, IsOpen (B i : Set (R i)))]
variable [hCopen : Fact (∀ i, IsOpen (C i : Set (M i)))]

instance [∀ i, ContinuousSMul (R i) (M i)] :
    ContinuousSMul (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i]) where
  continuous_smul := by
    rw [continuous_dom_prod hBopen.elim hCopen.elim]
    exact fun S hS ↦ (continuous_inclusion hS).comp continuous_smul

end continuous_smul

section components

variable [Π i, TopologicalSpace (M₂ i)]

omit [(i : ι) → TopologicalSpace (R i)] in
theorem isOpenMap_linearMap_of_surjective [DecidableEq ι]
    (hCopen : ∀ i, IsOpen (C i : Set (M i)))
    (hCopen₂ : ∀ i, IsOpen (C₂ i : Set (M₂ i)))
    (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i])
    (hf : ∀ i, IsOpenMap (linearMap_component f i))
    (hsurj : ∀ᶠ i in Filter.cofinite, Set.SurjOn (linearMap_component f i) (C i) (C₂ i)) :
    IsOpenMap f := by
  apply RestrictedProduct.isOpenMap_of_open_components hCopen hCopen₂ f
    (fun i ↦ linearMap_component f i) (linearMap_apply_eq_component f) hf hsurj

end components

section free_topology

variable (n : Type*)

variable (B) in

def piSubringSubmodule (i : ι) : Submodule (B i) (n → R i) :=
  Submodule.pi Set.univ fun (_ : n) ↦ Subring.toSubmodule (Subring.ofClass (B i))

def _root_.LinearEquiv.restrictedProductPi [Fintype n] :
    Πʳ i, [n → R i, piSubringSubmodule B n i]_[ℱ] ≃ₗ[Πʳ i, [R i, B i]_[ℱ]]
      n → Πʳ i, [R i, B i]_[ℱ] where
  toFun x j := map (fun i y ↦ y j)
    (by
      filter_upwards with i r hr
      rw [piSubringSubmodule, Submodule.coe_pi, Set.mem_univ_pi] at hr
      exact hr j)
    x
  invFun x := ⟨fun i j ↦ x j i, by
    have h := fun j ↦ (x j).eventually
    simp [piSubringSubmodule]
    exact h⟩
  map_add' x y := rfl
  map_smul' x y := rfl

lemma isOpen_piSubringSubmodule [Finite n] (hOpen : ∀ i, IsOpen (B i : Set (R i))) (i : ι) :
    IsOpen (SetLike.coe <| piSubringSubmodule B n i) := by
  rw [piSubringSubmodule, Submodule.coe_pi]
  apply isOpen_set_pi Set.finite_univ
  intro j _
  exact hOpen i

variable [∀ i, IsTopologicalRing (R i)]

def _root_.ContinuousLinearEquiv.restrictedProductPi [Fintype n]
    (hOpen : ∀ i, IsOpen (B i : Set (R i))) :
    Πʳ i, [n → R i, piSubringSubmodule B n i] ≃L[Πʳ i, [R i, B i]] n → Πʳ i, [R i, B i] where
  __ := LinearEquiv.restrictedProductPi n
  continuous_toFun := by
    apply continuous_pi
    intro i
    dsimp [LinearEquiv.restrictedProductPi]
    exact Continuous.restrictedProduct_congrRight _ (fun _ ↦ continuous_apply i)
  continuous_invFun := by
    have := Fact.mk hOpen
    have := Fact.mk (isOpen_piSubringSubmodule n hOpen)
    exact IsModuleTopology.continuous_of_linearMap
      (LinearEquiv.restrictedProductPi n).symm.toLinearMap

lemma moduleToplogy_of_prod [Finite n] (hOpen : ∀ i, IsOpen (B i : Set (R i))) :
    IsModuleTopology (Πʳ i, [R i, B i]) (Πʳ i, [n → R i, piSubringSubmodule B n i]) :=
  let := Fintype.ofFinite n
  have := Fact.mk hOpen
  IsModuleTopology.iso (ContinuousLinearEquiv.restrictedProductPi n hOpen).symm

end free_topology

variable [∀ i, IsTopologicalRing (R i)]
variable [∀ i, IsModuleTopology (R i) (M i)]
variable [Module.Finite (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i])]

theorem isModuleTopology (hBOpen : ∀ i, IsOpen (B i : Set (R i)))
    (hCOpen : ∀ i, IsOpen (C i : Set (M i)))
    : IsModuleTopology (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i]) := by
  have := Fact.mk hBOpen
  have := Fact.mk hCOpen
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i])
  let g' := ContinuousLinearEquiv.restrictedProductPi (Fin n) hBOpen
  let g := f ∘ₗ g'.toLinearMap
  have (i : ι) : ContinuousAdd (M i) := IsModuleTopology.toContinuousAdd (R i) (M i)
  have (i : ι) : ContinuousSMul (R i) (M i) := IsModuleTopology.toContinuousSMul (R i) (M i)
  have := moduleToplogy_of_prod (Fin n) hBOpen
  have hsurj : Function.Surjective g := hf.comp g'.surjective
  apply IsModuleTopology.of_isOpenMap_surjective _ g _ hsurj
  · classical
    apply isOpenMap_linearMap_of_surjective (isOpen_piSubringSubmodule (Fin n) hBOpen) hCOpen
    · intro i
      apply IsModuleTopology.isOpenMap_of_surjective
      exact surjective_components_of_surjective _ _ (linearMap_apply_eq_component g) hsurj _
        (Set.Finite.compl_mem_cofinite (Set.finite_singleton i))
    · exact eventually_surjOn_of_surjective Filter.comap_id.symm g _
        (linearMap_apply_eq_component g) hsurj

end RestrictedProduct
end

section

class Pi.FiberwiseSMul {α β : Type*} (f : α → β) (R : β → Type*) (M : α → Type*)
    [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (M a)]
    [(b : β) → (σ : {a // f a = b}) → Module (R b) (M σ)]
    [Module ((b : β) → R b) ((a : α) → M a)] : Prop where
  map_smul (f R M) (r : (b : β) → R b) (x : (a : α) → M a) (b : β) (σ : {a // f a = b}) :
    (r • x) σ = r b • x σ

def LinearEquiv.piScalarPiCongrFiberwise {α : Type*} {β : Type*} {R : β → Type*} {γ₁ : α → Type*}
    {γ₂ : β → Type*} {f : α → β} [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (γ₁ a)]
    [(b : β) → AddCommMonoid (γ₂ b)] [(b : β) → (a : { a : α // f a = b }) → Module (R b) (γ₁ a)]
    [(b : β) → Module (R b) (γ₂ b)] [Module (∀ b, R b) (∀ a, γ₁ a)] [Pi.FiberwiseSMul f R γ₁]
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃ₗ[R b] γ₂ b) :
    ((a : α) → γ₁ a) ≃ₗ[∀ b, R b] ((b : β) → γ₂ b) where
  __ := Equiv.piCongrFiberwise fun b => (e b).toEquiv
  map_add' _ _ := by funext; simp [← Pi.add_def]
  map_smul' r x := by funext; simp [← (e _).map_smul, Pi.FiberwiseSMul.map_smul, Pi.smul_def]

def LinearEquiv.piScalarPiComm {α β : Type*} (R : α → Type*) (φ : α → β → Type*)
    [∀ a, Semiring (R a)] [∀ a b, AddCommMonoid (φ a b)] [∀ a b, Module (R a) (φ a b)] :
    ((a : α) → (b : β) → φ a b) ≃ₗ[∀ a, R a] ((b : β) → (a : α) → φ a b) where
  __ := Equiv.piComm φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

class Prod.IsProdSMul (R S M N : Type*) [SMul R M] [SMul S N] [SMul (R × S) (M × N)] : Prop where
  map_smul (x : R × S) (y : M × N)  : x • y = (x.1 • y.1, x.2 • y.2)

theorem Prod.IsProdSMul.smul_fst {R S M N : Type*} [SMul R M] [SMul S N] [SMul (R × S) (M × N)]
    [Prod.IsProdSMul R S M N] (x : R × S) (y : M × N) : (x • y).1 = x.1 • y.1 := by
  rw [Prod.IsProdSMul.map_smul x y]

theorem Prod.IsProdSMul.smul_snd {R S M N : Type*} [SMul R M] [SMul S N] [SMul (R × S) (M × N)]
    [Prod.IsProdSMul R S M N] (x : R × S) (y : M × N) : (x • y).2 = x.2 • y.2 := by
  rw [Prod.IsProdSMul.map_smul x y]

open scoped RestrictedProduct in

class RestrictedProduct.FiberwiseSMul {α β : Type*} (f : α → β) (R : (b : β) → Type*)
    (A : (b : β) → Set (R b)) (𝓕 : Filter β) (M : (a : α) → Type*) (B : (a : α) → Set (M a))
    (𝓖 : Filter α) [(b : β) → (σ : { a // f a = b }) → SMul (R b) (M ↑σ)]
    [SMul (Πʳ b, [R b, A b]_[𝓕]) (Πʳ a, [M a, B a]_[𝓖])] : Prop where
  map_smul (r : Πʳ b, [R b, A b]_[𝓕]) (x : Πʳ a, [M a, B a]_[𝓖]) (b : β)
    (σ : {a // f a = b}) : (r • x) σ = r b • x σ
end

section

namespace IsDedekindDomain.FiniteAdeleRing

variable (R K : Type*) [CommRing R] [Field K] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

noncomputable abbrev integralAdeles : Subring (FiniteAdeleRing R K) :=
  RestrictedProduct.structureSubring _ _ _

variable {R K}

@[simp] lemma one_apply (v : HeightOneSpectrum R) : (1 : FiniteAdeleRing R K) v = 1 := rfl

@[simp] lemma mul_apply (a b : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl

abbrev mk (f : ∀ v, HeightOneSpectrum.adicCompletion K v)
    (h : ∀ᶠ (i : HeightOneSpectrum R) in Filter.cofinite,
    f i ∈ (fun v ↦ ↑(HeightOneSpectrum.adicCompletionIntegers K v)) i) : FiniteAdeleRing R K :=
  ⟨f, h⟩

@[simp]
lemma mk_apply (f : ∀ v, HeightOneSpectrum.adicCompletion K v)
    (h : ∀ᶠ (i : HeightOneSpectrum R) in Filter.cofinite,
    f i ∈ (fun v ↦ ↑(HeightOneSpectrum.adicCompletionIntegers K v)) i) (v : HeightOneSpectrum R) :
    mk f h v = f v := rfl
end IsDedekindDomain.FiniteAdeleRing

end

section

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum adicCompletion Extension

open scoped TensorProduct

lemma tendsTo_comap_cofinite [FaithfulSMul A B] :
    Filter.Tendsto (under A (B:=B)) Filter.cofinite Filter.cofinite :=
  have : FaithfulSMul A (FractionRing B) := FractionRing.instFaithfulSMul A B
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <|
    Extension.finite A (FractionRing A) (FractionRing B) B)

lemma cofinite_mapsTo_adicCompletionSemialgHom :
    ∀ᶠ (w : HeightOneSpectrum B) in Filter.cofinite,
    Set.MapsTo (Extension.adicCompletionSemialgHom K L (v := under A w) ⟨w, rfl⟩)
      (adicCompletionIntegers K (under A w)) (adicCompletionIntegers L w) := by
  apply Filter.Eventually.of_forall
  intro w
  exact Set.image_subset_iff.1 <| adicCompletionSemialgHom_image_adicCompletionIntegers K L ⟨w, rfl⟩

namespace FiniteAdeleRing

noncomputable def mapRingHom : 𝔸ᶠ[A, K] →+* 𝔸ᶠ[B, L] :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  RestrictedProduct.mapAlongRingHom (adicCompletion K) (adicCompletion L) (under A)
    (tendsTo_comap_cofinite A B) (fun w ↦ adicCompletionSemialgHom K L (v := w.under A) ⟨w, rfl⟩)
    (cofinite_mapsTo_adicCompletionSemialgHom A K L B)

set_option backward.isDefEq.respectTransparency false in
noncomputable def mapSemialgHom :
    𝔸ᶠ[A, K] →SA[algebraMap K L] 𝔸ᶠ[B, L] where
  __ := FiniteAdeleRing.mapRingHom A K L B
  map_smul' k a := by
    ext w
    refine congrArg _ ?_
    have h := (adicCompletionSemialgHom K L (v := w.under A) ⟨w, rfl⟩).map_smul' k (a (under A w))
    simp only [Algebra.smul_def'] at h ⊢
    exact h
  continuous_toFun :=
    have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
    RestrictedProduct.mapAlong_continuous _ _ _ (tendsTo_comap_cofinite A B) _
      (cofinite_mapsTo_adicCompletionSemialgHom A K L B)
      fun w ↦ adicCompletionSemialgHom_continuous K L ⟨w, rfl⟩

variable {A K B} in
lemma mapSemialgHom_apply (x : 𝔸ᶠ[A, K]) (w : HeightOneSpectrum B) :
    mapSemialgHom A K L B x w = adicCompletionSemialgHom K L ⟨w, rfl⟩ (x (under A w)) := rfl

open scoped TensorProduct.RightActions RestrictedProduct

variable [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]

instance : Algebra (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, v.adicCompletionIntegers K])
    (Πʳ w: HeightOneSpectrum B, [w.adicCompletion L, w.adicCompletionIntegers L]) :=
  inferInstanceAs (Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L])

attribute [local instance 9999] Algebra.toSMul in

class ComapFiberwiseSMul extends RestrictedProduct.FiberwiseSMul (α := HeightOneSpectrum B)
    (under A) (adicCompletion K) (fun v ↦ adicCompletionIntegers K v) Filter.cofinite
    (adicCompletion L) (fun w ↦ adicCompletionIntegers L w) Filter.cofinite

variable [ComapFiberwiseSMul A K L B]

variable {A K L B} in
theorem ComapFiberwiseSMul.map_smul' (x : 𝔸ᶠ[A, K]) (y : 𝔸ᶠ[B, L]) (v : HeightOneSpectrum A)
    (w : v.Extension B) : (x • y) w.1 = x v • y w.1 :=
  ComapFiberwiseSMul.toFiberwiseSMul.map_smul x y v w

variable {A K B} in
lemma BaseChange.algebraMap_apply (w : HeightOneSpectrum B) (x : 𝔸ᶠ[A, K]) :
    algebraMap _ 𝔸ᶠ[B, L] x w = adicCompletionSemialgHom K L ⟨w, rfl⟩ (x (under A w)) := by
  simp [Algebra.algebraMap_eq_smul_one, ComapFiberwiseSMul.map_smul' x 1 (w.under A) ⟨w, rfl⟩,
    RingHom.smul_toAlgebra, SemialgHom.toLinearMap_eq_coe]

noncomputable section bijection

def tensorEquivTensor [FiniteDimensional K L] : L ⊗[K] 𝔸ᶠ[A, K] ≃ₗ[B] B ⊗[A] 𝔸ᶠ[A, K] := by
  exact linearEquivTensorProductModuleLeft A K L B 𝔸ᶠ[A, K]

omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma tensorEquivTensor_tmul [FiniteDimensional K L] (b : B) (x : 𝔸ᶠ[A, K]) :
    tensorEquivTensor A K L B (algebraMap B L b ⊗ₜ[K] x) = b ⊗ₜ[A] x := by
  simp [tensorEquivTensor, linearEquivTensorProductModuleLeft_tmul]

set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in

def tensorEquivRestrictedProduct : B ⊗[A] 𝔸ᶠ[A, K] ≃ₗ[B] Πʳ v, [B ⊗[A] (adicCompletion K v),
    RestrictedProduct.rangeLTensorLeft A B (adicCompletion K) (integerSubmodule K) v] := by
  have := Module.finitePresentation_of_finite A B
  have := isTorsionFree A K L B
  let f := RestrictedProduct.lTensorEquivLeft A B (adicCompletion K) (integerSubmodule K) .cofinite
  apply LinearEquiv.trans (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) ?_) f
  exact {
    __ := AddEquiv.refl _
    map_smul' a x := by
      ext v
      exact congrArg _ (Algebra.smul_def a (x v) |>.symm)
  }

set_option backward.isDefEq.respectTransparency false in
omit [IsFractionRing B L] in
lemma tensorEquivRestrictedProduct_tmul (b : B) (x : 𝔸ᶠ[A, K]) (v : HeightOneSpectrum A) :
    tensorEquivRestrictedProduct A K L B (b ⊗ₜ[A] x) v = b ⊗ₜ[A] (x v) := by
  simp [tensorEquivRestrictedProduct]

set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in

def restrictedProduct_tensorProduct_equiv_restrictedProduct_prod [FiniteDimensional K L] :
    Πʳ v, [B ⊗[A] (adicCompletion K v),
      RestrictedProduct.rangeLTensorLeft A B (adicCompletion K) (integerSubmodule K) v] ≃ₗ[B]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      Submodule.pi Set.univ fun w : Extension B v ↦ (integerSubmodule L w.val)] :=
  LinearEquiv.restrictedProductCongrRight (R₁ := (B ⊗[A] adicCompletion K ·))
    (S₁ := fun v ↦ Submodule B (B ⊗[A] adicCompletion K v)) (integerBaseChangeLinearEquiv K L B)
      (.of_forall <| integerBaseChangeLinearEquiv_bijOn K L)

omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma restrictedProduct_tensorProduct_equiv_restrictedProduct_prod_apply [FiniteDimensional K L]
    (f) (v : HeightOneSpectrum A) :
    FiniteAdeleRing.restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B f v =
    integerBaseChangeLinearEquiv K L B v (f v) := rfl

set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in

def restrictedProduct_prod_equiv :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      Submodule.pi .univ fun w : Extension B v ↦ (integerSubmodule L w.val)] ≃ₗ[B]
    𝔸ᶠ[B, L] :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  {
    __ := RestrictedProduct.flatten_equiv'
      (fun w : HeightOneSpectrum B ↦ SetLike.coe <| w.adicCompletionIntegers L)
      (tendsTo_comap_cofinite A B)
    map_add' x y := rfl
    map_smul' a x := by
      ext w
      refine congrArg _ ?_
      change a • (x (under A w) ⟨w, rfl⟩) = _
      simp [Submodule.coe_pi,Algebra.smul_def, RingHom.id_apply, Equiv.toFun_as_coe]
      rfl
  }

omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma restrictedProduct_prod_equiv_apply (f) (w : HeightOneSpectrum B) :
    restrictedProduct_prod_equiv A K L B f w = f (under A w) ⟨w, rfl⟩ := rfl

set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in

def baseChangeLinearEquiv [FiniteDimensional K L] : L ⊗[K] 𝔸ᶠ[A, K] ≃ₗ[L] 𝔸ᶠ[B, L] :=
  let f₁ := tensorEquivTensor A K L B
  let f₂ := tensorEquivRestrictedProduct A K L B
  let f₃ := restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B
  let f₄ := restrictedProduct_prod_equiv A K L B
  let f := f₁ ≪≫ₗ f₂ ≪≫ₗ f₃ ≪≫ₗ f₄
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors B) L f

lemma algebraMap_apply_eq_algebraMap (x : K) (v : HeightOneSpectrum A) :
    algebraMap K 𝔸ᶠ[A, K] x v = algebraMap K (v.adicCompletion K) x := rfl

set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in
@[simp]
lemma baseChangeLinearEquiv_tmul [FiniteDimensional K L] (b : B) (x : 𝔸ᶠ[A, K]) :
    baseChangeLinearEquiv A K L B (algebraMap B L b ⊗ₜ x) =
      (algebraMap _ 𝔸ᶠ[B, L] b) * (algebraMap _ 𝔸ᶠ[B, L] x) := by
  ext w
  simp [baseChangeLinearEquiv, restrictedProduct_prod_equiv_apply, tensorEquivTensor_tmul,
    restrictedProduct_tensorProduct_equiv_restrictedProduct_prod_apply,
    tensorEquivRestrictedProduct_tmul, BaseChange.algebraMap_apply,
    IsScalarTower.algebraMap_apply B L 𝔸ᶠ[B, L],
    IsScalarTower.algebraMap_apply B L (w.adicCompletion L), -Submodule.coe_pi]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseChange_bijective [FiniteDimensional K L] :
    Function.Bijective (SemialgHom.baseChange_of_algebraMap <|
      (mapSemialgHom A K L B).toSemialgHom) := by
  suffices ⇑(SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B) =
      ⇑(FiniteAdeleRing.baseChangeLinearEquiv A K L B) by
    rw [ContinuousSemialgHom.toSemialgHom_eq_coe, this]
    exact (FiniteAdeleRing.baseChangeLinearEquiv A K L B).bijective
  rw [← AlgHom.coe_toLinearMap, ← LinearEquiv.coe_toLinearMap]

  apply congr_arg _ <| LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l x =>
    ext w
    refine congrArg _ ?_
    obtain ⟨⟨b, s⟩, hl : (s : B) • l = algebraMap B L b⟩ :=
      IsLocalizedModule.surj (M := B) (M' := L) (nonZeroDivisors B) (Algebra.linearMap B L) l
    rw [LinearEquiv.coe_coe, ← IsUnit.smul_left_cancel <| IsLocalization.map_units L s]
    simp only [Algebra.smul_def, ← algebraMap_apply_eq_algebraMap, ← mul_apply]
    simp only [← Algebra.smul_def, ← map_smul]
    simp [hl, baseChangeLinearEquiv_tmul, BaseChange.algebraMap_apply, mapSemialgHom_apply,
      SemialgHom.baseChange_of_algebraMap_tmul, Algebra.compHom_algebraMap_apply,
      TensorProduct.smul_tmul']
  | add => simp_all

def baseChangeAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃ₐ[L] 𝔸ᶠ[B, L] :=
  .ofBijective (SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B)
    (FiniteAdeleRing.baseChange_bijective A K L B)

def baseChangeAdeleAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃ₐ[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] where
  __ := SemialgHom.baseChangeRightOfAlgebraMap <|
    (FiniteAdeleRing.mapSemialgHom A K L B).toSemialgHom
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  commutes' x := by
    ext
    simp [BaseChange.algebraMap_apply]
    rfl

instance [FiniteDimensional K L] : Module.Finite 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] :=
  Module.Finite.equiv (FiniteAdeleRing.baseChangeAdeleAlgEquiv A K L B).toLinearEquiv

end bijection

section moduleTopology

attribute [local instance 9999] Algebra.toModule in

noncomputable local instance (v : HeightOneSpectrum A) : Module (adicCompletionIntegers K v)
    ((w : Extension B v) → adicCompletion L w.val) :=
  Module.compHom _ (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))

noncomputable local instance (v : HeightOneSpectrum A) : SMul (adicCompletionIntegers K v)
    ((w : Extension B v) → adicCompletion L w.val) :=
  Module.toDistribMulAction.toDistribSMul.toSMul

noncomputable local instance (v : HeightOneSpectrum A) : MulAction (v.adicCompletionIntegers K)
    (v.adicCompletion K) := LieAlgebra.ofAssociativeAlgebra.toMulAction

attribute [local instance 9999] Algebra.toModule Algebra.toSMul in

noncomputable def piAdicIntegerSubmodule (v : HeightOneSpectrum A) :
    Submodule (adicCompletionIntegers K v) ((w : Extension B v) → adicCompletion L w.val) :=
  let module (w : Extension B v) := Module.compHom (adicCompletion L w.val)
    (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))
  Submodule.pi Set.univ fun (w : Extension B v) ↦
    letI := (module w).toDistribMulAction.toDistribSMul.toSMul
    have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.val)
        (adicCompletion L w.val) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let s := (adicCompletionIntegers L w.val).toSubmodule
    letI : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L).toSubring :=
      inferInstanceAs (Algebra (adicCompletionIntegers K v) (adicCompletionIntegers L w.1))
    s.restrictScalars (adicCompletionIntegers K v)

private noncomputable local instance (priority := 9999) (v : HeightOneSpectrum A) :
    Module (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
  Algebra.toModule

set_option synthInstance.maxHeartbeats 80000 in

set_option maxHeartbeats 400000 in

noncomputable local instance : Module 𝔸ᶠ[A, K]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.1,
    ↑(piAdicIntegerSubmodule A K L B v)] :=
  RestrictedProduct.instModuleCoe_fLT

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 80000 in

set_option maxHeartbeats 400000 in

noncomputable def restrictedProduct_pi_equiv :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      piAdicIntegerSubmodule A K L B v] ≃L[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] :=
  have := FaithfulSMul.of_field_isFractionRing A B K L
  let f : _ ≃ₜ 𝔸ᶠ[B, L] := RestrictedProduct.flatten_homeomorph'
    (G := adicCompletion L) (fun w ↦ adicCompletionIntegers L w) (tendsTo_comap_cofinite A B)
  {
    __ := f
    map_add' x y := rfl
    map_smul' r x := by
      ext w
      rw [RingHom.id_apply, Algebra.smul_def, RestrictedProduct.mul_apply,
        BaseChange.algebraMap_apply]
      rfl
  }

attribute [instance 100] RestrictedProduct.instSMulCoeOfSMulMemClass

set_option synthInstance.maxHeartbeats 160000 in

set_option maxHeartbeats 800000 in
lemma restrictedProduct_pi_isModuleTopology [FiniteDimensional K L] : IsModuleTopology 𝔸ᶠ[A, K]
    (Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      piAdicIntegerSubmodule A K L B v]) := by
  have :=
    Module.Finite.equiv (FiniteAdeleRing.restrictedProduct_pi_equiv A K L B).symm.toLinearEquiv
  unfold FiniteAdeleRing at this

  refine @RestrictedProduct.isModuleTopology _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ this ?_ ?_
  · exact fun v ↦ Valued.isOpen_integer (adicCompletion K v)
  · intro v
    simp only [piAdicIntegerSubmodule, Submodule.coe_pi, Submodule.coe_restrictScalars]
    apply isOpen_set_pi _ (fun _ _ ↦ Valued.isOpen_integer _)
    rw [Set.finite_univ_iff]
    exact Extension.finite A K L B v

set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in
instance [FiniteDimensional K L] : IsModuleTopology 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] :=
  have := restrictedProduct_pi_isModuleTopology A K L B
  IsModuleTopology.iso (FiniteAdeleRing.restrictedProduct_pi_equiv A K L B)

end moduleTopology

noncomputable def baseChangeAdeleContinuousAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃A[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] :=
  IsModuleTopology.continuousAlgEquivOfAlgEquiv <| baseChangeAdeleAlgEquiv A K L B

noncomputable def baseChangeContinuousAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃A[L] 𝔸ᶠ[B, L] where
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  __ := FiniteAdeleRing.baseChangeAdeleContinuousAlgEquiv A K L B

end IsDedekindDomain.FiniteAdeleRing


