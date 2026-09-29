-- Prove2me | Definitions.Def_DedekindDomain_Completion_BaseChange
-- name    : DedekindDomain_Completion_BaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/15298316-7825-5df5-b5ae-80b14928093f
-- title:
--   Base change of adic completions along an extension of Dedekind domains
-- statement:
--   The standing setting is the AKLB situation: $A$ a Dedekind domain with fraction field $K$, $B$ an $A$-algebra, integral over $A$, which is a Dedekind domain with fraction field $L$, together with compatible scalar towers over $K\subseteq L$; $v$ is a height-one prime of $A$ and $w$ ranges over `Extension B v`, the subtype of height-one primes of $B$ whose contraction to $A$ is $v$. For such a $w$ the inclusion $K\to L$ is continuous for the $v$-adic and $w$-adic topologies (`adicValued.continuous_algebraMap`), and completing it gives `Extension.adicCompletionSemialgHom`, a ring map $K_v\to L_w$ semilinear over $K\to L$; its valuation behaviour is $|\,\varphi(x)\,| = |x|^{e}$ with $e$ the ramification index of $w$ over $v$, so integers map to integers, and $L_w$ becomes a $K_v$-algebra. Taking all $w\mid v$ at once yields `adicCompletion.semialgHomPi`, $K_v\to\prod_{w\mid v}L_w$, and by base change the $L$-algebra map `adicCompletion.baseChange`, $L\otimes_K K_v\to\prod_{w\mid v}L_w$, together with its avatar `baseChangeRight` as a $K_v$-algebra map. Surjectivity comes from density of $L$ in the product (`denseRange_of_prodAlgebraMap`, resting on `closureAlgebraMapIntegers_eq_prodIntegers`: the closure of the image of $A$ in a finite product of completions is the product of the integer rings) together with finite-dimensionality; injectivity from the rank count $[L:K]=\sum_{w\mid v}e_wf_w=\sum_w[L_w:K_v]$, where the local identities `ramificationIdx_eq_ramificationIdx`, `inertiaDeg_eq_inertiaDeg` and `ramificationIdx_mul_inertiaDeg_eq_finrank` are proved. Hence `baseChangeAlgEquiv`, an $L$-algebra isomorphism $L\otimes_K K_v\cong\prod_{w\mid v}L_w$, refined to a topological isomorphism `baseChangeContinuousAlgEquiv` using that each $L_w$, and the product, carry the $K_v$-module topology. On the integral level, `tensorAdicCompletionIntegersTo` sends $B\otimes_A\mathcal O_v\to L\otimes_K K_v$ with clopen image equal to the closure of the image of $B$, and `integerBaseChangeLinearEquiv` is the $B$-linear isomorphism $B\otimes_A K_v\cong\prod_{w\mid v}L_w$ carrying the image of $B\otimes_A\mathcal O_v$ bijectively onto $\prod_{w\mid v}\mathcal O_{L_w}$. Ancillary general lemmas include $\pi$-valued semialgebra maps, base change of a semialgebra hom along `algebraMap`, right base change of a basis and the resulting rank equality $\operatorname{rank}_B(A\otimes_R B)=\operatorname{rank}_R A$, and multiplication units as linear equivalences.
--
--   **Relation to Mathlib.** Mathlib supplies the adic completion `adicCompletion` of a fraction field at a height-one prime and its valuation subring `adicCompletionIntegers`; the subtype `Extension` of primes of $B$ above $v$, the semialgebra map between completions, the base-change comparison with the product over $w\mid v$ and its integral counterpart are the project's own, as are the generic additions to the semialgebra-hom and tensor-product interfaces ([`Pi.semialgHom`](../def/DedekindDomain_Completion_BaseChange.html#L25), [`SemialgHom.baseChange_of_algebraMap`](../def/DedekindDomain_Completion_BaseChange.html#L76), [`Module.Basis.rightBaseChange`](../def/DedekindDomain_Completion_BaseChange.html#L191)).
--
--   **Where it is used.** These comparisons are the local foundation for working adelically over number fields: they identify the completion of an extension at the places above a given place and match integral lattices, and they are used throughout the treatment of local components of automorphic forms and of local conditions on Galois representations.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file: `FLT/DedekindDomain/Completion/BaseChange.lean` — commit 8387d589 (2026-05-27); © 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang, Matthew Jasper (see §5); `FLT/Mathlib/Algebra/Algebra/Bilinear.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri, Ruben Van de Velde; `FLT/Mathlib/Algebra/Algebra/Pi.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri; `FLT/Mathlib/RingTheory/TensorProduct/Basis.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper; `FLT/DedekindDomain/IntegralClosure.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang, Matthew Jasper; `FLT/Mathlib/Algebra/Module/Submodule/Basic.lean` — © 2025 Yaël Dillies; authors: Yaël Dillies, Kevin Buzzard, Matthew Jasper; `FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_DedekindDomain_Completion_BaseChange.lean

import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_Mathlib_IsModuleTopology
import Definitions.Def_Mathlib_Topology_Algebra_UniformRing
import Definitions.Def_Mathlib_RightActionInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

set_option maxSynthPendingDepth 3
set_option Elab.async false

section

variable {R S : Type*} [Ring R]

def Subring.toSubmodule (S : Subring R) : Submodule S R where
  __ := S
  smul_mem' x y h := by
    rw [smul_def, smul_eq_mul]
    apply S.mul_mem (SetLike.coe_mem x) h

section

def Pi.semialgHom {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) :
    A →ₛₐ[φ] (i : I) → f i where
  __ := RingHom.pi fun i ↦ (g i).toRingHom
  map_smul' r a := by ext; simp [RingHom.pi]

@[simp]
theorem Pi.semialgHom_apply {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R]
    [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) (a : A) (i : I) :
    (Pi.semialgHom _ φ g) a i = g i a :=
  rfl

def Pi.semialgHomPi {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J} (p : (i : I) → g (r i) →ₛₐ[φ] f i) :
    ((j : J) → g j) →ₛₐ[φ] (i : I) → f i where
  toFun x w := p w (x (r w))
  map_one' := by simp [Pi.one_def]
  map_mul' x y := funext fun w => by simp [map_mul]
  map_zero' := by simp [Pi.zero_def]
  map_add' x y := funext fun w => by simp [map_add]
  map_smul' k x := funext fun w => (p w).map_smul' k (x (r w))

@[simp]
theorem Pi.semialgHomPi_apply {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J} (p : (i : I) → g (r i) →ₛₐ[φ] f i)
    (a : (j : J) → g j) (i : I) :
    Pi.semialgHomPi _ _ p a i = p i (a (r i)) := rfl

def AlgEquiv.piCongrFiberwise {α : Type*} {β : Type*} {R : Type*} {γ₁ : α → Type*} {γ₂ : β → Type*}
    {f : α → β} [CommSemiring R] [(a : α) → Semiring (γ₁ a)] [(b : β) → Semiring (γ₂ b)]
    [(a : α) → Algebra R (γ₁ a)] [(b : β) → Algebra R (γ₂ b)]
    (e : (b : β) → ((x : { x : α // f x = b }) → γ₁ x.1) ≃ₐ[R] γ₂ b) :
    ((a : α) → γ₁ a) ≃ₐ[R] ((b : β) → γ₂ b) where
  __ := Equiv.piCongrFiberwise fun _ => (e _).toEquiv
  map_add' _ _ := by funext b; simp [← Pi.add_def]
  map_mul' _ _ := by funext b; simp [← Pi.mul_def]
  commutes' r := by funext b; simp [← (e b).commutes' r, Pi.algebraMap_def]

section
open scoped TensorProduct
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*}

noncomputable
def SemialgHom.baseChange_of_algebraMap [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) :
    S ⊗[R] A →ₐ[S] B :=
  letI : Algebra R B := Algebra.compHom _ (algebraMap R S)
  have : IsScalarTower R S B := .of_algebraMap_eq fun _ ↦ rfl
  let ρ : A →ₐ[R] B := {
    toRingHom := ψ.toRingHom
    commutes' := ψ.commutes
  }
  Algebra.TensorProduct.lift (Algebra.ofId S _) ρ fun s a ↦ Algebra.commutes s (ρ a)

theorem SemialgHom.baseChange_of_algebraMap_tmul [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (s : S) (a : A) :
    ψ.baseChange_of_algebraMap (s ⊗ₜ[R] a) = algebraMap _ _ s * ψ a := by
  simp [baseChange_of_algebraMap, SemialgHom.toLinearMap_eq_coe, Algebra.ofId_apply]

@[simp]
theorem SemialgHom.baseChange_of_algebraMap_tmul_right [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (a : A) :
    ψ.baseChange_of_algebraMap (1 ⊗ₜ[R] a) = ψ a := by
  simp [baseChange_of_algebraMap, SemialgHom.toLinearMap_eq_coe]

@[simp]
theorem SemialgHom.baseChange_of_algebraMap_tmul_left [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (s : S) :
    ψ.baseChange_of_algebraMap (s ⊗ₜ[R] 1) = algebraMap _ _ s := by
  simp [baseChange_of_algebraMap, SemialgHom.toLinearMap_eq_coe, Algebra.ofId_apply]

open scoped TensorProduct.RightActions in

instance [Algebra R S] [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    letI := ψ.toAlgebra
    IsBiscalar S A ψ.baseChange_of_algebraMap where
  __ := ψ.toAlgebra
  map_smul₁ s x := ψ.baseChange_of_algebraMap.map_smul_of_tower ..
  map_smul₂ a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [TensorProduct.smul_tmul', -algebraMap_smul,
        algebra_compatible_smul B a, SemialgHom.baseChange_of_algebraMap_tmul,
        RingHom.algebraMap_toAlgebra, SemialgHom.toLinearMap_eq_coe]
      ring
    | add x y hx hy => simp_all

open scoped TensorProduct.RightActions in

noncomputable
def SemialgHom.baseChangeRightOfAlgebraMap [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    letI := ψ.toAlgebra
    S ⊗[R] A →ₐ[A] B :=
  letI := ψ.toAlgebra
  AlgHom.changeScalars A ψ.baseChange_of_algebraMap

open scoped TensorProduct.RightActions in
@[simp]
theorem SemialgHom.baseChangeRightOfAlgebraMap_apply [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) (x : S ⊗[R] A) :
    baseChangeRightOfAlgebraMap ψ x = baseChange_of_algebraMap ψ x := by
  simp [baseChangeRightOfAlgebraMap, AlgHom.changeScalars_apply]

open scoped TensorProduct.RightActions in
@[simp]
theorem SemialgHom.baseChangeRightOfAlgebraMap_coe [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    ⇑ψ.baseChangeRightOfAlgebraMap = ⇑ψ.baseChange_of_algebraMap :=
  funext_iff.2 <| ψ.baseChangeRightOfAlgebraMap_apply

variable (F : Type*) [CommSemiring F] {A : Type*} [Ring A]
    [Algebra F A]

def _root_.LinearEquiv.mulLeft (u : Aˣ) : A ≃ₗ[F] A where
  toFun x := u * x
  invFun y := u⁻¹ * y
  left_inv x := by simp
  right_inv y := by simp
  map_add' x₁ x₂ := left_distrib ↑u x₁ x₂
  map_smul' f x := by simp

@[simp]
theorem LinearEquiv.coe_mulLeft (u : Aˣ) :
    (LinearEquiv.mulLeft F u : A →ₗ[F] A) = LinearMap.mulLeft F (u : A) :=
  rfl

def _root_.LinearEquiv.mulRight (u : Aˣ) : A ≃ₗ[F] A where
  toFun x := x * u
  invFun y := y * u⁻¹
  left_inv x := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]
  map_add' x₁ x₂ := right_distrib x₁ x₂ u
  map_smul' f x := by simp

@[simp]
theorem LinearEquiv.coe_mulRight (u : Aˣ) :
    (LinearEquiv.mulRight F u : A →ₗ[F] A) = LinearMap.mulRight F (u : A) :=
  rfl

section

section Basis

open scoped TensorProduct

open scoped TensorProduct.RightActions

variable {R : Type*} (A : Type*) {B : Type*} {ι : Type*} [CommSemiring R]
variable [CommSemiring A] [Algebra R A] [Fintype ι]
variable [CommSemiring B] [Algebra R B]

noncomputable
def Module.Basis.rightBaseChange [DecidableEq ι] (b : Module.Basis ι R A) :
    Module.Basis ι B (A ⊗[R] B) where
  repr :=
    let comm : B ⊗[R] A ≃ₗ[B] A ⊗[R] B :=
      TensorProduct.RightActions.Algebra.TensorProduct.comm R B A
    let π : B ⊗[R] A ≃ₗ[B] (ι → B) :=
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl B B)
        b.equivFun).trans
      (TensorProduct.piScalarRight _ _ _ _)
    let finite : (ι →₀ B) ≃ₗ[B] (ι → B) := Finsupp.linearEquivFunOnFinite B B ι
    comm.symm.trans π |>.trans finite.symm

@[simp]
lemma Module.Basis.rightBaseChange_repr [DecidableEq ι] (b : Module.Basis ι R A) (i) (x : B) :
    (b.rightBaseChange A).repr (b i ⊗ₜ x) = Finsupp.single i x := by
  have : ∑ (j : ι), (Pi.single i (1 : R) : ι → R) j • (b j) = b i := by
    conv =>
      lhs
      arg 2
      intro j
      rw [Pi.single_comm, Pi.single_apply_smul]
    simp
  rw [← LinearEquiv.eq_symm_apply]
  simp [rightBaseChange, this]

@[simp]
lemma Module.Basis.rightBaseChange_apply [DecidableEq ι] (b : Basis ι R A) (i) :
    b.rightBaseChange A i = b i ⊗ₜ (1 : B) := by
  rw [apply_eq_iff]
  exact rightBaseChange_repr A b i 1

end Basis

section Finrank

namespace TensorProduct

open scoped TensorProduct.RightActions

variable {R : Type*} (A : Type*) {B : Type*} [CommRing R]
  [CommSemiring A] [Algebra R A] [CommRing B] [Algebra R B] [Nontrivial B]

lemma finrank_rightAlgebra [Module.Finite R A] [Module.Free R A] :
    Module.finrank B (A ⊗[R] B) = Module.finrank R A := by
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R B)
  let b := Module.Free.chooseBasis R A
  let b' : Module.Basis _ _ (A ⊗[R] B) := b.rightBaseChange A
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']

end TensorProduct

end Finrank

namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

open Valuation.IsRankOneDiscrete in

theorem closureAlgebraMapIntegers_eq_prodIntegers {ι : Type*}
    (v : ι → HeightOneSpectrum A)
    (injective : Function.Injective v) :
    closure (SetLike.coe (algebraMap A ((i : ι) → (v i).adicCompletion K)).range) =
    (Set.pi Set.univ (fun (i : ι) ↦ ((v i).adicCompletionIntegers K).carrier)) := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro c ⟨a, ha⟩ i -
      rw [← ha]
      simp only [Pi.algebraMap_apply]
      exact coe_mem_adicCompletionIntegers (v i) a
    · apply isClosed_set_pi
      rintro w -
      apply Valued.isClosed_valuationSubring
  · intro f hf
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Pi.zero_def, nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨I, t, htn, hts⟩ := hU
    choose g' hg' using fun w => (Valued.is_topological_valuation (t w)).mp (htn w)
    let g := fun w ↦ Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt _).toMulEquiv (g' w)
    obtain ⟨a, ha⟩ :=
      exists_forall_adicValued_sub_lt K I g v injective (fun w => ⟨f w, hf w ⟨⟩⟩)
    use algebraMap A _ a
    constructor
    · rw [RingHom.coe_range]
      exact Set.mem_range_self a
    · refine hts fun w hw ↦ hg' w ?_
      rw [Set.mem_setOf_eq, ← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
        valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
          (valuedAdicCompletion_surjective K (v w))]
      exact ha w hw

theorem denseRange_of_prodAlgebraMap {ι : Type*} [Finite ι]
    {valuation : ι → HeightOneSpectrum A} (injective : Function.Injective valuation) :
    DenseRange (algebraMap K ((i : ι) → (valuation i).adicCompletion K)) := by
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  let S := Set.range (algebraMap K ((i : ι) → (valuation i).adicCompletion K))

  have hint : Set.pi Set.univ (fun (i : ι) ↦ ((valuation i).adicCompletionIntegers K).carrier)
      ⊆ closure S := by
    rw [← closureAlgebraMapIntegers_eq_prodIntegers _ _ injective]
    apply closure_mono
    exact fun _ ⟨a, ha⟩ ↦ ⟨algebraMap A K a, ha⟩

  have hmul : ∀x, x ∈ closure S → ∀k : K, k • x ∈ closure S := by
    intro x h k
    let f := fun (z : (i : ι) → (valuation i).adicCompletion K) ↦ k • z
    have hf : ContinuousAt f x := Continuous.continuousAt (continuous_const_smul k)
    apply closure_mono _ <| mem_closure_image hf h
    rintro x ⟨_, ⟨z, rfl⟩, rfl⟩
    use k • algebraMap K _ z
    ext i
    simp [Algebra.smul_def, f]

  intro x
  obtain ⟨k, y, hy, hx⟩ := adicCompletion.eq_mul_pi_adicCompletionIntegers K valuation x
  exact hx ▸ hmul y (hint hy) k

end IsDedekindDomain.HeightOneSpectrum

section

open scoped WithZero Valued TensorProduct
open Valuation.IsRankOneDiscrete WithZero

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

section assumptions

variable [IsIntegralClosure B A L] [FiniteDimensional K L]

example : IsDomain B := by
  have foo : Function.Injective (algebraMap B L) := IsIntegralClosure.algebraMap_injective B A _
  have bar : IsDomain L := inferInstance
  exact Function.Injective.isDomain _ foo

example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L

example [IsDomain B] [Algebra.IsSeparable K L] : IsDedekindDomain B :=
  IsIntegralClosure.isDedekindDomain A K L B

example [IsDedekindDomain B] : IsFractionRing B L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K L B

example [Algebra.IsSeparable K L] : Module.Finite A B :=
  have := IsIntegralClosure.isNoetherian A K L B
  Module.IsNoetherian.finite A B

example : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L

end assumptions

variable [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]

namespace IsDedekindDomain.HeightOneSpectrum

variable (v : HeightOneSpectrum A) {A B}

local notation "σ" => fun v w => algebraMap (WithVal (HeightOneSpectrum.valuation K v))
    (WithVal (HeightOneSpectrum.valuation L w))

private theorem continuousAdd_withVal_pin (w : HeightOneSpectrum B) :
    ContinuousAdd (WithVal (HeightOneSpectrum.valuation L w)) := inferInstance

omit [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsIntegral A B] in
private theorem addMonoidHomClass_withVal_pin (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) :
    AddMonoidHomClass (WithVal (HeightOneSpectrum.valuation K v) →+* WithVal (HeightOneSpectrum.valuation L w))
      (WithVal (HeightOneSpectrum.valuation K v)) (WithVal (HeightOneSpectrum.valuation L w)) := inferInstance

private theorem isTopologicalAddGroup_withVal_pin (v : HeightOneSpectrum A) :
    IsTopologicalAddGroup (WithVal (HeightOneSpectrum.valuation K v)) := inferInstance

attribute [local instance] continuousAdd_withVal_pin addMonoidHomClass_withVal_pin isTopologicalAddGroup_withVal_pin

set_option backward.isDefEq.respectTransparency false in
lemma adicValued.continuous_algebraMap
   (w : HeightOneSpectrum B) (hvw : w.under A = v) :
    Continuous (σ v w) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γL _
  let e := v.asIdeal.ramificationIdx' w.asIdeal

  let σL := WithVal.valueGroupOrderIso₀ (w.valuation L)
  let σw := valueGroup₀_equiv_withZeroMulInt (w.valuation L)
  let m : ℤᵐ⁰ := σw (σL γL)

  let σv := valueGroup₀_equiv_withZeroMulInt (v.valuation K)
  let σK := (WithVal.valueGroupOrderIso₀ (v.valuation K))
  let γK := σK.symm (σv.symm (exp (m.log / e)))
  have hγK : γK ≠ 0 := by simp [γK]
  use .mk0 _ hγK
  simp only [Units.val_mk0, Set.mem_setOf_eq, true_and]
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx₀; · simp
  rw [σK.lt_symm_apply] at hx
  replace hx := (WithVal.valueGroupOrderIso₀_restrict (v.valuation K) x).symm.trans_lt hx
  rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (v.valuation_surjective K),
    OrderMonoidIso.apply_symm_apply, ← log_lt_log (by simp_all) (by simp)] at hx
  rw [← σL.strictMono.lt_iff_lt]
  refine lt_of_eq_of_lt (WithVal.valueGroupOrderIso₀_restrict (w.valuation L) _) ?_
  rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (w.valuation_surjective L),
    WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply, ← valuation_comap A,
    ← log_lt_log (by simp_all) (by simp), log_pow, nsmul_eq_mul, mul_comm]
  subst hvw
  apply Int.mul_lt_of_lt_ediv (mod_cast pos_of_ne_zero (ramificationIdx_ne_zero A B
    (algebraMap_injective_of_field_isFractionRing A B K L) w)) hx

namespace Extension

variable {v} (w : v.Extension B)

@[simps!]
def _root_.WithVal.semialgebraMap {R S Γ₀ Γ₀' : Type*} [CommRing R]
    [CommRing S] [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀']
    [Algebra R S] (v : Valuation R Γ₀) (w : Valuation S Γ₀') :
    WithVal v →ₛₐ[algebraMap R S] WithVal w where
  __ := algebraMap (WithVal v) (WithVal w)
  map_smul' r x := by
    simp [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply, Algebra.smul_def]

noncomputable def adicCompletionSemialgHomCompletion :
    (v.valuation K).Completion →ₛₐ[algebraMap K L] (w.1.valuation L).Completion :=
  .restrictScalars (WithVal.semialgebraMap (v.valuation K) (w.1.valuation L)) <|
    UniformSpace.Completion.mapSemialgHom _ <| adicValued.continuous_algebraMap K L v w.1 w.2

noncomputable def adicCompletionSemialgHom :
    v.adicCompletion K →ₛₐ[algebraMap K L] w.1.adicCompletion L where
  toFun x := .ofCompletion (adicCompletionSemialgHomCompletion K L w x.toCompletion)
  map_add' x y := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_add, map_add, adicCompletion.toCompletion_ofCompletion]
  map_smul' k x := by
    apply adicCompletion.ext
    exact (adicCompletionSemialgHomCompletion K L w).map_smul k x.toCompletion
  map_zero' := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_zero, map_zero, adicCompletion.toCompletion_ofCompletion]
  map_one' := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_one, map_one, adicCompletion.toCompletion_ofCompletion]
  map_mul' x y := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_mul, map_mul, adicCompletion.toCompletion_ofCompletion]

lemma adicCompletionSemialgHom_apply (x : v.adicCompletion K) :
    w.adicCompletionSemialgHom K L x =
      .ofCompletion (adicCompletionSemialgHomCompletion K L w x.toCompletion) := rfl

lemma toCompletion_adicCompletionSemialgHom (x : v.adicCompletion K) :
    (w.adicCompletionSemialgHom K L x).toCompletion =
      adicCompletionSemialgHomCompletion K L w x.toCompletion := rfl

lemma adicCompletionSemialgHom_coe (x : WithVal (v.valuation K)) :
    w.adicCompletionSemialgHom K L x = algebraMap K L x.ofVal :=
  (w.adicCompletionSemialgHom K L).commutes _

open WithZeroTopology in

lemma valued_adicCompletionSemialgHom (x) :
    Valued.v (adicCompletionSemialgHom K L w x) = Valued.v x ^
      (w.1.under A).asIdeal.ramificationIdx' w.1.asIdeal := by
  obtain ⟨y, rfl⟩ := adicCompletion.ofCompletion_surjective K v x
  revert y
  apply funext_iff.mp
  symm
  apply UniformSpace.Completion.ext
  · exact ((Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective K)).comp
      (adicCompletion.continuous_ofCompletion K v)).pow _
  · exact (Valued.continuous_valuation_of_surjective (w.1.valuedAdicCompletion_surjective L)).comp
      ((adicCompletion.continuous_ofCompletion L w.1).comp
        (UniformSpace.Completion.continuous_map.comp
          ((adicCompletion.continuous_toCompletion K v).comp (adicCompletion.continuous_ofCompletion K v))))
  intro a
  change Valued.v (a : v.adicCompletion K) ^ _ = Valued.v (w.adicCompletionSemialgHom K L a)
  rw [adicCompletionSemialgHom_coe, adicCompletion.valued_coe, ← valuation_comap A K L B w.1]
  simp only [w.2]
  congr 1
  rw [adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply]
  rfl

lemma adicCompletionSemialgHom_image_adicCompletionIntegers :
    w.adicCompletionSemialgHom K L '' (v.adicCompletionIntegers K) ⊆
      w.1.adicCompletionIntegers L := by
  rintro y ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx ⊢
  rw [w.valued_adicCompletionSemialgHom K L]
  rwa [pow_le_one_iff]
  exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1

noncomputable
instance : Algebra (v.adicCompletion K) (w.1.adicCompletion L) :=
  (w.adicCompletionSemialgHom K L).toAlgebra

lemma adicCompletionSemialgHom_continuous : Continuous (w.adicCompletionSemialgHom K L) :=
  (adicCompletion.continuous_ofCompletion L w.1).comp
    (UniformSpace.Completion.continuous_extension.comp (adicCompletion.continuous_toCompletion K v))

instance : ContinuousSMul (adicCompletion K v) (adicCompletion L w.1) := by
  constructor
  have leftCts := w.adicCompletionSemialgHom_continuous K L
  exact Continuous.mul (Continuous.fst' leftCts) continuous_snd

end Extension

section shortcut_instances

private noncomputable instance : Valued (v.adicCompletion K) ℤᵐ⁰ := inferInstance
private noncomputable instance : Field (v.adicCompletion K) := inferInstance
private noncomputable instance : CommRing (v.adicCompletion K) := inferInstance
private noncomputable instance : Ring (v.adicCompletion K) := inferInstance
private noncomputable instance : CommSemiring (v.adicCompletion K) := inferInstance
private noncomputable instance : Semiring (v.adicCompletion K) := inferInstance
private noncomputable instance : AddCommGroup (v.adicCompletion K) := inferInstance
private noncomputable instance : AddCommMonoid (v.adicCompletion K) := inferInstance

private noncomputable instance (w : v.Extension B) : Valued (w.1.adicCompletion L) ℤᵐ⁰ := inferInstance
private noncomputable instance (w : v.Extension B) : Field (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : CommRing (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : Ring (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : CommSemiring (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : Semiring (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : AddCommGroup (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : AddCommMonoid (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : Algebra (v.adicCompletion K) (w.1.adicCompletion L) := inferInstance
private noncomputable instance (w : v.Extension B) : Module (v.adicCompletion K) (w.1.adicCompletion L) := inferInstance

private noncomputable instance : CommRing (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : Ring (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : CommSemiring (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : Semiring (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : AddCommGroup (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : AddCommMonoid (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : Algebra (v.adicCompletion K) (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : Module (v.adicCompletion K) (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private noncomputable instance : Algebra L (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private instance : IsTopologicalRing (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance
private instance : IsTopologicalAddGroup (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

end shortcut_instances

namespace adicCompletion

variable (B)

noncomputable def semialgHomPi :
    v.adicCompletion K →ₛₐ[algebraMap K L] ∀ w : v.Extension B, w.1.adicCompletion L :=
  Pi.semialgHom _ _ fun i ↦ i.adicCompletionSemialgHom K L

noncomputable abbrev baseChange :
    L ⊗[K] adicCompletion K v →ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  (semialgHomPi K L B v).baseChange_of_algebraMap

lemma baseChange_tmul_apply (x y w) : baseChange K L B v (x ⊗ₜ y) w =
    (algebraMap _ (w.1.adicCompletion L) x) * (algebraMap _ (w.1.adicCompletion L) y) := rfl

open scoped TensorProduct.RightActions in

noncomputable abbrev baseChangeRight :
    L ⊗[K] adicCompletion K v →ₐ[adicCompletion K v] Π w : v.Extension B, w.1.adicCompletion L :=
  (semialgHomPi K L B v).baseChangeRightOfAlgebraMap

section ModuleTopology

open WithZeroMulInt Valued in

noncomputable local instance :
    Valuation.RankOne (Valued.v : Valuation (adicCompletion K v) ℤᵐ⁰) where
  hom' := (toNNReal (by norm_num : (2 : NNReal) ≠ 0)).comp
    (valueGroup₀_equiv_withZeroMulInt _).toMonoidWithZeroHom
  strictMono' := toNNReal_strictMono (by norm_num) |>.comp
    (valueGroup₀_equiv_withZeroMulInt_strictMono _)
  exists_val_nontrivial := by
    obtain ⟨x, hx1, hx2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    use algebraMap A K x
    rw [valuedAdicCompletion_eq_valuation' v (algebraMap A K x)]
    constructor
    · simpa only [ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    · apply ne_of_lt
      rwa [valuation_of_algebraMap, intValuation_lt_one_iff_mem]

attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

lemma baseChangeRight_surjective [FiniteDimensional K L] :
    Function.Surjective (baseChangeRight K L B v) := by
  let s := (baseChangeRight K L B v).toLinearMap.range
  have isClosed : IsClosed s.carrier :=
    Submodule.closed_of_finiteDimensional (E := (w : Extension B v) → adicCompletion L w.val) s
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, Submodule.eq_top_iff']
  simp_rw [← Submodule.mem_toAddSubmonoid, ← AddSubmonoid.mem_toSubsemigroup,
      ← AddSubsemigroup.mem_carrier]
  have denseL : DenseRange (algebraMap L ((w : Extension B v) → adicCompletion L w.val)) := by
    have := Extension.finite A K L B v
    exact denseRange_of_prodAlgebraMap _ Subtype.val_injective
  rw [← isClosed.closure_eq]
  apply Dense.mono _ denseL
  rintro _ ⟨l, rfl⟩
  use (l ⊗ₜ 1)

  exact SemialgHom.baseChange_of_algebraMap_tmul_left (semialgHomPi K L B v) l

attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

instance [FiniteDimensional K L] :
    Module.Finite (adicCompletion K v) (Π w : v.Extension B, w.1.adicCompletion L) :=
  .of_surjective (baseChangeRight K L B v).toLinearMap (baseChangeRight_surjective K L B v)

attribute [local instance 9999] Algebra.toModule in

instance [FiniteDimensional K L] (w : v.Extension B) :
    Module.Finite (adicCompletion K v) (adicCompletion L w.1) :=
  Module.Finite.of_pi (fun (w : Extension B v) => w.1.adicCompletion L) w

instance instIsModuleTopology [FiniteDimensional K L] (w : v.Extension B) :
    IsModuleTopology (v.adicCompletion K) (w.1.adicCompletion L) := by
  let Kv := adicCompletion K v
  let Lw := adicCompletion L w.1
  let iso : ((Fin (Module.finrank Kv Lw)) → Kv) ≃L[Kv] Lw :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun Kv)
  apply IsModuleTopology.iso iso

instance instIsModuleTopologyPi [FiniteDimensional K L] :

    IsModuleTopology (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) := by
  let := Extension.finite A K L B v
  exact IsModuleTopology.instPi

open scoped TensorProduct.RightActions in

lemma baseChangeRight_isOpenQuotientMap [FiniteDimensional K L] :
    IsOpenQuotientMap (baseChangeRight K L B v) := by
  have : T2Space (L ⊗[K] adicCompletion K v) :=
    IsModuleTopology.t2Space' (K := (adicCompletion K v))
  have hsurj := baseChangeRight_surjective K L B v
  rw [← AlgHom.coe_toLinearMap]
  exact ⟨hsurj, LinearMap.continuous_of_finiteDimensional _,
    LinearMap.isOpenMap_of_finiteDimensional _ hsurj⟩

end ModuleTopology

end adicCompletion

section ModuleTopology

open Extension adicCompletion

variable (B)

noncomputable def tensorAdicCompletionIntegersTo :
    B ⊗[A] adicCompletionIntegers K v →ₐ[B] L ⊗[K] adicCompletion K v :=
  Algebra.TensorProduct.lift
    (Algebra.algHom _ _ _)
    ((Algebra.TensorProduct.includeRight.restrictScalars A).comp (IsScalarTower.toAlgHom _ _ _))
    (fun _ _ ↦ .all _ _)

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
@[simp]
lemma tensorAdicCompletionIntegersTo_tmul (v : HeightOneSpectrum A) (b : B)
    (x : v.adicCompletionIntegers K) : tensorAdicCompletionIntegersTo K L B v (b ⊗ₜ x) =
      (algebraMap B L b) ⊗ₜ x.val := by
  simp [tensorAdicCompletionIntegersTo, Algebra.algHom]

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
open scoped TensorProduct.RightActions in

lemma tensorAdicCompletionIntegersTo_range_subset_closure [FiniteDimensional K L] :
  (tensorAdicCompletionIntegersTo K L B v).range.carrier ⊆
    closure (algebraMap B (L ⊗[K] adicCompletion K v)).range := by
  rintro _ ⟨s, rfl⟩
  induction s with
    | zero =>
        apply subset_closure
        use 0
        simp
    | add x y hx hy =>

        rw [RingHom.map_add]
        apply map_mem_closure₂ _ hx hy _
        · exact (ModuleTopology.continuousAdd _ _).continuous_add
        intro _ ha _ hb
        exact add_mem ha hb
    | tmul b a' =>

        simp only [RingHom.coe_range, tensorAdicCompletionIntegersTo,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
          AlgHom.coe_comp, AlgHom.coe_restrictScalars', IsScalarTower.coe_toAlgHom',
          Function.comp_apply, ValuationSubring.algebraMap_apply,
          Algebra.TensorProduct.includeRight_apply]

        let f (y : ↥(adicCompletionIntegers K v)) : (L ⊗[K] adicCompletion K v) :=
          (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b * (1 : L) ⊗ₜ[K] (y : adicCompletion K v)
        have hfval : f = fun (y : ↥(adicCompletionIntegers K v)) =>
              (y : adicCompletion K v) • (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b := by
          ext y
          unfold f
          rw [Algebra.smul_def]
          exact mul_comm _ _
        have hcf : ContinuousAt f a' := by
          apply Continuous.continuousAt
          rw [hfval]
          exact continuous_subtype_val.fun_smul continuous_const

        have hy : a' ∈ closure (Set.range (algebraMap A _)) := by
          apply denseRange_of_integerAlgebraMap
        apply mem_closure_image hcf hy
        constructor
        · exact isClosed_closure

        rintro u ⟨_, ⟨a, rfl⟩, rfl⟩
        apply subset_closure
        use algebraMap A B a * b
        unfold f
        rw [Algebra.algebraMap_eq_smul_one (A := (adicCompletionIntegers K v)) a,
          coe_smul_adicCompletionIntegers, ← TensorProduct.smul_tmul, Algebra.ofId_apply,
          Algebra.TensorProduct.algebraMap_apply, RingHom.map_mul, ← Algebra.smul_def]
        simp

open scoped TensorProduct.RightActions in
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L]  in

lemma tensorAdicCompletionIntegersTo_isClopen_range
    [IsIntegralClosure B A L] [FiniteDimensional K L] :
    IsClopen (SetLike.coe (tensorAdicCompletionIntegersTo K L B v).range) := by

  have : SeparatelyContinuousAdd (L ⊗[K] v.adicCompletion K) :=
    instSeparatelyContinuousAddOfContinuousAdd
  rw [← Subalgebra.coe_toSubring, ← Subring.coe_toAddSubgroup]
  refine OpenAddSubgroup.isClopen ⟨_, ?_⟩

  apply AddSubgroup.isOpen_of_zero_mem_interior
  rw [mem_interior, Subring.coe_toAddSubgroup, Subalgebra.coe_toSubring]

  obtain ⟨ι, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' : Module.Basis ι (adicCompletion K v) (L ⊗[K] (adicCompletion K v)) := by
    classical
    exact b.rightBaseChange L

  let equiv : L ⊗[K] (adicCompletion K v) ≃L[v.adicCompletion K] (ι → adicCompletion K v) :=
    IsModuleTopology.continuousLinearEquiv (b'.equivFun)

  use equiv.symm '' (Set.pi Set.univ (fun _ => SetLike.coe (adicCompletionIntegers K v)))
  refine ⟨?_, ?_, by simp⟩
  · intro t ⟨g, hg, ht⟩

    have hf : ∀ (i : ι), ∃ (w : B), (algebraMap B L w) = (b i) := by
      intro i
      apply IsIntegralClosure.isIntegral_iff.mp (hb i)
    choose f hf_prop using hf
    let b : B ⊗[A] ↥(adicCompletionIntegers K v) := ∑ (i : ι), (f i) ⊗ₜ ⟨g i, hg i trivial⟩
    use b
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, ← ht]
    unfold equiv
    rw [IsModuleTopology.continuousLinearEquiv_symm_apply, Module.Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro x
    simp only [Finset.univ_eq_attach, Finset.mem_attach, tensorAdicCompletionIntegersTo_tmul,
      hf_prop, Module.Basis.rightBaseChange_apply, Algebra.smul_def,
      TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, imp_self, b']
  · rw [ContinuousLinearEquiv.image_symm_eq_preimage]
    apply IsOpen.preimage equiv.continuous
    apply isOpen_set_pi Set.finite_univ
    rintro i -
    exact Valued.isOpen_valuationSubring (v.adicCompletion K)

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
open scoped TensorProduct.RightActions in

lemma range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap
    [IsIntegralClosure B A L] [FiniteDimensional K L] :
    Set.range (tensorAdicCompletionIntegersTo K L B v) =
      closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) := by
  apply Set.Subset.antisymm
  · apply tensorAdicCompletionIntegersTo_range_subset_closure
  · apply closure_minimal
    · rintro _ ⟨b, rfl⟩
      use b ⊗ₜ[A] 1
      simp
    · apply IsClopen.isClosed
      apply tensorAdicCompletionIntegersTo_isClopen_range

omit [Algebra A L] [IsScalarTower A B L] in

lemma pi_adicCompletionIntegers_eq_closure_range_algebraMap :
    (Set.univ.pi (fun (w : Extension B v) ↦ (w.1.adicCompletionIntegers L).carrier)) =
      closure (Set.range (algebraMap B _)) := by
  let val := fun (w : Extension B v) ↦ w.1
  have hinj : Function.Injective val :=
    (Set.injective_codRestrict Subtype.property).mp fun _ _ a ↦ a
  rw [← closureAlgebraMapIntegers_eq_prodIntegers L _ hinj]
  rfl

open scoped TensorProduct.RightActions in

lemma isClosed_baseChange_image_closure_range_algebraMap [FiniteDimensional K L] :
    IsClosed ((baseChange K L B v) ''
        closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v)))) := by
  let S := AddSubgroup.map
      (baseChange K L B v).toAddMonoidHom
      (tensorAdicCompletionIntegersTo K L B v).range.toSubring.toAddSubgroup
  have hSclosed : IsClosed S.carrier := by
    apply AddSubgroup.isClosed_of_isOpen
    apply (baseChangeRight_isOpenQuotientMap K L B v).isOpenMap
    apply (tensorAdicCompletionIntegersTo_isClopen_range K L B v).isOpen
  suffices h : (baseChange K L B v) ''
    closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) = S.carrier by
    rwa [h]
  rw [← range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap]
  rfl

instance : MulActionHomClass
    (L ⊗[K] adicCompletion K v →ₐ[L] (w : Extension B v) → adicCompletion L w.1) B
    (L ⊗[K] adicCompletion K v) ((w : Extension B v) → adicCompletion L w.1) where
  map_smulₛₗ φ b x := by
    rw [← IsScalarTower.algebraMap_smul L, AlgHom.map_smul_of_tower,
      IsScalarTower.algebraMap_smul, id_def]

open scoped TensorProduct.RightActions in

theorem range_baseChange_comp_tensorAdicCompletionTo_eq_pi [FiniteDimensional K L] :
    Set.range (baseChange K L B v ∘ tensorAdicCompletionIntegersTo K L B v) =
    Set.univ.pi (fun w ↦ (w.1.adicCompletionIntegers L).carrier) := by
  have hrange :
    Set.range (algebraMap B ((w : Extension B v) → adicCompletion L w.1)) =
      (baseChange K L B v) '' (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]
  have hrange' := isClosed_baseChange_image_closure_range_algebraMap K L B v
  rw [Set.range_comp, range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap,
    pi_adicCompletionIntegers_eq_closure_range_algebraMap, hrange, ← IsClosed.closure_eq hrange']
  exact closure_image_closure
    (baseChangeRight_isOpenQuotientMap K L B v).continuous

namespace Extension

variable {B} (w : v.Extension B)

noncomputable def adicCompletionIntegersRingHom :
    v.adicCompletionIntegers K →+* w.1.adicCompletionIntegers L :=
  RingHom.restrict (w.adicCompletionSemialgHom K L) _ _
    fun x hx ↦ w.adicCompletionSemialgHom_image_adicCompletionIntegers K L ⟨x, hx, rfl⟩

noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  (w.adicCompletionIntegersRingHom K L).toAlgebra

lemma integer_algebraMap_apply (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) x =
      (w.adicCompletionSemialgHom K L) x.val := rfl

variable {v} in

noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletion L) :=
  Algebra.compHom (w.1.adicCompletion L) (algebraMap _ (adicCompletion K v))

end Extension

open scoped TensorProduct.RightActions in
instance : IsBiscalar B (v.adicCompletionIntegers K) (tensorAdicCompletionIntegersTo K L B v) where
  map_smul₁ _ _ := map_smul ..
  map_smul₂ _ _ := by
    simp only [tensorAdicCompletionIntegersTo_tmul, Algebra.smul_def,
      TensorProduct.RightActions.algebraMap_eval, map_mul, map_one]
    rfl

attribute [local instance 9999] Algebra.toModule Algebra.toSMul in
instance {w : v.Extension B} : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v)
    (w.1.adicCompletion L) := Submonoid.instIsScalarTowerSubtypeMem (adicCompletionIntegers K v)

open scoped TensorProduct.RightActions in

noncomputable def tensorAdicCompletionIntegersToPiRight :
    B ⊗[A] v.adicCompletionIntegers K →ₐ[v.adicCompletionIntegers K]
        Π w : v.Extension B, w.1.adicCompletion L :=
  ((baseChangeRight K L B v).restrictScalars _).comp
    ((tensorAdicCompletionIntegersTo K L B v).changeScalars _)

namespace Extension

variable (w : v.Extension B)

open scoped TensorProduct.RightActions in

noncomputable def tensorAdicCompletionIntegersToAdicCompletion :
    B ⊗[A] (adicCompletionIntegers K v) →ₐ[adicCompletionIntegers K v] adicCompletion L w.1 :=
  Pi.evalAlgHom _ _ w |>.comp (tensorAdicCompletionIntegersToPiRight K L B v)

open scoped TensorProduct.RightActions in

lemma tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers [FiniteDimensional K L] :
    Set.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v) =
      adicCompletionIntegers L w.1 := by
  ext x
  have memrange := (range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L B v)
  rw [Set.ext_iff] at memrange
  constructor
  · rintro ⟨y, rfl⟩
    exact (memrange _).mp (Set.mem_range_self y) w trivial
  · intro hx
    classical
    set x' : (w : Extension B v) → adicCompletion L w.val := Pi.single w x with hx'
    obtain ⟨y, (hy : _ = x')⟩ : x' ∈ Set.range _ := by
      rw [memrange x', Set.mem_pi]
      intro w' _
      by_cases h : w = w'
      · rw [← h, hx', Pi.single_eq_same]
        exact hx
      · rw [hx', Pi.single_eq_of_ne' h]
        exact Subring.zero_mem _
    use y
    have hyw := congr_fun hy w
    simp [hx'] at hyw
    exact hyw

noncomputable local instance : MulAction (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  LieAlgebra.ofAssociativeAlgebra.toMulAction

attribute [local instance 9999] Algebra.toSMul Algebra.toModule in
open scoped TensorProduct.RightActions in

noncomputable instance (priority := 1001) [Module.Finite A B] [FiniteDimensional K L] :
    Module.Finite (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
  let integerSubmodule : Submodule (adicCompletionIntegers K v) (adicCompletion L w.1) :=
    let : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L).toSubring :=
      inferInstanceAs (Algebra (adicCompletionIntegers K v) (adicCompletionIntegers L w.1))
    have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
        (adicCompletion L w.1) := .of_algebraMap_smul fun _ _ ↦ rfl
    (adicCompletionIntegers L w.1).toSubmodule.restrictScalars
      (adicCompletionIntegers K v)
  have heq : (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap.range =
      integerSubmodule := by
    ext x
    apply w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L B v |> Set.ext_iff.mp
  have := Module.Finite.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap
  have := w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L B v
  exact Module.Finite.equiv <| LinearEquiv.ofEq
    (LinearMap.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap) _ heq

end Extension

end ModuleTopology

namespace adicCompletion

open Extension

section RamificationInertia

variable {v} (w : v.Extension B)

lemma _root_.WithZero.ofAdd_neg_ofNat_pow (n : ℕ) :
    (WithZero.coe (Multiplicative.ofAdd (-n : ℤ))) = (Multiplicative.ofAdd (-1 : ℤ)) ^ n := by
  rw [← WithZero.coe_pow, ← ofAdd_nsmul, nsmul_eq_mul, Int.mul_neg_one]

theorem ramificationIdx_eq_ramificationIdx :
    (v.completionIdeal K).ramificationIdx' (w.1.completionIdeal L) =
      v.asIdeal.ramificationIdx' w.1.asIdeal := by
  apply Ideal.ramificationIdx_spec
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [mem_completionIdeal_iff'] at hx
    rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow, integer_algebraMap_apply,
      valued_adicCompletionSemialgHom]
    rw [WithZero.ofAdd_neg_ofNat_pow, w.2]
    apply pow_le_pow_left' hx
  · obtain ⟨ϖ, hϖ⟩ := adicCompletion.exists_uniformizer K v
    have hϖ' : ϖ ∈ v.completionIdeal K := by
      rw [mem_completionIdeal_iff, hϖ]
      decide
    rw [Ideal.map_le_iff_le_comap]
    intro h
    have hcomap := h hϖ'
    rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow, integer_algebraMap_apply,
      valued_adicCompletionSemialgHom, hϖ, ← WithZero.ofAdd_neg_ofNat_pow,
      WithZero.coe_le_coe, w.2, Multiplicative.ofAdd_le] at hcomap
    simp at hcomap

theorem inertiaDeg_eq_inertiaDeg :
    v.asIdeal.inertiaDeg' w.1.asIdeal = (v.completionIdeal K).inertiaDeg' (w.1.completionIdeal L) :=
  letI := Algebra.compHom (adicCompletionIntegers L w.1) (algebraMap A B)
  have : IsScalarTower A B (adicCompletionIntegers L w.1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    ext
    rw [Algebra.compHom_algebraMap_eq, RingHom.coe_comp, Function.comp_apply,
      algebraMap_completionIntegers, integer_algebraMap_apply, algebraMap_completionIntegers,
      IsScalarTower.algebraMap_apply B L (adicCompletion L w.1),
      ← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
    symm
    apply SemialgHom.commutes
  have : w.1.asIdeal.LiesOver v.asIdeal := ⟨by simp_rw [← w.2]; rfl⟩

  have : (completionIdeal L w.1).LiesOver (completionIdeal K v) := {
    «over» := by
      rw [Ideal.under_def]
      ext x
      rw [Ideal.mem_comap, mem_completionIdeal_iff, mem_completionIdeal_iff,
        integer_algebraMap_apply, valued_adicCompletionSemialgHom K L, pow_lt_one_iff]
      exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1
  }
  calc v.asIdeal.inertiaDeg' w.1.asIdeal
      = v.asIdeal.inertiaDeg' (w.1.completionIdeal L) := by
        rw [Ideal.inertiaDeg_algebra_tower v.asIdeal w.1.asIdeal (w.1.completionIdeal L),
          inertiaDeg_asIdeal_completionIdeal, mul_one]
    _ = (v.completionIdeal K).inertiaDeg' (w.1.completionIdeal L) := by
        rw [Ideal.inertiaDeg_algebra_tower v.asIdeal (v.completionIdeal K) (w.1.completionIdeal L),
          inertiaDeg_asIdeal_completionIdeal, one_mul]

noncomputable local instance : MulAction (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  LieAlgebra.ofAssociativeAlgebra.toMulAction

theorem ramificationIdx_mul_inertiaDeg_eq_finrank [FiniteDimensional K L] [Module.Finite A B] :
    v.asIdeal.ramificationIdx' w.1.asIdeal * v.asIdeal.inertiaDeg' w.1.asIdeal =
      Module.finrank (adicCompletion K v) (adicCompletion L w.1) := by
  have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
      (adicCompletion L w.1) := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v) (adicCompletion L w.1) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  rw [← Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (adicCompletionIntegers L w.1)
    (adicCompletion K v) (adicCompletion L w.1) (v.completionIdeal_ne_bot K),
    ramificationIdx_eq_ramificationIdx, inertiaDeg_eq_inertiaDeg K L w]

end RamificationInertia

variable [FiniteDimensional K L] [Module.Finite A B] (B)
variable (v : HeightOneSpectrum A) (w : v.Extension B)

local instance : Module.Free (v.adicCompletion K) (adicCompletion L w.1) :=
  Module.free_of_finite_type_torsion_free'

open scoped TensorProduct.RightActions in

lemma finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion :
    Module.finrank (adicCompletion K v) (L ⊗[K] adicCompletion K v) =
      Module.finrank (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
  letI := Extension.fintype A K L B v
  calc Module.finrank (adicCompletion K v) (L ⊗[K] adicCompletion K v)
    _ = Module.finrank K L := by rw [TensorProduct.finrank_rightAlgebra]
    _ = ∑ (w : Extension B v), Ideal.ramificationIdx' v.asIdeal w.val.asIdeal *
        Ideal.inertiaDeg' v.asIdeal w.val.asIdeal := by
        rw [Ideal.sum_ramification_inertia_extensions]
    _ = ∑ (w : Extension B v), Module.finrank (adicCompletion K v) (adicCompletion L w.val) :=
        Finset.sum_congr rfl fun w _ ↦ ramificationIdx_mul_inertiaDeg_eq_finrank K L w
    _ = Module.finrank (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) := by
        rw [Module.finrank_pi_fintype (adicCompletion K v)]

attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

theorem baseChange_bijective : Function.Bijective (baseChange K L B v) := by
  change Function.Bijective (baseChangeRight K L B v)
  have hsurj := baseChangeRight_surjective K L B v
  refine ⟨?_, hsurj⟩
  have hrank := finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion K L B v
  rwa [← AlgHom.coe_toLinearMap, LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank]

noncomputable def baseChangeAlgEquiv :
    L ⊗[K] v.adicCompletion K ≃ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  AlgEquiv.ofBijective (baseChange K L B v) <| baseChange_bijective K L B v

open scoped TensorProduct.RightActions in

private lemma rightActions_smul_tmul_right {R S M : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid M] [Module R M] (s : S) (m : M) (t : S) :
    s • (m ⊗ₜ[R] t) = m ⊗ₜ[R] (s * t) := by
  rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
    smul_eq_mul, TensorProduct.comm_symm_tmul]

open scoped TensorProduct.RightActions in

private lemma rightActions_smul_eq_one_tmul_mul {R S M : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [CommSemiring M] [Algebra R M] (s : S) (x : M ⊗[R] S) :
    s • x = (1 ⊗ₜ[R] s) * x := by
  induction x with
  | zero => simp
  | add a b ha hb => rw [smul_add, mul_add, ha, hb]
  | tmul m t => rw [rightActions_smul_tmul_right, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

noncomputable def baseChangeContinuousAlgEquiv :
    L ⊗[K] v.adicCompletion K ≃A[L] Π w : v.Extension B, w.1.adicCompletion L :=

  have : IsBiscalar L (v.adicCompletion K) (baseChangeAlgEquiv K L B v).toAlgHom :=
    { map_smul₁ := fun l x => by exact (baseChange K L B v).toLinearMap.map_smul l x
      map_smul₂ := fun s x => by
        rw [rightActions_smul_eq_one_tmul_mul, map_mul]
        funext w
        rw [Pi.mul_apply, Pi.smul_apply, Algebra.smul_def]
        congr 1

        show baseChange K L B v (1 ⊗ₜ[K] s) w = algebraMap (adicCompletion K v) (adicCompletion L w.1) s
        rw [baseChange_tmul_apply, map_one, one_mul] }
  IsModuleTopology.continuousAlgEquivOfIsBiscalar (v.adicCompletion K)
    (baseChangeAlgEquiv K L B v)

noncomputable def integerBaseChangeLinearEquiv :
    B ⊗[A] v.adicCompletion K ≃ₗ[B] ∀ w : v.Extension B, w.1.adicCompletion L :=
  (linearEquivTensorProductModuleLeft A K L B (v.adicCompletion K)).symm.trans
    ((baseChangeAlgEquiv K L B v).toLinearEquiv.restrictScalars B)

@[simp]
lemma integerBaseChangeLinearEquiv_tmul_apply (b x) :
    integerBaseChangeLinearEquiv K L B v (b ⊗ₜ[A] x) w =
      algebraMap B _ b * algebraMap _ _ x := by
  rw [integerBaseChangeLinearEquiv, LinearEquiv.trans_apply,
    linearEquivTensorProductModuleLeft_symm_tmul]
  rfl

noncomputable def integerSubmodule (v : HeightOneSpectrum A) : Submodule A (adicCompletion K v) :=
  let s : Submodule (adicCompletionIntegers K v) _ := (adicCompletionIntegers K v).toSubmodule
  s.restrictScalars A

end adicCompletion

namespace adicCompletionIntegers

open adicCompletion

variable (B)

noncomputable def tensorCoe : B ⊗[A] v.adicCompletionIntegers K →ₗ[B] B ⊗[A] v.adicCompletion K :=
  TensorProduct.AlgebraTensorModule.lTensor _ _
    (Algebra.algHom A (adicCompletionIntegers K v) (adicCompletion K v))

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] in
@[simp]
lemma tensorCoe_tmul (b : B) (x : v.adicCompletionIntegers K) :
    tensorCoe K B v (b ⊗ₜ x) = b ⊗ₜ x.val := rfl

end adicCompletionIntegers

namespace adicCompletion

open Extension

variable [FiniteDimensional K L] [Module.Finite A B]

attribute [local instance 9999] SMulCommClass.of_commMonoid TensorProduct.isScalarTower_left
  IsScalarTower.right in
theorem integerBaseChangeLinearEquiv_bijOn (v : HeightOneSpectrum A) :
    Set.BijOn (integerBaseChangeLinearEquiv K L B v)
      (Set.range (adicCompletionIntegers.tensorCoe K B v))
      (Submodule.pi Set.univ fun (w : Extension B v) ↦ integerSubmodule L w.val) := by
  suffices h : ((integerBaseChangeLinearEquiv K L B v) ''
      (LinearMap.range (adicCompletionIntegers.tensorCoe K B v))) =
      Submodule.pi .univ fun (w : Extension B v) ↦ (integerSubmodule L w.val).restrictScalars A from
    h ▸ Equiv.bijOn_image (integerBaseChangeLinearEquiv K L B v).toEquiv
  apply Eq.trans _ (range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L B v)
  rw [LinearMap.coe_range, ← Set.range_comp, ← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  rw [← AlgHom.coe_restrictScalars' B (baseChange K L B v), ← AlgHom.coe_comp,
    ← AlgHom.coe_toLinearMap]
  congr
  ext
  simp [baseChange_tmul_apply]

end IsDedekindDomain.HeightOneSpectrum.adicCompletion


