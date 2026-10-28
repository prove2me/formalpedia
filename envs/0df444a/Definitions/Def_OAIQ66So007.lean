-- Prove2me | Definitions.Def_OAIQ66So007
-- name    : OAIQ66So007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:11:54.662037+00:00
-- url     : https://prove2.me/theorems/3521d761-761b-420a-989e-564cc739c78d
-- title:
--   Definitions bundle OAIQ66So007 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 247 declarations of OpenAI's Lean: 116 definitions, 12 inductive types or structures, 3 instances and 116 theorems. The definitions and types are `OAI.ListChains.CoefficientProduct`, `OAI.ListChains.Shape`, `OAI.ListChains.iterateHom`, `OAI.ListChains.shiftOrigin`, `OAI.ListChains.simplexTypes`, `OAI.ListChains.symmetricClosure`, `OAI.ListChains.tupleShapeEquiv`, `OAI.LocalNilpotence.IsLocallyNilpotent`, `OAI.LocalNilpotence.partialSum`, `OAI.NoncommElementary.columnAction`, `OAI.NoncommElementary.columnPerm`, `OAI.NoncommElementary.diagonal`, `OAI.NoncommElementary.position`, `OAI.OrbitCoefficients.Orbits`, `OAI.OrbitModule.Presentation`, `OAI.OrbitModule.Presentation.ofIso`, `OAI.OrderBasedComplex.Contraction`, `OAI.OrderBasedComplex.Data`, `OAI.OrderBasedComplex.chosenBasis`, `OAI.OrderBasedComplex.chosenExtend`, `OAI.OrderBasedComplex.chosenHomotopy`, `OAI.OrderBasedComplex.chosenHomotopyBasis`, `OAI.OrderBasedComplex.extend`, `OAI.OrderBasedComplex.extendBasis`, `OAI.OrderBasedComplex.homotopy`, `OAI.OrderBasedComplex.homotopyBasis`, `OAI.OrderChains.project`, `OAI.PosetTransport.belowEmbed`, `OAI.PosetTransport.linkBelow`, `OAI.PosetTransport.rankAbove`, `OAI.PosetTransport.rankBelow`, `OAI.PosetTransport.rankEmbed`, `OAI.PosetTransport.rankFiberIso`, `OAI.PosetTransport.rankStep`, `OAI.PrefixPermutation.complement`, `OAI.PrefixPermutation.matrixPart`, `OAI.PrefixPermutation.support`, `OAI.PrefixPermutation.value`, `OAI.ProductCoefficient.Module`, `OAI.ProductCoefficient.affineShift` and 88 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_BinaryPrefixOperators`, `FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts`, `FiniteType_CosetCoordinates`, `FiniteType_InducedFree`, `FiniteType_ListChainsHasPropagation`, `FiniteType_ListChainsMapChainComp`, `FiniteType_ListChainsShiftOrigin`, `FiniteType_OrderBasedComplex`, `FiniteType_OrderChainsExactInOfTop`, `FiniteType_OrderChainsOnSet`, `FiniteType_PosetTransport`, `FiniteType_PrefixPermutation`, `FiniteType_ProductCoefficient`, `FiniteType_ProductCoefficientAffineShift`, `FiniteType_ProductCriterion`, `FiniteType_ProductFiniteResolution`, `FiniteType_Representation`, `FiniteType_SequentialLimit`, `FiniteType_StandardHomology`, `FiniteType_SteinbergSixThree`, `FiniteType_SurjectiveTrivialInduction`, `FiniteType_UniformProductSupport`, `SimpleOvergroups_BoundedContexts`, `SimpleOvergroups_BoundedForms`, `SimpleOvergroups_EffectiveActions`, `SimpleOvergroups_EffectiveFold`, `SimpleOvergroups_EnlargementCore`, `SimpleOvergroups_NamedActions`, `SimpleOvergroups_PlanEffective`, `SimpleOvergroups_Rekey`, `SimpleOvergroups_TruncatedAction`, `SimpleOvergroups_TruncatedAlgebra`, `SimpleOvergroups_TruncatedArrays`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So013`, `OAIQ66So014` and `OAIQ66So015`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductFiniteResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ProductFiniteResolution

open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidAlgebra

variable {k G : Type} [CommRing k] [Group G]

structure FreeCover (C : Rep k G) where
  ι : Type
  π : Rep.free k G ι ⟶ C
  surjective : Function.Surjective π.hom
  finite_of : Module.Finite k[G] C.ρ.asModule → Finite ι

structure Beginning (Z : Rep k G) where
  α₀ : Type
  α₁ : Type
  α₂ : Type
  [finite₀ : Finite α₀]
  [finite₁ : Finite α₁]
  [finite₂ : Finite α₂]
  d₁ : Rep.free k G α₁ ⟶ Rep.free k G α₀
  d₂ : Rep.free k G α₂ ⟶ Rep.free k G α₁
  ε : Rep.free k G α₀ ⟶ Z
  d₂_d₁ : d₂ ≫ d₁ = 0
  d₁_ε : d₁ ≫ ε = 0
  exact₁ : (ShortComplex.mk d₂ d₁ d₂_d₁).Exact
  exact₀ : (ShortComplex.mk d₁ ε d₁_ε).Exact
  [epi_ε : Epi ε]

attribute [instance] Beginning.finite₀ Beginning.finite₁ Beginning.finite₂ Beginning.epi_ε

end ProductFiniteResolution

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsHasPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G H : Type*) [Group G] [Group H]

lemma hom_image_propagation (f : G →* H) {V : Set G} {A : Set G}
    (h : ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y ∈ A) :
    ∀ x ∈ f '' V, ∀ y ∈ f '' V, x⁻¹ * y ∈ f '' A := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  exact ⟨x⁻¹*y, h x hx y hy, by simp only [map_mul, map_inv]⟩

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsMapChainComp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*)

variable [Group G]

open scoped Pointwise

def symmetricClosure (S : Set G) : Set G := insert 1 (S ∪ S⁻¹)

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryPrefixOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains
section

variable (G : Type*) [Group G]

def iterateHom (f : G →* G) : ℕ → G →* G
  | 0 => MonoidHom.id G
  | k+1 => f.comp (iterateHom f k)
@[simp] lemma iterateHom_zero (f : G →* G) : iterateHom G f 0 = MonoidHom.id G := rfl
@[simp] lemma iterateHom_one (f : G →* G) : iterateHom G f 1 = f := by ext; rfl

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsShiftOrigin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*) [Group G] {C : Type*}

def shiftOrigin (f : G →* G) (σ : C → C) (δ : C → G) : ℕ → C → G
  | 0, _ => 1
  | k+1, c => δ (σ^[k] c) * f (shiftOrigin f σ δ k c)

end

section

variable (G : Type*) [Group G]

def simplexTypes (A : Set G) (n : ℕ) : Set (List G) :=
  {l | l.length = n ∧ ∀ x ∈ l, x ∈ A}

omit [Group G] in
lemma simplexTypes_finite {A : Set G} (hA : A.Finite) (n : ℕ) :
    (simplexTypes G A n).Finite := by
  induction n with
  | zero =>
    apply (Set.finite_singleton []).subset
    intro l hl
    exact List.length_eq_zero_iff.mp hl.1
  | succ n ih =>
    apply ((hA.prod ih).image (fun p : G × List G => p.1 :: p.2)).subset
    intro l hl
    cases l with
    | nil => simp [simplexTypes] at hl
    | cons a l =>
      refine ⟨(a,l),⟨hl.2 a (List.mem_cons_self),?_⟩,rfl⟩
      refine ⟨by simpa using hl.1,fun x hx => hl.2 x ?_⟩
      exact List.mem_cons_of_mem _ hx

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_UniformProductSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace UniformProductSupport

variable {R I S M : Type*} [Ring R] [AddCommGroup M] [Module R M]

def evaluate (i : I) : (S →₀ (I → M)) →ₗ[R] (S →₀ M) :=
  Finsupp.mapRange.linearMap (LinearMap.proj i)

@[simp] lemma evaluate_apply (i : I) (c : S →₀ (I → M)) (s : S) :
    evaluate (R := R) (I := I) (S := S) (M := M) i c s = c s i := rfl

lemma evaluate_support_subset (i : I) (c : S →₀ (I → M)) :
    (evaluate (R := R) (I := I) (S := S) (M := M) i c).support ⊆ c.support := by
  change (Finsupp.mapRange (fun m : I → M => m i) rfl c).support ⊆ c.support
  exact Finsupp.support_mapRange

lemma evaluate_injective : Function.Injective
    (fun c : S →₀ (I → M) => fun i => evaluate (R := R) (I := I) (S := S) (M := M) i c) := by
  intro c d h
  ext s i
  exact congrArg (fun v : I → S →₀ M => v i s) h

theorem exists_lift_iff (z : I → S →₀ M) :
    (∃ c : S →₀ (I → M), ∀ i, evaluate (R := R) (I := I) (S := S) (M := M) i c = z i) ↔
      ∃ T : Finset S, ∀ i, (z i).support ⊆ T := by
  classical
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c.support,?_⟩
    intro i
    rw [← hc i]
    exact evaluate_support_subset i c
  · rintro ⟨T,hT⟩
    let c : S →₀ (I → M) := Finsupp.onFinset T (fun s i => z i s) (by
      intro s hs
      by_contra h
      apply hs
      funext i
      exact Finsupp.notMem_support_iff.mp (fun hz => h (hT i hz)))
    refine ⟨c,?_⟩
    intro i
    ext s
    rfl

end UniformProductSupport

namespace ListChains

variable (G I C : Type*) [Group G]

abbrev Shape (n : ℕ) := {l : List G // l.length = n}
abbrev CoefficientProduct := I → (C × G →₀ ℤ)

def tupleShapeEquiv (n : ℕ) : (Fin n → G) ≃ Shape G n where
  toFun s := ⟨List.ofFn s,List.length_ofFn⟩
  invFun l := fun i => l.val.get ⟨i.val,by have h := l.property; omega⟩
  left_inv := by intro s;funext i;simp
  right_inv := by
    rintro ⟨l,hl⟩
    subst n
    apply Subtype.ext
    exact List.ofFn_getElem

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ProductCoefficient
variable (G I C : Type*) [Group G]

abbrev Module := I → (C × G →₀ ℤ)

def rightShift (g : G) : (C × G →₀ ℤ) →ₗ[ℤ] (C × G →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (p.1,p.2*g⁻¹))

@[simp] lemma rightShift_single (g : G) (c : C) (u : G) (r : ℤ) :
    rightShift G C g (Finsupp.single (c,u) r) = Finsupp.single (c,u*g⁻¹) r := by
  simp [rightShift]

lemma rightShift_one : rightShift G C 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro ⟨c,u⟩ r
  simp

lemma rightShift_mul (g h : G) :
    rightShift G C (g*h) = (rightShift G C g).comp (rightShift G C h) := by
  apply Finsupp.lhom_ext
  rintro ⟨c,u⟩ r
  simp [mul_assoc]

def representation : Representation ℤ G (Module G I C) where
  toFun g := LinearMap.pi (fun i => (rightShift G C g).comp (LinearMap.proj i))
  map_one' := by
    apply LinearMap.ext
    intro z
    funext i
    exact congrArg (fun f : (C × G →₀ ℤ) →ₗ[ℤ] (C × G →₀ ℤ) => f (z i)) (rightShift_one G C)
  map_mul' g h := by
    apply LinearMap.ext
    intro z
    funext i
    exact congrArg (fun f : (C × G →₀ ℤ) →ₗ[ℤ] (C × G →₀ ℤ) => f (z i)) (rightShift_mul G C g h)

@[simp] lemma representation_apply (g : G) (z : Module G I C) (i : I) :
    representation G I C g z i = rightShift G C g (z i) := rfl

abbrev rep : Rep ℤ G := Rep.of (representation G I C)

end ProductCoefficient

open _root_.CategoryTheory
namespace RelativeStandardFree
variable (k G : Type) [CommRing k] [Group G]

def basisEquiv (n : ℕ) : (Fin (n+1) → G) ≃ ((Fin n → G) × G) where
  toFun c := (fun i => (c 0)⁻¹ * c i.succ, c 0)
  invFun p := Fin.cons p.2 (fun i => p.2 * p.1 i)
  left_inv := by
    intro c
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv := by
    rintro ⟨s,g⟩
    simp

def linearEquiv (n : ℕ) : MonoidAlgebra k (Fin (n+1) → G) ≃ₗ[k]
    ((Fin n → G) →₀ MonoidAlgebra k G) :=
  (MonoidAlgebra.coeffLinearEquiv k).trans
    ((Finsupp.lcongr (basisEquiv G n) (LinearEquiv.refl k k)).trans
      ((Finsupp.curryLinearEquiv k).trans
        (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm)))

@[simp] lemma linearEquiv_single (n : ℕ) (c : Fin (n+1) → G) (r : k) :
    linearEquiv k G n (MonoidAlgebra.single c r) =
      Finsupp.single (fun i => (c 0)⁻¹*c i.succ) (MonoidAlgebra.single (c 0) r) := by
  simp [linearEquiv,basisEquiv]

lemma linearEquiv_intertwines (n : ℕ) (g : G) :
    (linearEquiv k G n).toLinearMap.comp ((Rep.diagonal k G (n+1)).ρ g) =
      ((Rep.free k G (Fin n → G)).ρ g).comp (linearEquiv k G n).toLinearMap := by
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change linearEquiv k G n ((Representation.diagonal k G (n+1)) g
      (MonoidAlgebra.single c 1)) = (Representation.free k G (Fin n → G)) g
      (linearEquiv k G n (MonoidAlgebra.single c 1))
  rw [Representation.ofMulAction_single,linearEquiv_single,linearEquiv_single,
    Representation.free_single_single]
  congr 1
  funext i
  simp [mul_assoc]

end RelativeStandardFree

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
namespace Representation
open scoped _root_.Representation
open _root_.TensorProduct
variable {k G V W X : Type*} [CommRing k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]
  {ρ : Representation k G V} {σ : Representation k G W}

def coinvariantsLTensorEquiv (τ : Representation k G X) (e : ρ.Equiv σ) :
    (τ.tprod ρ).Coinvariants ≃ₗ[k] (τ.tprod σ).Coinvariants :=
  LinearEquiv.ofLinearMap
    (_root_.Representation.Coinvariants.map _ _ (e.toIntertwiningMap.lTensor τ))
    (_root_.Representation.Coinvariants.map _ _ (e.symm.toIntertwiningMap.lTensor τ))
    (by
      apply _root_.Representation.Coinvariants.hom_ext
      apply _root_.TensorProduct.ext
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro b
      change _root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] e (e.symm b)) = _root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] b)
      rw [_root_.Representation.Equiv.apply_symm_apply])
    (by
      apply _root_.Representation.Coinvariants.hom_ext
      apply _root_.TensorProduct.ext
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro b
      change _root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] e.symm (e b)) = _root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] b)
      rw [_root_.Representation.Equiv.symm_apply_apply])

@[simp] lemma coinvariantsLTensorEquiv_mk_tmul (τ : Representation k G X)
    (e : ρ.Equiv σ) (a : X) (b : V) :
    coinvariantsLTensorEquiv τ e (_root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] b)) =
      _root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] e b) := rfl

end Representation

namespace RelativeStandardFree
open MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (k G : Type) [CommRing k] [Group G] (A : Rep k G)

def repEquiv (n : ℕ) : (Rep.diagonal k G (n+1)).ρ.Equiv (Rep.free k G (Fin n → G)).ρ :=
  Representation.Equiv.mk (linearEquiv k G n) (linearEquiv_intertwines k G n)

@[simp] lemma repEquiv_apply (n : ℕ) (z : MonoidAlgebra k (Fin (n+1) → G)) :
    repEquiv k G n z = linearEquiv k G n z := rfl

def freeCoinvariantEquiv (n : ℕ) :
    (A.ρ.tprod (Representation.free k G (Fin n → G))).Coinvariants ≃ₗ[k]
      ((Fin n → G) →₀ A) := by
  classical
  exact Rep.coinvariantsTensorFreeLEquiv A (Fin n → G)

def coinvariantEquiv (n : ℕ) :
    (A ⊗ Rep.diagonal k G (n+1)).ρ.Coinvariants ≃ₗ[k] ((Fin n → G) →₀ A) :=
  (Representation.coinvariantsLTensorEquiv A.ρ (repEquiv k G n)).trans
    (freeCoinvariantEquiv k G A n)

@[simp] lemma coinvariantEquiv_mk_tmul_single (n : ℕ) (a : A)
    (c : Fin (n+1) → G) (r : k) :
    coinvariantEquiv k G A n (Coinvariants.mk _ (a ⊗ₜ[k] MonoidAlgebra.single c r)) =
      Finsupp.single (fun i => (c 0)⁻¹*c i.succ) (r • A.ρ (c 0)⁻¹ a) := by
  classical
  change Rep.coinvariantsTensorFreeToFinsupp A (Fin n → G)
    (Representation.coinvariantsLTensorEquiv A.ρ (repEquiv k G n)
      (Coinvariants.mk _ (a ⊗ₜ[k] MonoidAlgebra.single c r))) = _
  rw [coinvariantsLTensorEquiv_mk_tmul,repEquiv_apply,linearEquiv_single]
  exact Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single A a _ _ r

end RelativeStandardFree

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCoefficientAffineShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
namespace ProductCoefficient
variable (G I C : Type*) [Group G]

def affineShift (f : G →* G) (σ : C → C) (δ : C → G) :
    (C × G →₀ ℤ) →ₗ[ℤ] (C × G →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (σ p.1,δ p.1*f p.2))

@[simp] lemma affineShift_single (f : G →* G) (σ : C → C) (δ : C → G)
    (c : C) (g : G) (r : ℤ) :
    affineShift G C f σ δ (Finsupp.single (c,g) r) = Finsupp.single (σ c,δ c*f g) r := by
  simp [affineShift]

end ProductCoefficient

open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CosetCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits

namespace RegularProduct
section
open _root_.CategoryTheory
variable (G I : Type) [Group G]

abbrev Module := I → (G →₀ ℤ)

def rightShift (g : G) : (G →₀ ℤ) →ₗ[ℤ] (G →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun x => x*g⁻¹)

@[simp] lemma rightShift_single (g x : G) (r : ℤ) :
    rightShift G g (Finsupp.single x r) = Finsupp.single (x*g⁻¹) r := by
  simp [rightShift]

lemma rightShift_one : rightShift G 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x r
  simp

lemma rightShift_mul (g h : G) :
    rightShift G (g*h) = (rightShift G g).comp (rightShift G h) := by
  apply Finsupp.lhom_ext
  intro x r
  simp [mul_assoc]

def representation : Representation ℤ G (Module G I) where
  toFun g := LinearMap.pi (fun i => (rightShift G g).comp (LinearMap.proj i))
  map_one' := by
    apply LinearMap.ext
    intro a
    funext i
    exact LinearMap.congr_fun (rightShift_one G) (a i)
  map_mul' g h := by
    apply LinearMap.ext
    intro a
    funext i
    exact LinearMap.congr_fun (rightShift_mul G g h) (a i)

abbrev rep : Rep ℤ G := Rep.of (representation G I)

end

open _root_.CategoryTheory

end RegularProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StandardHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct

open _root_.CategoryTheory

namespace LocalNilpotence

variable {A : Type*} [AddCommGroup A]

def IsLocallyNilpotent (f : A →+ A) : Prop := ∀ x, ∃ n : ℕ, (f : A → A)^[n] x = 0

def partialSum (f : A →+ A) : ℕ → A → A
  | 0, _ => 0
  | n+1, x => partialSum f n x + (f : A → A)^[n] x

end LocalNilpotence

open _root_.CategoryTheory

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Pointwise

namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

omit [Fintype n] in
lemma single_sub (i j : n) (a b : R) :
    Matrix.single i j (a-b)=Matrix.single i j a-Matrix.single i j b := by
  rw [sub_eq_add_neg,Matrix.single_add,← Matrix.single_neg,sub_eq_add_neg]

def diagonal : (n → Rˣ) →* (Matrix n n R)ˣ where
  toFun d := {
    val := Matrix.diagonal (fun i => (d i).val)
    inv := Matrix.diagonal (fun i => (d i).inv)
    val_inv := by rw [Matrix.diagonal_mul_diagonal']; simp
    inv_val := by rw [Matrix.diagonal_mul_diagonal']; simp }
  map_one' := Units.ext (by simp)
  map_mul' d e := Units.ext (by simp)

@[simp] lemma diagonal_val (d : n → Rˣ) :
    (diagonal d).val=Matrix.diagonal (fun i => (d i).val) := rfl

def position (i : n) : Rˣ →* (Matrix n n R)ˣ where
  toFun u := diagonal (fun k => if k=i then u else 1)
  map_one' := by simp only [ite_self]; exact map_one diagonal
  map_mul' u v := by
    rw [← map_mul]; congr 1; funext k; by_cases h : k=i <;> simp [h]

lemma position_val (i : n) (u : Rˣ) :
    (position i u).val=1+Matrix.single i i (u.val-1) := by
  change Matrix.diagonal (fun k => ((if k=i then u else 1) : Rˣ).val)=_
  ext k l
  by_cases hki : k=i
  · subst k
    by_cases hli : l=i
    · subst l; simp [Matrix.single]
    · simp [Matrix.single,Ne.symm hli]
  · by_cases hkl : k=l
    · subst l; simp [Matrix.single,hki,Ne.symm hki]
    · simp [Matrix.single,Ne.symm hki,hkl]

lemma diagonal_single (d : n → R) (i j : n) (a : R) :
    Matrix.diagonal d*Matrix.single i j a=Matrix.single i j (d i*a) := by
  ext k l
  by_cases hki : i=k <;> by_cases hjl : j=l <;>
    simp [Matrix.diagonal_mul,Matrix.single,hki,hjl]

lemma single_diagonal (d : n → R) (i j : n) (a : R) :
    Matrix.single i j a*Matrix.diagonal d=Matrix.single i j (a*d j) := by
  ext k l
  by_cases hki : i=k <;> by_cases hjl : j=l <;>
    simp [Matrix.mul_diagonal,Matrix.single,hki,hjl]

end NoncommElementary

open scoped commutatorElement

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_InducedFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation

namespace OrbitModule
open scoped MonoidalCategory
variable {k G : Type} [CommRing k] [Group G]
structure Presentation (C : Rep k G) where
  α : Type
  β : Type
  [finiteα : Finite α]
  [finiteβ : Finite β]
  d : Rep.free k G β ⟶ Rep.free k G α
  ε : Rep.free k G α ⟶ C
  w : d ≫ ε = 0
  exact : (ShortComplex.mk d ε w).Exact
  [epi : Epi ε]
attribute [instance] Presentation.finiteα Presentation.finiteβ Presentation.epi

def Presentation.ofIso {C D : Rep k G} (P : Presentation C) (e : C ≅ D) : Presentation D where
  α := P.α
  β := P.β
  d := P.d
  ε := P.ε ≫ e.hom
  w := by rw [← Category.assoc,P.w,zero_comp]
  exact := by
    let E := ShortComplex.mk P.d P.ε P.w
    let F := ShortComplex.mk P.d (P.ε ≫ e.hom) (by rw [← Category.assoc,P.w,zero_comp])
    let iso : E ≅ F := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by dsimp [E,F]; simp) (by dsimp [E,F]; simp)
    exact (ShortComplex.exact_iff_of_iso iso).mp P.exact

end OrbitModule

open _root_.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace SequentialAction

variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (s : X → X) (heq : ∀ g x, s (g • x) = f g • s x)

def HasImageTupleTransitivity : Prop :=
  ∀ (n : ℕ) (x y : Fin n → X), Function.Injective x → Function.Injective y →
    ∃ g : U, ∀ a, g • s (x a) = s (y a)

end SequentialAction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PrefixPermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace PrefixPermutation
variable {R Y : Type*} [Ring R] [DecidableEq Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (x : ι → Y) (hx : Function.Injective x)

def matrixPart (σ : Equiv.Perm ι) : R := ∑ i, S (x (σ i))*T (x i)

def support : R := ∑ i, S (x i)*T (x i)

omit [DecidableEq Y] [DecidableEq ι] in
@[simp] lemma partial_one : matrixPart S T x 1=support S T x := rfl

def value (σ : Equiv.Perm ι) : R := 1-support S T x+matrixPart S T x σ

omit [DecidableEq Y] [DecidableEq ι] in
@[simp] lemma value_one : value S T x 1=1 := by simp [value]

end PrefixPermutation

namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]
                                                                          
def columnPerm (u : (Matrix n n R)ˣ) : Equiv.Perm (n → R) where
  toFun := Matrix.mulVec u.val
  invFun := Matrix.mulVec u.inv
  left_inv x := by rw [Matrix.mulVec_mulVec, u.inv_val, Matrix.one_mulVec]
  right_inv x := by rw [Matrix.mulVec_mulVec, u.val_inv, Matrix.one_mulVec]

def columnAction : (Matrix n n R)ˣ →* Equiv.Perm (n → R) where
  toFun := columnPerm
  map_one' := by ext x i; simp [columnPerm]
  map_mul' u v := by
    ext x i
    change (u.val * v.val).mulVec x i = u.val.mulVec (v.val.mulVec x) i
    rw [Matrix.mulVec_mulVec]

lemma position_mulVec (i : n) (v : Rˣ) (a : R) :
    Matrix.mulVec (position i v).val (Pi.single i a)=Pi.single i (v.val*a) := by
  ext k
  by_cases hk : k=i
  · subst k; simp [position_val,Matrix.single]
  · simp [position_val,Matrix.single,hk,Ne.symm hk]

end NoncommElementary

namespace PrefixPermutation
variable {R Y ι : Type*} [Ring R] [DecidableEq Y] [Fintype ι] [DecidableEq ι]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)
variable (x : ι → Y) (hx : Function.Injective x)

def complement (ψ : R →ₙ+* R) : R := 1-ψ (support S T x)

end PrefixPermutation

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergSixThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace NoncommElementary
section
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma positions_commute (i j : n) (h : i≠j) (u v : Rˣ) :
    Commute (position i u) (position j v) := by
  apply Commute.map _ diagonal
  change (fun k => if k=i then u else 1)*(fun k => if k=j then v else 1)=
    (fun k => if k=j then v else 1)*(fun k => if k=i then u else 1)
  funext k
  by_cases hki : k=i
  · subst k; simp [h]
  · by_cases hkj : k=j
    · subst k; simp [Ne.symm h]
    · simp [hki,hkj]

end

end NoncommElementary

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
namespace ProductBrown
attribute [-instance] AddCommGroup.toIntModule
end ProductBrown

open Classical
open _root_.CategoryTheory CategoryTheory.Limits
namespace OrbitCoefficients
variable {k G V W : Type} [CommRing k] [Group G] [MulAction G V] [MulAction G W]
variable (A : Rep k G)

variable (V) in
abbrev Orbits := MulAction.orbitRel.Quotient G V
variable (j : Orbits (G := G) V)

lemma orbitCoset_equivariant (g : G) (q : G ⧸ MulAction.stabilizer G j.out) :
    ((MulAction.orbitEquivQuotientStabilizer G j.out).symm (g • q)).val =
      g • ((MulAction.orbitEquivQuotientStabilizer G j.out).symm q).val :=
  MulAction.ofQuotientStabilizer_smul G j.out g q

end OrbitCoefficients

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SurjectiveTrivialInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
namespace SurjectiveTrivialInduction
open _root_.CategoryTheory _root_.Representation _root_.OAI.Representation
attribute [-instance] AddCommGroup.toIntModule
end SurjectiveTrivialInduction

open _root_.CategoryTheory CategoryTheory.Limits
namespace ProductGroupHomology
section
attribute [-instance] AddCommGroup.toIntModule
variable {G H α : Type} [Group G] [Group H]
instance action : MulAction (G × H) (α × G) where
  smul g x := (x.1,g.1*x.2)
  one_smul x := by
    change (x.1,(1:G)*x.2) = x
    exact Prod.ext rfl (one_mul _)
  mul_smul g h x := by
    change (x.1,(g.1*h.1)*x.2) = (x.1,g.1*(h.1*x.2))
    rw [mul_assoc]

def stabilizerEquiv (v : α × G) : MulAction.stabilizer (G × H) v ≃* H where
  toFun g := g.val.2
  invFun h := ⟨(1,h),by change (v.1,1*v.2) = v; simp⟩
  left_inv g := by
    apply Subtype.ext
    have hg := congrArg Prod.snd (MulAction.mem_stabilizer_iff.mp g.property)
    change g.val.1*v.2 = v.2 at hg
    exact Prod.ext (mul_right_cancel (hg.trans (one_mul v.2).symm)).symm rfl
  right_inv h := rfl
  map_mul' _ _ := rfl

open scoped MonoidalCategory
end

open _root_.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
variable {G H : Type} [Group G] [Group H]
variable (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
abbrev R : Rep ℤ G ⥤ Rep ℤ (G × H) := Rep.resFunctor (MonoidHom.fst G H)
def C : ℕ → Rep ℤ (G × H)
  | 0 => Rep.trivial ℤ (G × H) ℤ
  | n+1 => (R (G := G) (H := H)).obj (P.complex.X n)
def d : (n : ℕ) → C (H := H) P (n+1) ⟶ C (H := H) P n
  | 0 => (R (H := H)).map (P.π.f 0)
  | n+1 => (R (H := H)).map (P.complex.d (n+1) n)
lemma w (n : ℕ) : d (H := H) P (n+1) ≫ d P n = 0 := by
  cases n with
  | zero =>
    change (R (G := G) (H := H)).map (P.complex.d 1 0) ≫ (R (G := G) (H := H)).map (P.π.f 0) = 0
    rw [← Functor.map_comp,P.complex_d_comp_π_f_zero,Functor.map_zero]
  | succ n =>
    change (R (H := H)).map _ ≫ (R (H := H)).map _ = 0
    rw [← Functor.map_comp,P.complex.d_comp_d,Functor.map_zero]
instance instEpiRepIntProdDOfNatNat : Epi (d (H := H) P 0) :=
  (Rep.epi_iff_surjective _).mpr ((Rep.epi_iff_surjective (P.π.f 0)).mp inferInstance)
end ProductGroupHomology

attribute [instance] AddCommGroup.toIntModule

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderBasedComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderBasedComplex

structure Data (B : Type*) where
  degree : B → ℕ
  d : (B →₀ ℤ) →ₗ[ℤ] (B →₀ ℤ)
  aug : (B →₀ ℤ) →ₗ[ℤ] ℤ
  d_squared : ∀ c, d (d c) = 0
  lowers : ∀ b t, t ∈ (d (Finsupp.single b 1)).support → degree t + 1 = degree b
  aug_single : ∀ b, aug (Finsupp.single b 1) = if degree b = 0 then 1 else 0
  aug_d : ∀ c, aug (d c) = 0

variable {B : Type*} (C : Data B)

structure Contraction {M : Type*} [AddCommGroup M]
    (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ) where
  point : M
  cone : M →ₗ[ℤ] M
  d_point : d point = 0
  aug_point : aug point = 1
  aug_cone : ∀ c, aug (cone c) = 0
  identity : ∀ c, d (cone c) + cone (d c) = c - aug c • point

variable {M : Type*} [AddCommGroup M]
  (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ) (T : B → Contraction d aug)

def extendBasis (b : B) : M :=
  if C.degree b = 0 then (T b).point else
    (T b).cone (∑ t ∈ (C.d (Finsupp.single b 1)).support.attach,
      C.d (Finsupp.single b 1) t.1 • extendBasis t.1)
termination_by C.degree b
decreasing_by
  have h := C.lowers b t.1 t.2
  omega

def extend : (B →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (extendBasis C d aug T)

@[simp] lemma extend_single (b : B) :
    extend C d aug T (Finsupp.single b 1) = extendBasis C d aug T b := by
  simp only [extend, Finsupp.linearCombination_single, one_smul]

variable (F G : (B →₀ ℤ) →ₗ[ℤ] M)

def homotopyBasis (b : B) : M :=
  (T b).cone (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
    ∑ t ∈ (C.d (Finsupp.single b 1)).support.attach,
      C.d (Finsupp.single b 1) t.1 • homotopyBasis t.1)
termination_by C.degree b
decreasing_by
  have h := C.lowers b t.1 t.2
  omega

def homotopy : (B →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (homotopyBasis C d aug T F G)

end OrderBasedComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactInOfTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace OrderBasedComplex
section
variable {B M : Type*} [AddCommGroup M] (C : Data B)
  (point : B → M) (fill : B → ℕ → M → M)

noncomputable def chosenBasis (b : B) : M :=
  if C.degree b = 0 then point b else
    fill b (C.degree b - 1) (∑ t ∈ (C.d (Finsupp.single b 1)).support.attach,
      C.d (Finsupp.single b 1) t.1 • chosenBasis t.1)
termination_by C.degree b
decreasing_by
  have h := C.lowers b t.1 t.2
  omega

noncomputable def chosenExtend : (B →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (chosenBasis C point fill)

end

variable {B M : Type*} [AddCommGroup M] (C : Data B)
  (fill : B → ℕ → M → M) (F G : (B →₀ ℤ) →ₗ[ℤ] M)

noncomputable def chosenHomotopyBasis (b : B) : M :=
  fill b (C.degree b) (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
    ∑ t ∈ (C.d (Finsupp.single b 1)).support.attach,
      C.d (Finsupp.single b 1) t.1 • chosenHomotopyBasis t.1)
termination_by C.degree b
decreasing_by
  have h := C.lowers b t.1 t.2
  omega
noncomputable def chosenHomotopy : (B →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (chosenHomotopyBasis C fill F G)
end OrderBasedComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsOnSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
variable (P : Type*) [Preorder P]

noncomputable def project (U : Set P) (u : U) (x : P) : U := by
  classical
  exact if h : x ∈ U then ⟨x,h⟩ else u
end

end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PosetTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace PosetTransport
section
universe u v w
variable {P : Type u} [Preorder P] {Q : Type v} [Preorder Q]
variable {H : Type w} [Group H]

section Rank
variable {R : Type*} [PartialOrder R]
def rankAbove (r : R → ℕ) (m : ℕ) : Set R := {x | m ≤ r x}
def rankEmbed (r : R → ℕ) (m : ℕ) : rankAbove r m →o R where
  toFun := Subtype.val
  monotone' := fun _ _ h => h

def rankStep (r : R → ℕ) (m : ℕ) : rankAbove r (m+1) →o rankAbove r m where
  toFun x := ⟨x.val,Nat.le_trans (Nat.le_succ m) x.property⟩
  monotone' := fun _ _ h => h

def rankFiberIso (r : R → ℕ) (hr : StrictMono r) (m : ℕ)
    (p : rankAbove r m) (hp : r p.val = m) :
    {q : rankAbove r (m+1) // p ≤ rankStep r m q} ≃o Set.Ioi p.val where
  toFun q := ⟨q.val.val,lt_of_le_of_ne q.property (by
    intro he
    have hq := q.val.property
    change m+1 ≤ r q.val.val at hq
    rw [← he,hp] at hq
    omega)⟩
  invFun q := ⟨⟨q.val,by
    have h := hr q.property
    change m+1 ≤ r q.val
    omega⟩,q.property.le⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end Rank

section RankBelow
variable {R : Type*} [PartialOrder R]
def rankBelow (r : R → ℕ) (m : ℕ) : Set R := {x | r x ≤ m}
def belowEmbed (r : R → ℕ) (m : ℕ) : rankBelow r m →o R :=
  ⟨Subtype.val,fun _ _ h => h⟩
def linkBelow (r : R → ℕ) (hr : StrictMono r) (m : ℕ) (a : R) (ha : r a = m+1) :
    Set.Iio a →o rankBelow r m where
  toFun x := ⟨x.val,by have hh := hr x.property; change r x.val ≤ m; omega⟩
  monotone' := fun _ _ h => h

end RankBelow

end

open OrderChains
end PosetTransport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TruncatedAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

structure WordCalculus (M : Type*) [Monoid M] (m : ℕ) where
  grade : M → ℕ
  grade_one : grade 1 = 0
  grade_mul : ∀ a b, grade (a * b) = grade a + grade b
  omega : M
  grade_omega : grade omega = 0
  omega_ne_one : omega ≠ 1
  normal : M → M
  normal_one : normal 1 = 1
  normal_omega : normal omega = omega
  nonincreasing : ∀ w, grade w ≤ m → grade (normal w) ≤ grade w
  idempotent : ∀ w, grade w ≤ m → normal (normal w) = normal w
  context : ∀ {u v}, normal u = normal v → ∀ a b,
    grade (a * u * b) ≤ m → grade (a * v * b) ≤ m →
    normal (a * u * b) = normal (a * v * b)
  absorbs : ∀ a b, normal (a * omega * b) = omega

namespace WordCalculus
variable {M : Type*} [Monoid M] {m : ℕ} (C : WordCalculus M m)
variable (k : Type*) [CommSemiring k]

def ball (b : ℕ) : Submodule k (MonoidAlgebra k M) :=
  MonoidAlgebra.supported k k {w | C.grade w ≤ b}

theorem single_mem_ball {w : M} {b : ℕ} (hw : C.grade w ≤ b) (a : k) :
    MonoidAlgebra.single w a ∈ C.ball k b := by
  change ∀ ⦃v⦄, v ∈ (MonoidAlgebra.single w a).coeff.support → C.grade v ≤ b
  intro v hv
  have hvw : v = w := ((Finsupp.mem_support_single v w a).mp hv).1
  simpa only [hvw] using hw

@[simp] theorem one_mem_ball (b : ℕ) : (1 : MonoidAlgebra k M) ∈ C.ball k b := by
  rw [MonoidAlgebra.one_def]
  exact C.single_mem_ball k (by rw [C.grade_one]; exact Nat.zero_le _) 1

def collect : MonoidAlgebra k M →ₗ[k] MonoidAlgebra k M :=
  (Finsupp.linearCombination k (fun w =>
    if C.normal w = C.omega then 0 else MonoidAlgebra.single (C.normal w) (1 : k))).comp
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem collect_single (w : M) (a : k) :
    C.collect k (MonoidAlgebra.single w a) =
      if C.normal w = C.omega then 0 else MonoidAlgebra.single (C.normal w) a := by
  classical
  simp only [collect, LinearMap.comp_apply]
  split <;> rename_i h <;> simp [h, MonoidAlgebra.smul_single]

end WordCalculus

end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TruncatedAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

structure KeyBall (X K : Type*) where
  ball : ℕ → Set X
  mono : Monotone ball
  key : X → K

namespace KeyBall
variable {X K : Type*} (C : KeyBall X K) (m : ℕ)

def Represented (k : K) : Prop := ∃ b, b ≤ m ∧ ∃ x ∈ C.ball b, C.key x = k

def leastCost (k : K) : ℕ :=
  if h : C.Represented m k then Nat.find h else 0

theorem represented_key {x : X} {b : ℕ} (hx : x ∈ C.ball b) (hb : b ≤ m) :
    C.Represented m (C.key x) := ⟨b, hb, x, hx, rfl⟩

variable [Nonempty X]

def representative (k : K) : X :=
  if h : ∃ x ∈ C.ball (C.leastCost m k), C.key x = k then Classical.choose h
  else Classical.choice ‹Nonempty X›

def canonical (x : X) : X := C.representative m (C.key x)

end KeyBall

structure ActionCalculus (V X K L : Type*) [Group V] [MulAction V X] (m : ℕ) where
  group : KeyBall V K
  point : KeyBall X L
  one_mem : ∀ b, (1 : V) ∈ group.ball b
  inv_mem : ∀ {b v}, v ∈ group.ball b → v⁻¹ ∈ group.ball b
  mul_mem : ∀ {b c u v}, u ∈ group.ball b → v ∈ group.ball c → u*v ∈ group.ball (b+c)
  smul_mem : ∀ {b c v x}, v ∈ group.ball b → x ∈ point.ball c → v • x ∈ point.ball (b+c)
  inv_congr : ∀ {u v}, group.key u = group.key v → group.key u⁻¹ = group.key v⁻¹
  mul_congr : ∀ {b c b' c' u v u' v'},
    u ∈ group.ball b → v ∈ group.ball c →
    u' ∈ group.ball b' → v' ∈ group.ball c' →
    b+c ≤ m → b'+c' ≤ m → group.key u = group.key u' → group.key v = group.key v' →
    group.key (u*v) = group.key (u'*v')
  smul_congr : ∀ {b c b' c' v x v' x'},
    v ∈ group.ball b → x ∈ point.ball c →
    v' ∈ group.ball b' → x' ∈ point.ball c' →
    b+c ≤ m → b'+c' ≤ m → group.key v = group.key v' → point.key x = point.key x' →
    point.key (v • x) = point.key (v' • x')

namespace ActionCalculus
variable {V X K L : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m)

theorem inverse_action_iff {v : V} {y z : X} {b c e : ℕ}
    (hv : v ∈ C.group.ball b) (hy : y ∈ C.point.ball c) (hz : z ∈ C.point.ball e)
    (hyb : b+c ≤ m) (hzb : b+e ≤ m) (hybb : 2*b+c ≤ m) (hzbb : 2*b+e ≤ m) :
    C.point.key y = C.point.key (v • z) ↔ C.point.key (v⁻¹ • y) = C.point.key z := by
  constructor
  · intro he
    simpa only [inv_smul_smul] using C.smul_congr (C.inv_mem hv) hy
      (C.inv_mem hv) (C.smul_mem hv hz) hyb (by omega) rfl he
  · intro he
    simpa only [smul_inv_smul] using C.smul_congr hv
      (C.smul_mem (C.inv_mem hv) hy) hv hz (by omega) hzb rfl he

theorem inverse_action_iff_of_total {v : V} {y z : X} {b c e d : ℕ}
    (hv : v ∈ C.group.ball b) (hy : y ∈ C.point.ball c) (hz : z ∈ C.point.ball e)
    (h : b+c+e ≤ d) (hm : 3*d ≤ m) :
    C.point.key y = C.point.key (v • z) ↔ C.point.key (v⁻¹ • y) = C.point.key z :=
  C.inverse_action_iff hv hy hz (by omega) (by omega) (by omega) (by omega)

end ActionCalculus

end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_BoundedForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding

structure WithBound {A K : Type*} (B : KeyBall A K) where
  val : A
  cost : ℕ
  mem : val ∈ B.ball cost

namespace WithBound
variable {A K : Type*} {B : KeyBall A K}
def key (a : WithBound B) : K := B.key a.val
end WithBound

namespace ActionCalculus
variable {V X K L : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m)

abbrev GLabel := WithBound C.group
abbrev XLabel := WithBound C.point

def identity : C.GLabel := ⟨1,0,C.one_mem 0⟩
def multiply (g h : C.GLabel) : C.GLabel :=
  ⟨g.val*h.val, g.cost+h.cost, C.mul_mem g.mem h.mem⟩
def inverse (g : C.GLabel) : C.GLabel := ⟨g.val⁻¹,g.cost,C.inv_mem g.mem⟩
def act (g : C.GLabel) (x : C.XLabel) : C.XLabel :=
  ⟨g.val • x.val,g.cost+x.cost,C.smul_mem g.mem x.mem⟩

inductive Letter where
  | grp : C.GLabel → Letter
  | pre : C.XLabel → Letter
  | del : C.XLabel → Letter
  | zero : Letter

namespace Letter
def cost : C.Letter → ℕ
  | .grp g => g.cost
  | .pre x | .del x => x.cost
  | .zero => 0

def key : C.Letter → Sum K (Sum L (Option L))
  | .grp g => .inl g.key
  | .pre x => .inr (.inl x.key)
  | .del x => .inr (.inr (some x.key))
  | .zero => .inr (.inr none)
end Letter

abbrev Form := Option (List C.XLabel × C.GLabel × List C.XLabel)

namespace Form
def cost : C.Form → ℕ
  | none => 0
  | some (l,g,r) => (l.map WithBound.cost).sum + g.cost + (r.map WithBound.cost).sum

def key : C.Form → Option (List L × K × List L) :=
  Option.map (fun p => (p.1.map WithBound.key, p.2.1.key, p.2.2.map WithBound.key))
end Form

def wordCost (w : List C.Letter) : ℕ := (w.map (Letter.cost C)).sum

@[simp] theorem wordCost_nil : C.wordCost [] = 0 := rfl
@[simp] theorem wordCost_cons (a : C.Letter) (w : List C.Letter) :
    C.wordCost (a::w) = a.cost C + C.wordCost w := rfl
@[simp] theorem wordCost_append (a b : List C.Letter) :
    C.wordCost (a++b) = C.wordCost a + C.wordCost b := by simp [wordCost]

variable [DecidableEq L]

def step : C.Letter → C.Form → C.Form
  | _, none => none
  | .zero, _ => none
  | .pre x, some (l,g,r) => some (x::l,g,r)
  | .grp h, some ([],g,r) => some ([],C.multiply h g,r)
  | .grp h, some (x::l,g,r) => some (C.act h x::l,g,r)
  | .del y, some ([],g,r) => some ([],C.identity,r++[C.act (C.inverse g) y])
  | .del y, some (x::l,g,r) => if y.key = x.key then some (l,g,r) else none

def run (w : List C.Letter) (f : C.Form) : C.Form :=
  w.foldr (C.step) f

def normalize (w : List C.Letter) : C.Form := C.run w (some ([],C.identity,[]))

@[simp] theorem run_nil (f : C.Form) : C.run [] f = f := rfl
@[simp] theorem run_cons (a : C.Letter) (w : List C.Letter) (f : C.Form) :
    C.run (a::w) f = C.step a (C.run w f) := rfl
@[simp] theorem run_append (a b : List C.Letter) (f : C.Form) :
    C.run (a++b) f = C.run a (C.run b f) := by simp [run]

@[simp] theorem step_none (a : C.Letter) : C.step a none = none := by cases a <;> rfl
@[simp] theorem run_none (w : List C.Letter) : C.run w none = none := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

theorem step_cost (a : C.Letter) (f : C.Form) :
    (C.step a f).cost C ≤ a.cost C + f.cost C := by
  cases f with
  | none => simp [Form.cost]
  | some p =>
    rcases p with ⟨l,g,r⟩
    cases a with
    | zero => simp [step,Form.cost]
    | pre x => simp [step,Form.cost,Letter.cost]; omega
    | grp h =>
      cases l <;> simp [step,Form.cost,Letter.cost,multiply,act] <;> omega
    | del y =>
      cases l with
      | nil => simp [step,Form.cost,Letter.cost,act,inverse,identity]; omega
      | cons x l =>
        by_cases h : y.key = x.key <;> simp [step,h,Form.cost,Letter.cost]; omega

theorem run_cost (w : List C.Letter) (f : C.Form) :
    (C.run w f).cost C ≤ C.wordCost w + f.cost C := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [run_cons]
    exact (C.step_cost a (C.run w f)).trans (by simp only [wordCost_cons]; omega)

theorem normalize_cost (w : List C.Letter) :
    (C.normalize w).cost C ≤ C.wordCost w := by
  simpa [normalize, Form.cost, identity] using C.run_cost w (some ([],C.identity,[]))

theorem step_congr {a a' : C.Letter} {f f' : C.Form}
    (ha : a.key C = a'.key C) (hf : f.key C = f'.key C)
    (hb : a.cost C + f.cost C ≤ m) (hb' : a'.cost C + f'.cost C ≤ m) :
    (C.step a f).key C = (C.step a' f').key C := by
  cases f with
  | none =>
    cases f' with
    | none => simp
    | some p => simp [Form.key] at hf
  | some p =>
    cases f' with
    | none => simp [Form.key] at hf
    | some p' =>
      rcases p with ⟨l,g,r⟩
      rcases p' with ⟨l',g',r'⟩
      simp only [Form.key, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨hl,hg,hr⟩ := hf
      cases a <;> cases a' <;> simp only [Letter.key, Sum.inl.injEq, Sum.inr.injEq,
        Option.some.injEq, reduceCtorEq] at ha
      case pre.pre x x' => simp [step,Form.key,ha,hl,hg,hr]
      case zero.zero => rfl
      case grp.grp h h' =>
        cases l with
        | nil =>
          have he : l' = [] := by simpa using hl.symm
          subst l'
          have he := C.mul_congr h.mem g.mem h'.mem g'.mem
            (by simp only [Letter.cost,Form.cost,List.map_nil,List.sum_nil,zero_add] at hb; omega)
            (by simp only [Letter.cost,Form.cost,List.map_nil,List.sum_nil,zero_add] at hb'; omega) ha hg
          simp [step,Form.key,multiply,WithBound.key, he,hr]
        | cons x l =>
          cases l' with
          | nil => simp at hl
          | cons x' l' =>
            simp only [List.map_cons, List.cons.injEq] at hl
            have he := C.smul_congr h.mem x.mem h'.mem x'.mem
              (by simp only [Letter.cost,Form.cost,List.map_cons,List.sum_cons] at hb; omega)
              (by simp only [Letter.cost,Form.cost,List.map_cons,List.sum_cons] at hb'; omega)
              ha hl.1
            change (C.act h x).key = (C.act h' x').key at he
            simp only [step,Form.key,Option.map_some,List.map_cons,he,hl.2,hg,hr]
      case del.del y y' =>
        cases l with
        | nil =>
          have he : l' = [] := by simpa using hl.symm
          subst l'
          have he := C.smul_congr (C.inv_mem g.mem) y.mem (C.inv_mem g'.mem) y'.mem
            (by simp only [Letter.cost,Form.cost,List.map_nil,List.sum_nil,zero_add] at hb; omega)
            (by simp only [Letter.cost,Form.cost,List.map_nil,List.sum_nil,zero_add] at hb'; omega)
            (C.inv_congr hg) ha
          simp [step,Form.key,act,inverse,WithBound.key,he,hr]
        | cons x l =>
          cases l' with
          | nil => simp at hl
          | cons x' l' =>
            simp only [List.map_cons,List.cons.injEq] at hl
            simp only [step,ha,hl.1]
            split <;> simp [Form.key,hl.2,hg,hr]

theorem run_congr {w w' : List C.Letter} {f f' : C.Form}
    (hw : w.map (Letter.key C) = w'.map (Letter.key C))
    (hf : f.key C = f'.key C)
    (hb : C.wordCost w + f.cost C ≤ m) (hb' : C.wordCost w' + f'.cost C ≤ m) :
    (C.run w f).key C = (C.run w' f').key C := by
  induction w generalizing w' with
  | nil =>
    have he : w' = [] := by simpa using hw.symm
    subst w'
    exact hf
  | cons a w ih =>
    cases w' with
    | nil => simp at hw
    | cons a' w' =>
      simp only [List.map_cons,List.cons.injEq] at hw
      have ht : C.wordCost w + f.cost C ≤ m := by simp only [wordCost_cons] at hb; omega
      have ht' : C.wordCost w' + f'.cost C ≤ m := by simp only [wordCost_cons] at hb'; omega
      rw [run_cons,run_cons]
      exact C.step_congr hw.1 (ih hw.2 ht ht')
        (by have := C.run_cost w f; simp only [wordCost_cons] at hb; omega)
        (by have := C.run_cost w' f'; simp only [wordCost_cons] at hb'; omega)

theorem normalize_left_context {u v a : List C.Letter}
    (he : (C.normalize u).key C = (C.normalize v).key C)
    (hu : C.wordCost (a++u) ≤ m) (hv : C.wordCost (a++v) ≤ m) :
    (C.normalize (a++u)).key C = (C.normalize (a++v)).key C := by
  simp only [normalize,run_append]
  apply C.run_congr rfl he
  · have := C.normalize_cost u
    simp only [wordCost_append] at hu
    omega
  · have := C.normalize_cost v
    simp only [wordCost_append] at hv
    omega

end ActionCalculus
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_BoundedContexts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.ActionCalculus
variable {V X K L : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m) [DecidableEq L]

def display : C.Form → List C.Letter
  | none => [.zero]
  | some (l,g,r) => l.map .pre ++ .grp g :: r.reverse.map .del

omit [DecidableEq L] in
@[simp] theorem wordCost_pres [DecidableEq L] (l : List C.XLabel) :
    C.wordCost (l.map .pre) = (l.map WithBound.cost).sum := by
  simp [wordCost,Function.comp_def,Letter.cost]

omit [DecidableEq L] in
@[simp] theorem wordCost_dels [DecidableEq L] (l : List C.XLabel) :
    C.wordCost (l.map .del) = (l.map WithBound.cost).sum := by
  simp [wordCost,Function.comp_def,Letter.cost]

omit [DecidableEq L] in
@[simp] theorem wordCost_reverse [DecidableEq L] (w : List C.Letter) :
    C.wordCost w.reverse = C.wordCost w := by simp [wordCost]

@[simp] theorem display_cost (f : C.Form) : C.wordCost (C.display f) = f.cost C := by
  cases f with
  | none => rfl
  | some p => rcases p with ⟨l,g,r⟩; simp [display,Form.cost,Letter.cost,Nat.add_assoc]

omit [DecidableEq L] in
theorem display_congr [DecidableEq L] {f f' : C.Form} (hf : f.key C = f'.key C) :
    (C.display f).map (Letter.key C) = (C.display f').map (Letter.key C) := by
  cases f with
  | none =>
    cases f' with
    | none => rfl
    | some p => simp [Form.key] at hf
  | some p =>
    cases f' with
    | none => simp [Form.key] at hf
    | some p' =>
      rcases p with ⟨l,g,r⟩
      rcases p' with ⟨l',g',r'⟩
      simp only [Form.key,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hf
      have hp : (l.map (.pre : C.XLabel → C.Letter)).map (Letter.key C) =
          (l'.map .pre).map (Letter.key C) := by
        simpa only [List.map_map,Function.comp_def,Letter.key] using
          congrArg (List.map (fun x : L => Sum.inr (Sum.inl x) : L → Sum K (Sum L (Option L)))) hf.1
      have hd : (r.reverse.map (.del : C.XLabel → C.Letter)).map (Letter.key C) =
          (r'.reverse.map .del).map (Letter.key C) := by
        have he := congrArg (fun xs : List L => xs.reverse.map
          (fun x => Sum.inr (Sum.inr (some x)) : L → Sum K (Sum L (Option L)))) hf.2.2
        simpa only [List.map_reverse,List.map_map,Function.comp_def,Letter.key] using he
      simp only [display,List.map_append,List.map_cons,Letter.key,hp,hf.2.1,hd]

@[simp] theorem step_zero (f : C.Form) : C.step .zero f = none := by cases f <;> rfl

theorem step_identity (f : C.Form) :
    (C.step (.grp C.identity) f).key C = f.key C := by
  cases f with
  | none => rfl
  | some p =>
    rcases p with ⟨l,g,r⟩
    cases l <;> simp [step,Form.key,identity,multiply,act,WithBound.key]

theorem step_multiply (g h : C.GLabel) (f : C.Form) :
    (C.step (.grp g) (C.step (.grp h) f)).key C =
      (C.step (.grp (C.multiply g h)) f).key C := by
  cases f with
  | none => rfl
  | some p =>
    rcases p with ⟨l,q,r⟩
    cases l <;> simp [step,Form.key,multiply,act,WithBound.key,mul_assoc,mul_smul]

theorem step_group_pre (g : C.GLabel) (x : C.XLabel) (f : C.Form) :
    C.step (.grp g) (C.step (.pre x) f) = C.step (.pre (C.act g x)) f := by
  cases f with
  | none => rfl
  | some p => rcases p with ⟨l,q,r⟩; rfl

theorem step_delete_pre (y x : C.XLabel) (f : C.Form) :
    C.step (.del y) (C.step (.pre x) f) = if y.key = x.key then f else none := by
  cases f with
  | none => simp
  | some p => rcases p with ⟨l,q,r⟩; rfl

theorem step_delete_group (y : C.XLabel) (g : C.GLabel) (f : C.Form)
    {d : ℕ} (hb : y.cost + g.cost + f.cost C ≤ d) (hm : 3*d ≤ m) :
    (C.step (.del y) (C.step (.grp g) f)).key C =
      (C.step (.del (C.act (C.inverse g) y)) f).key C := by
  cases f with
  | none => rfl
  | some p =>
    rcases p with ⟨l,q,r⟩
    cases l with
    | nil => simp [step,Form.key,multiply,inverse,act,WithBound.key,mul_smul]
    | cons x l =>
      have he : y.key = (C.act g x).key ↔ (C.act (C.inverse g) y).key = x.key :=
        C.inverse_action_iff_of_total g.mem y.mem x.mem
          (by simp only [Form.cost,List.map_cons,List.sum_cons] at hb; omega) hm
      simp only [step,he]

theorem normalize_nil_ne_zero : (C.normalize []).key C ≠ none := by
  simp only [normalize,run_nil,Form.key,Option.map_some,ne_eq,reduceCtorEq,not_false_eq_true]

end SimpleFInftyOvergroups.BoundedEncoding.ActionCalculus

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveFold
attribute [-instance] _root_.OAI.ProductGroupHomology.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace SimpleFInftyOvergroups.EffectiveNames
namespace PartialFold
variable {P A B : Type*} (f : P × A × B → Part B)

def left (p : P) : List A → B → Part B
  | [], b => Part.some b
  | a::w, b => (f (p,a,b)).bind (left p w)

def right (p : P) : List A → B → Part B
  | [], b => Part.some b
  | a::w, b => (right p w b).bind (fun c => f (p,a,c))

theorem left_append (p : P) (u v : List A) (b : B) :
    left f p (u++v) b = (left f p u b).bind (left f p v) := by
  induction u generalizing b with
  | nil => simp [left]
  | cons a u ih =>
    simp only [List.cons_append,left,Part.bind_assoc]
    congr 1
    funext c
    exact ih c

theorem right_eq_left_reverse (p : P) (w : List A) (b : B) :
    right f p w b = left f p w.reverse b := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [right,List.reverse_cons,left_append,← ih,left]
    simp only [Part.bind_some_right]

def loop : P × List A × B → Part (B ⊕ (P × List A × B))
  | (_,[],b) => Part.some (.inl b)
  | (p,a::w,b) => (f (p,a,b)).map (fun c => .inr (p,w,c))

theorem fix_loop (p : P) (w : List A) (b : B) :
    PFun.fix (loop f) (p,w,b) = left f p w b := by
  induction w generalizing b with
  | nil =>
    apply Part.ext
    intro out
    erw [PFun.mem_fix_iff]
    simp only [loop,Part.mem_some_iff,Sum.inl.injEq,Sum.inr_ne_inl,exists_false,
      false_and,or_false,left]
  | cons a w ih =>
    apply Part.ext
    intro out
    erw [PFun.mem_fix_iff]
    simp only [loop,Part.mem_map_iff,Sum.inr_ne_inl,exists_false,and_false,false_or]
    constructor
    · rintro ⟨⟨p',w',c⟩,⟨c',hc,he⟩,ho⟩
      have he' : (p,w,c') = (p',w',c) := Sum.inr.inj he
      obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj he' |>.imp_right Prod.mk.inj
      rw [ih] at ho
      exact Part.mem_bind_iff.mpr ⟨c',hc,ho⟩
    · intro ho
      obtain ⟨c,hc,ho⟩ := Part.mem_bind_iff.mp ho
      exact ⟨(p,w,c),⟨c,hc,rfl⟩,by rw [ih]; exact ho⟩

end PartialFold
end SimpleFInftyOvergroups.EffectiveNames

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_NamedActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.NamedAction

structure Operations (G X : Type*) where
  one : G
  mul : G → G → G
  inv : G → G
  act : G → X → X
  gcost : G → ℕ
  xcost : X → ℕ
  cost_one : gcost one = 0
  cost_mul : ∀ g h, gcost (mul g h) = gcost g + gcost h
  cost_inv : ∀ g, gcost (inv g) = gcost g
  cost_act : ∀ g x, xcost (act g x) = gcost g + xcost x

abbrev Letter (G X : Type*) := G ⊕ (X ⊕ Option X)
abbrev Form (G X : Type*) := Option (List X × G × List X)
abbrev Result (K L : Type*) := Option (List L × K × List L)

namespace Operations
variable {G X K L : Type*} (N : Operations G X)

def letterCost : Letter G X → ℕ
  | .inl g => N.gcost g
  | .inr (.inl x) | .inr (.inr (some x)) => N.xcost x
  | .inr (.inr none) => 0

def wordCost (w : List (Letter G X)) : ℕ := (w.map N.letterCost).sum

def formCost : Form G X → ℕ
  | none => 0
  | some (l,g,r) => (l.map N.xcost).sum + N.gcost g + (r.map N.xcost).sum

def formKey (kg : G → K) (kx : X → L) : Form G X → Result K L :=
  Option.map (fun p => (p.1.map kx,kg p.2.1,p.2.2.map kx))

def plan : Letter G X → Form G X → Form G X ⊕ (X × X × Form G X)
  | _, none => .inl none
  | .inr (.inr none), _ => .inl none
  | .inr (.inl x), some (l,g,r) => .inl (some (x::l,g,r))
  | .inl h, some ([],g,r) => .inl (some ([],N.mul h g,r))
  | .inl h, some (x::l,g,r) => .inl (some (N.act h x::l,g,r))
  | .inr (.inr (some y)), some ([],g,r) =>
      .inl (some ([],N.one,r++[N.act (N.inv g) y]))
  | .inr (.inr (some y)), some (x::l,g,r) => .inr (y,x,some (l,g,r))

variable [DecidableEq L]

def totalStep (kx : X → L) (a : Letter G X) (f : Form G X) : Form G X :=
  (N.plan a f).elim id (fun p => if kx p.1 = kx p.2.1 then p.2.2 else none)

def totalRun (kx : X → L) (w : List (Letter G X)) (f : Form G X) : Form G X :=
  w.foldr (N.totalStep kx) f

def totalNormalize (kx : X → L) (w : List (Letter G X)) : Form G X :=
  N.totalRun kx w (some ([],N.one,[]))

def totalTest (kg : G → K) (kx : X → L) (w : List (Letter G X)) : Result K L :=
  formKey kg kx (N.totalNormalize kx w)

@[simp] theorem totalRun_nil (kx : X → L) (f : Form G X) : N.totalRun kx [] f = f := rfl
@[simp] theorem totalRun_cons (kx : X → L) (a : Letter G X) (w : List (Letter G X))
    (f : Form G X) : N.totalRun kx (a::w) f = N.totalStep kx a (N.totalRun kx w f) := rfl
@[simp] theorem wordCost_nil : N.wordCost [] = 0 := rfl
@[simp] theorem wordCost_cons (a : Letter G X) (w : List (Letter G X)) :
    N.wordCost (a::w) = N.letterCost a + N.wordCost w := rfl
@[simp] theorem wordCost_append (u v : List (Letter G X)) :
    N.wordCost (u++v) = N.wordCost u + N.wordCost v := by simp [wordCost]
@[simp] theorem totalStep_none (kx : X → L) (a : Letter G X) :
    N.totalStep kx a none = none := rfl

end Operations

structure Interpretation {G X V Y K L : Type*} [Group V] [MulAction V Y]
    {m : ℕ} (N : Operations G X) (C : ActionCalculus V Y K L m) where
  group : G → C.GLabel
  point : X → C.XLabel
  group_cost : ∀ g, (group g).cost = N.gcost g
  point_cost : ∀ x, (point x).cost = N.xcost x
  one : group N.one = C.identity
  mul : ∀ g h, group (N.mul g h) = C.multiply (group g) (group h)
  inv : ∀ g, group (N.inv g) = C.inverse (group g)
  act : ∀ g x, point (N.act g x) = C.act (group g) (point x)

namespace Interpretation
variable {G X V Y K L : Type*} [Group V] [MulAction V Y] {m : ℕ}
  {N : Operations G X} {C : ActionCalculus V Y K L m} (I : Interpretation N C)

def gkey (g : G) : K := (I.group g).key
def xkey (x : X) : L := (I.point x).key

def letter : Letter G X → C.Letter
  | .inl g => .grp (I.group g)
  | .inr (.inl x) => .pre (I.point x)
  | .inr (.inr (some x)) => .del (I.point x)
  | .inr (.inr none) => .zero

def form : Form G X → C.Form :=
  Option.map (fun p => (p.1.map I.point,I.group p.2.1,p.2.2.map I.point))

@[simp] theorem letter_cost (a : Letter G X) : (I.letter a).cost C = N.letterCost a := by
  rcases a with g | (x | y)
  · exact I.group_cost g
  · exact I.point_cost x
  · cases y with
    | none => rfl
    | some x => exact I.point_cost x

@[simp] theorem form_cost (f : Form G X) : (I.form f).cost C = N.formCost f := by
  cases f with
  | none => rfl
  | some p => simp [form,ActionCalculus.Form.cost,Operations.formCost,List.map_map,
      Function.comp_def,I.point_cost,I.group_cost]

@[simp] theorem word_cost (w : List (Letter G X)) : C.wordCost (w.map I.letter) = N.wordCost w := by
  simp [ActionCalculus.wordCost,Operations.wordCost,List.map_map,Function.comp_def]

@[simp] theorem form_key (f : Form G X) :
    (I.form f).key C = Operations.formKey I.gkey I.xkey f := by
  cases f <;> simp [form,Operations.formKey,ActionCalculus.Form.key,List.map_map,
    Function.comp_def,gkey,xkey]

variable [DecidableEq L]

theorem totalStep (a : Letter G X) (f : Form G X) :
    I.form (N.totalStep I.xkey a f) = C.step (I.letter a) (I.form f) := by
  cases f with
  | none => simp [form]
  | some p =>
    rcases p with ⟨l,g,r⟩
    rcases a with h | (x | y)
    · cases l <;> simp [Operations.totalStep,Operations.plan,letter,form,ActionCalculus.step,I.mul,I.act]
    · simp [Operations.totalStep,Operations.plan,letter,form,ActionCalculus.step]
    · cases y with
      | none => rfl
      | some y =>
        cases l with
        | nil => simp [Operations.totalStep,Operations.plan,letter,form,ActionCalculus.step,I.one,I.inv,I.act]
        | cons x l =>
          by_cases h : I.xkey y = I.xkey x
          · change (I.point y).key = (I.point x).key at h
            simp [Operations.totalStep,Operations.plan,letter,form,ActionCalculus.step,xkey,h]
          · change (I.point y).key ≠ (I.point x).key at h
            simp [Operations.totalStep,Operations.plan,letter,form,ActionCalculus.step,xkey,h]

theorem totalRun (w : List (Letter G X)) (f : Form G X) :
    I.form (N.totalRun I.xkey w f) = C.run (w.map I.letter) (I.form f) := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [Operations.totalRun_cons,I.totalStep,ih,List.map_cons,ActionCalculus.run_cons]

theorem totalNormalize (w : List (Letter G X)) :
    I.form (N.totalNormalize I.xkey w) = C.normalize (w.map I.letter) := by
  unfold Operations.totalNormalize
  rw [I.totalRun]
  simp only [form,Option.map_some,List.map_nil,I.one]
  rfl

theorem totalTest (w : List (Letter G X)) :
    N.totalTest I.gkey I.xkey w = (C.normalize (w.map I.letter)).key C := by
  rw [← I.totalNormalize,I.form_key]
  rfl

@[simp] theorem totalTest_nil : N.totalTest I.gkey I.xkey [] ≠ none := by
  simp only [I.totalTest,List.map_nil]
  exact C.normalize_nil_ne_zero

end Interpretation
end SimpleFInftyOvergroups.BoundedEncoding.NamedAction

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace SimpleFInftyOvergroups.BoundedEncoding.NamedAction
namespace Operations
variable {G X K L : Type*} (N : Operations G X) [DecidableEq L]

def compare (fx : X → Part L) (x y : X) : Part Bool :=
  (fx x).bind fun a => (fx y).map fun b => decide (a=b)

def step (fx : X → Part L) (a : Letter G X) (f : Form G X) : Part (Form G X) :=
  (N.plan a f).elim Part.some (fun p =>
    (compare fx p.1 p.2.1).map (fun b => bif b then p.2.2 else none))

def run (N : Operations G X) (fx : X → Part L) : List (Letter G X) → Form G X → Part (Form G X)
  | [], f => Part.some f
  | a::w, f => (run N fx w f).bind (N.step fx a)

theorem compare_full (fx : X → Part L) (kx : X → L) {x y : X}
    (hx : kx x ∈ fx x) (hy : kx y ∈ fx y) :
    decide (kx x = kx y) ∈ compare fx x y :=
  Part.mem_bind_iff.mpr ⟨_,hx,Part.mem_map _ hy⟩

variable {P : Type*} [Primcodable P] [Primcodable G] [Primcodable X]
  [Primcodable K] [Primcodable L]
variable {fg : P → G → Part K} {fx : P → X → Part L}

theorem partrec_compare (hx : Partrec₂ fx) :
    Partrec (fun p : P × X × X => compare (fx p.1) p.2.1 p.2.2) := by
  have ha : Partrec (fun p : P × X × X => fx p.1 p.2.1) :=
    hx.comp Computable.fst (Computable.fst.comp Computable.snd)
  apply ha.bind
  have hb : Partrec (fun p : (P × X × X) × L => fx p.1.1 p.1.2.2) :=
    hx.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp (Computable.snd.comp Computable.fst))
  exact (hb.map (Primrec.eq.decide.to_comp.comp
    (Computable.snd.comp Computable.fst) Computable.snd).to₂).to₂

theorem partrec_step (hn : Computable₂ N.plan) (hx : Partrec₂ fx) :
    Partrec (fun p : P × Letter G X × Form G X => N.step (fx p.1) p.2.1 p.2.2) := by
  let S := P × Letter G X × Form G X
  have hp : Computable (fun p : S => N.plan p.2.1 p.2.2) :=
    hn.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)
  have hb : Partrec₂ (fun (s : S) (p : X × X × Form G X) =>
      (compare (fx s.1) p.1 p.2.1).map (fun b => bif b then p.2.2 else none)) := by
    have hc : Partrec (fun p : S × (X × X × Form G X) =>
        compare (fx p.1.1) p.2.1 p.2.2.1) :=
      (partrec_compare hx).comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp Computable.snd).pair
          (Computable.fst.comp (Computable.snd.comp Computable.snd))))
    exact (hc.map (Computable.cond Computable.snd
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
      (Computable.const none)).to₂).to₂
  exact (Partrec.sumCasesOn_right hp Computable.snd.to₂ hb).of_eq
    (by intro p; unfold step; cases N.plan p.2.1 p.2.2 <;> rfl)

omit [Primcodable P] [Primcodable G] [Primcodable X] [Primcodable L] in
theorem run_eq_fold (p : P) (w : List (Letter G X)) (f : Form G X) :
    N.run (fx p) w f = EffectiveNames.PartialFold.right
      (fun s : P × Letter G X × Form G X => N.step (fx s.1) s.2.1 s.2.2) p w f := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [run,EffectiveNames.PartialFold.right,ih]

end Operations
end SimpleFInftyOvergroups.BoundedEncoding.NamedAction

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EnlargementCore
attribute [-instance] _root_.OAI.ProductGroupHomology.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SourceEnlargement

variable {D V Z : Type*} [Ring D] [Group V] [MulAction V Z]

def value (E : D) (g : V) : MonoidAlgebra D V :=
  MonoidAlgebra.single 1 (1 - E) + MonoidAlgebra.single g E

@[simp] lemma value_one (E : D) : value E (1 : V) = 1 := by
  simp only [value, ← MonoidAlgebra.single_add, sub_add_cancel]
  rfl

lemma value_mul (E : D) (hE : E * E = E) (g h : V) :
    value E g * value E h = value E (g * h) := by
  have ha : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have hb : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have hc : (1 - E) * (1 - E) = 1 - E := by
    rw [mul_sub, mul_one, ha, sub_zero]
  simp only [value, add_mul, mul_add, MonoidAlgebra.single_mul_single,
    one_mul, mul_one, ha, hb, hc, hE, MonoidAlgebra.single_zero, add_zero, zero_add]

def unitMap (E : D) (hE : E * E = E) : V →* (MonoidAlgebra D V)ˣ where
  toFun g :=
    { val := value E g
      inv := value E g⁻¹
      val_inv := by rw [value_mul E hE, mul_inv_cancel, value_one]
      inv_val := by rw [value_mul E hE, inv_mul_cancel, value_one] }
  map_one' := Units.ext (value_one E)
  map_mul' g h := Units.ext (value_mul E hE g h).symm

@[simp] lemma unitMap_val (E : D) (hE : E * E = E) (g : V) :
    (unitMap E hE g).val = value E g := rfl

def indexAction : V →* AddMonoid.End (Z →₀ D) where
  toFun g := Finsupp.mapDomain.addMonoidHom (fun z => g • z)
  map_one' := by
    apply AddMonoidHom.ext
    intro a
    change Finsupp.mapDomain (fun z : Z => (1 : V) • z) a = a
    simp only [one_smul]
    exact Finsupp.mapDomain_id
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro a
    change Finsupp.mapDomain (fun z : Z => (g * h) • z) a =
      Finsupp.mapDomain (fun z => g • z) (Finsupp.mapDomain (fun z => h • z) a)
    rw [← Finsupp.mapDomain_comp]
    simp only [mul_smul, Function.comp_def]

@[simp] lemma indexAction_single (g : V) (z : Z) (d : D) :
    indexAction g (Finsupp.single z d) = Finsupp.single (g • z) d :=
  Finsupp.mapDomain_single

lemma scalar_index_commute (d : D) (g : V) :
    Commute (Module.toAddMonoidEnd D (Z →₀ D) d) (indexAction g) := by
  apply Finsupp.addHom_ext
  intro z a
  change d • indexAction g (Finsupp.single z a) = indexAction g (d • Finsupp.single z a)
  simp only [indexAction_single, Finsupp.smul_single]

def ringAction : MonoidAlgebra D V →+* AddMonoid.End (Z →₀ D) :=
  MonoidAlgebra.liftNCRingHom (Module.toAddMonoidEnd D (Z →₀ D))
    indexAction scalar_index_commute

@[simp] lemma ringAction_single (g : V) (d : D) (z : Z) (a : D) :
    ringAction (MonoidAlgebra.single g d) (Finsupp.single z a) =
      Finsupp.single (g • z) (d * a) := by
  rw [ringAction, MonoidAlgebra.liftNCRingHom_single]
  change d • indexAction g (Finsupp.single z a) = _
  simp only [indexAction_single, Finsupp.smul_single, smul_eq_mul]

instance unitsAction : MulAction (MonoidAlgebra D V)ˣ (Z →₀ D) where
  smul w a := ringAction w.val a
  one_smul a := by change ringAction 1 a = a; rw [map_one]; rfl
  mul_smul w v a := by
    change ringAction (w.val * v.val) a = ringAction w.val (ringAction v.val a)
    rw [map_mul]; rfl

def group (P : Set D) (hP : ∀ E ∈ P, E * E = E) : Subgroup (MonoidAlgebra D V)ˣ :=
  Subgroup.closure {w | ∃ E : P, ∃ g : V, w = unitMap E.val (hP E.val E.property) g}

variable (P : Set D) (hP : ∀ E ∈ P, E * E = E)

def map (E : P) : V →* group (V := V) P hP :=
  (unitMap E.val (hP E.val E.property)).codRestrict _ fun g =>
    Subgroup.subset_closure ⟨E, g, rfl⟩

@[simp] lemma map_val (E : P) (g : V) :
    (map P hP E g).val = unitMap E.val (hP E.val E.property) g := rfl

end SourceEnlargement
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PlanEffective
attribute [-instance] _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.NamedAction.Operations
variable {G X : Type*} [Primcodable G] [Primcodable X] (N : Operations G X)
attribute [local fun_prop] Primrec
attribute [local fun_prop] Primrec.id Primrec.const Primrec.fst Primrec.snd Primrec.pair Primrec.comp
attribute [local fun_prop] Primrec.option_some Primrec.sumInl Primrec.sumInr
theorem primrec_cons {A : Type*} [Primcodable A] :
    Primrec (fun p : A × List A => p.1 :: p.2) := Primrec.list_cons
theorem primrec_append {A : Type*} [Primcodable A] :
    Primrec (fun p : List A × List A => p.1 ++ p.2) := Primrec.list_append
attribute [local fun_prop] primrec_cons primrec_append

theorem primrec_match_list {A B R : Type*} [Primcodable A] [Primcodable B] [Primcodable R]
    {f : A → List B} {g : A → R} {h : A → B × List B → R}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec (fun a => match f a with | [] => g a | b::l => h a (b,l)) :=
  (Primrec.list_casesOn hf hg hh).of_eq (fun a => by cases f a <;> rfl)
theorem primrec_match_option {A B R : Type*} [Primcodable A] [Primcodable B] [Primcodable R]
    {f : A → Option B} {g : A → R} {h : A → B → R}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec (fun a => match f a with | none => g a | some b => h a b) :=
  (Primrec.option_casesOn hf hg hh).of_eq (fun a => by cases f a <;> rfl)
theorem primrec_match_sum {A B C R : Type*}
    [Primcodable A] [Primcodable B] [Primcodable C] [Primcodable R]
    {f : A → B ⊕ C} {g : A → B → R} {h : A → C → R}
    (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec (fun a => match f a with | .inl b => g a b | .inr c => h a c) :=
  (Primrec.sumCasesOn hf hg hh).of_eq (fun a => by cases f a <;> rfl)

end SimpleFInftyOvergroups.BoundedEncoding.NamedAction.Operations

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_Rekey
attribute [-instance] _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
namespace KeyBall
variable {X K K' : Type*} (C : KeyBall X K)

def mapKey (f : K → K') : KeyBall X K' where
  ball := C.ball
  mono := C.mono
  key := f ∘ C.key

end KeyBall
namespace ActionCalculus
variable {V X K L K' L' : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m)

def rekey (g : K → K') (x : L → L') (hg : Function.Injective g)
    (hx : Function.Injective x) : ActionCalculus V X K' L' m where
  group := C.group.mapKey g
  point := C.point.mapKey x
  one_mem := C.one_mem
  inv_mem := C.inv_mem
  mul_mem := C.mul_mem
  smul_mem := C.smul_mem
  inv_congr := fun h => congrArg g (C.inv_congr (hg h))
  mul_congr := fun hu hv hu' hv' hb hb' he hf =>
    congrArg g (C.mul_congr hu hv hu' hv' hb hb' (hg he) (hg hf))
  smul_congr := fun hu hv hu' hv' hb hb' he hf =>
    congrArg x (C.smul_congr hu hv hu' hv' hb hb' (hg he) (hx hf))

end ActionCalculus
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TruncatedArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

namespace KeyBall
variable {X K : Type*} (C : KeyBall X K) (D : Type*) [AddCommMonoid D]

def arrayBall (b : ℕ) (p : X →₀ D) : Prop := ∀ x ∈ p.support, x ∈ C.ball b

def arrayCollect : (X →₀ D) →+ (K →₀ D) := Finsupp.mapDomain.addMonoidHom C.key

@[simp] theorem arrayCollect_single (x : X) (d : D) :
    C.arrayCollect D (Finsupp.single x d) = Finsupp.single (C.key x) d :=
  Finsupp.mapDomain_single

@[simp] theorem arrayBall_zero (b : ℕ) : C.arrayBall D b 0 := by simp [arrayBall]

theorem arrayBall_single {b : ℕ} {x : X} (hx : x ∈ C.ball b) (d : D) :
    C.arrayBall D b (Finsupp.single x d) := by
  intro y hy
  simpa only [((Finsupp.mem_support_single y x d).mp hy).1] using hx

theorem arrayBall_add {b : ℕ} {p q : X →₀ D}
    (hp : C.arrayBall D b p) (hq : C.arrayBall D b q) : C.arrayBall D b (p+q) := by
  intro x hx
  rcases Finset.mem_union.mp (Finsupp.support_add hx) with hx | hx
  · exact hp x hx
  · exact hq x hx

theorem arrayBall_mono {b c : ℕ} (hbc : b ≤ c) {p : X →₀ D}
    (hp : C.arrayBall D b p) : C.arrayBall D c p := fun x hx => C.mono hbc (hp x hx)

theorem array_induction {b : ℕ} {P : (X →₀ D) → Prop}
    (hz : P 0) (hs : ∀ x ∈ C.ball b, ∀ d : D, P (Finsupp.single x d))
    (ha : ∀ p q, P p → P q → P (p+q)) {p : X →₀ D} (hp : C.arrayBall D b p) : P p := by
  revert hp
  induction p using Finsupp.induction with
  | zero => exact fun _ => hz
  | single_add x d p hx hd ih =>
    intro hp
    have hb : x ∈ C.ball b := hp x (by rw [Finsupp.support_single_add hx hd]; simp)
    have hq : C.arrayBall D b p := by
      intro y hy
      exact hp y (by rw [Finsupp.support_single_add hx hd]; simp [hy])
    exact ha _ _ (hs x hb d) (ih hq)

def arrays : KeyBall (X →₀ D) (K →₀ D) where
  ball := C.arrayBall D
  mono := fun _ _ hbc _ hp => C.arrayBall_mono D hbc hp
  key := C.arrayCollect D

variable (m : ℕ) [Nonempty X]

def arrayCanonical : (X →₀ D) →+ (X →₀ D) :=
  Finsupp.mapDomain.addMonoidHom (C.canonical m)

@[simp] theorem arrayCanonical_single (x : X) (d : D) :
    C.arrayCanonical D m (Finsupp.single x d) = Finsupp.single (C.canonical m x) d :=
  Finsupp.mapDomain_single

theorem arrayCanonical_congr {p q : X →₀ D}
    (he : C.arrayCollect D p = C.arrayCollect D q) :
    C.arrayCanonical D m p = C.arrayCanonical D m q := by
  change Finsupp.mapDomain (C.representative m ∘ C.key) p =
    Finsupp.mapDomain (C.representative m ∘ C.key) q
  rw [Finsupp.mapDomain_comp, Finsupp.mapDomain_comp]
  exact congrArg (Finsupp.mapDomain (C.representative m)) he

end KeyBall

namespace KeyBall
variable {V K : Type*} [Monoid V] (C : KeyBall V K) (D : Type*) [Semiring D]

def algebraBall (b : ℕ) (p : MonoidAlgebra D V) : Prop := C.arrayBall D b p.coeff

def algebraCollect : MonoidAlgebra D V →+ (K →₀ D) :=
  (C.arrayCollect D).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

@[simp] theorem algebraCollect_single {V K : Type*} [Monoid V]
    (C : KeyBall V K) (D : Type*) [Semiring D] (v : V) (d : D) :
    C.algebraCollect D (MonoidAlgebra.single v d) = Finsupp.single (C.key v) d := by
  change C.arrayCollect D (Finsupp.single v d) = _
  exact C.arrayCollect_single D v d

@[simp] theorem algebraBall_zero (b : ℕ) : C.algebraBall D b 0 := C.arrayBall_zero D b

theorem algebraBall_single {V K : Type*} [Monoid V]
    (C : KeyBall V K) (D : Type*) [Semiring D] {b : ℕ} {v : V}
    (hv : v ∈ C.ball b) (d : D) :
    C.algebraBall D b (MonoidAlgebra.single v d) := C.arrayBall_single D hv d

theorem algebraBall_add {b : ℕ} {p q : MonoidAlgebra D V}
    (hp : C.algebraBall D b p) (hq : C.algebraBall D b q) : C.algebraBall D b (p+q) :=
  C.arrayBall_add D hp hq

theorem algebra_induction {b : ℕ} {P : MonoidAlgebra D V → Prop}
    (hz : P 0) (hs : ∀ v ∈ C.ball b, ∀ d : D, P (MonoidAlgebra.single v d))
    (ha : ∀ p q, P p → P q → P (p+q)) {p : MonoidAlgebra D V} (hp : C.algebraBall D b p) :
    P p := by
  have hh := C.array_induction D (P := fun a => P (MonoidAlgebra.ofCoeff a))
    hz (by intro v hv d; exact hs v hv d)
    (by intro p q hp hq; exact ha _ _ hp hq) hp
  simpa only [MonoidAlgebra.ofCoeff_coeff] using hh

variable (m : ℕ)

def algebraCanonical : MonoidAlgebra D V →+ MonoidAlgebra D V :=
  MonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((C.arrayCanonical D m).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

@[simp] theorem algebraCanonical_single (v : V) (d : D) :
    C.algebraCanonical D m (MonoidAlgebra.single v d) =
      MonoidAlgebra.single (C.canonical m v) d := by
  change MonoidAlgebra.ofCoeff (C.arrayCanonical D m (Finsupp.single v d)) = _
  rw [C.arrayCanonical_single D m, MonoidAlgebra.ofCoeff_single]

theorem algebraCanonical_congr {p q : MonoidAlgebra D V}
    (he : C.algebraCollect D p = C.algebraCollect D q) :
    C.algebraCanonical D m p = C.algebraCanonical D m q :=
  congrArg MonoidAlgebra.ofCoeff (C.arrayCanonical_congr D m he)

end KeyBall

namespace ActionCalculus
variable {V X K L : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m) (D : Type*) [Ring D]

theorem algebra_mul_mem {p q : MonoidAlgebra D V} {b c : ℕ}
    (hp : C.group.algebraBall D b p) (hq : C.group.algebraBall D c q) :
    C.group.algebraBall D (b+c) (p*q) := by
  apply C.group.algebra_induction D (P := fun p => C.group.algebraBall D (b+c) (p*q))
    ?_ ?_ ?_ hp
  · simp
  · intro u hu a
    apply C.group.algebra_induction D
      (P := fun q => C.group.algebraBall D (b+c) (MonoidAlgebra.single u a*q)) ?_ ?_ ?_ hq
    · simp
    · intro v hv d
      rw [MonoidAlgebra.single_mul_single]
      exact C.group.algebraBall_single D (C.mul_mem hu hv) _
    · intro x y hx hy
      rw [mul_add]
      exact C.group.algebraBall_add D hx hy
  · intro x y hx hy
    rw [add_mul]
    exact C.group.algebraBall_add D hx hy

theorem array_action_mem {p : MonoidAlgebra D V} {x : X →₀ D} {b c : ℕ}
    (hp : C.group.algebraBall D b p) (hx : C.point.arrayBall D c x) :
    C.point.arrayBall D (b+c) (SourceEnlargement.ringAction p x) := by
  apply C.group.algebra_induction D
    (P := fun p => C.point.arrayBall D (b+c) (SourceEnlargement.ringAction p x)) ?_ ?_ ?_ hp
  · simp
  · intro v hv a
    apply C.point.array_induction D
      (P := fun x => C.point.arrayBall D (b+c)
        (SourceEnlargement.ringAction (MonoidAlgebra.single v a) x)) ?_ ?_ ?_ hx
    · simp
    · intro z hz d
      rw [SourceEnlargement.ringAction_single]
      exact C.point.arrayBall_single D (C.smul_mem hv hz) _
    · intro x y hx hy
      rw [map_add]
      exact C.point.arrayBall_add D hx hy
  · intro p q hp hq
    rw [map_add]
    exact C.point.arrayBall_add D hp hq

end ActionCalculus
end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
end


