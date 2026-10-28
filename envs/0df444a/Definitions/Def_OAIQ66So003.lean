-- Prove2me | Definitions.Def_OAIQ66So003
-- name    : OAIQ66So003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:10:17.295101+00:00
-- url     : https://prove2.me/theorems/4e48fc65-9bc1-4d43-b71b-c6e267f98e7e
-- title:
--   Definitions bundle OAIQ66So003 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 121 declarations of OpenAI's Lean: 45 definitions, 5 inductive types or structures, 2 instances and 69 theorems. The definitions and types are `OAI.CWEquivariant.module`, `OAI.CWEquivariant.object`, `OAI.CWEquivariant.onSpace`, `OAI.CWEquivariant.rep`, `OAI.CWUniverse.chart`, `OAI.CWUniverse.cw`, `OAI.CWUniverse.piOne`, `OAI.CategoryTheory.ShortComplex.concreteCyclesMap`, `OAI.CategoryTheory.ShortComplex.concreteHomologyMap`, `OAI.CategoryTheory.ShortComplex.concreteHomologyMapData`, `OAI.CompressedSplittings.BinaryData`, `OAI.CompressedSplittings.BinaryData.firstExchange`, `OAI.CompressedSplittings.BinaryData.secondExchange`, `OAI.CompressedSplittings.Idempotent`, `OAI.CompressedSplittings.Idempotent.coefficient`, `OAI.NoncommElementary.root`, `OAI.PartialResolution.augmentation`, `OAI.PartialResolution.complex`, `OAI.PartialResolution.d`, `OAI.PartialResolution.headIso`, `OAI.PartialResolution.nextIso`, `OAI.PartialResolution.obj`, `OAI.PartialResolution.resolution`, `OAI.PartialResolution.seam`, `OAI.PartialResolution.startIso`, `OAI.PartialResolution.tailIso`, `OAI.ProductCriterion.coordinate`, `OAI.ProductCriterion.evalPair`, `OAI.ProductCriterion.moduleIso`, `OAI.ProductCriterion.moduleMap`, `OAI.ProductCriterion.tensorMap`, `OAI.ProductFiniteResolution.kerRep`, `OAI.ProductFiniteResolution.kerι`, `OAI.ProductFiniteResolution.repMap`, `OAI.RegularProductR.Module`, `OAI.RegularProductR.rep`, `OAI.RegularProductR.representation`, `OAI.RegularProductR.rightShift`, `OAI.RingExchange.Data`, `OAI.RingExchange.Data.unit` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`FiniteType_CategoryTheoryShortComplex`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/CategoryTheoryShortComplex.lean), [`FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/ClassifyingSpacesFiniteExtensionGeometricFromProducts.lean), [`FiniteType_CompressedSplittings`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/CompressedSplittings.lean), [`FiniteType_PartialResolution`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/PartialResolution.lean), [`FiniteType_PartialResolutionPartialCyclesFg`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/PartialResolutionPartialCyclesFg.lean), [`FiniteType_ProductFiniteResolution`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/ProductFiniteResolution.lean), [`FiniteType_RingExchange`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/RingExchange.lean), [`FiniteType_SingularChains`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/SingularChains.lean), [`FiniteType_SingularSigmaSingleMerge`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/SingularSigmaSingleMerge.lean), [`FiniteType_StageGeometry`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/StageGeometry.lean), [`FiniteType_Steinberg`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/Steinberg.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So011`, `OAIQ66So013` and `OAIQ66So014`; the statements `OAI.ProductFiniteResolution.finite_free_resolution_of_products` and `OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ066_SO.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSigmaSingleMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
attribute [-instance] AddCommGroup.toIntModule

attribute [instance] AddCommGroup.toIntModule

end

namespace CWEquivariant
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory HomologicalComplex
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]

abbrev rep (n : ℕ) := Representation.ofMulAction ℤ G (RelCWComplex.cell (univ : Set X) n)

abbrev module (n : ℕ) := (rep (G := G) (X := X) n).asModule

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CWEquivariant
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory HomologicalComplex
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]

abbrev object (n : ℕ) : Rep ℤ G := Rep.of (rep (G:=G) (X:=X) n)

def onSpace (g : G) : C((univ : Set X),(univ : Set X)) :=
  ⟨fun x => ⟨g • x.1,mem_univ _⟩,
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

namespace RegularProductR
open _root_.CategoryTheory
variable (k G I : Type) [CommRing k] [Group G]

abbrev Module := I → (G →₀ k)

def rightShift (g : G) : (G →₀ k) →ₗ[k] (G →₀ k) :=
  Finsupp.lmapDomain k k (fun x => x*g⁻¹)

@[simp] lemma rightShift_single (g x : G) (r : k) :
    rightShift k G g (Finsupp.single x r) = Finsupp.single (x*g⁻¹) r := by
  simp [rightShift]

lemma rightShift_one : rightShift k G 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x r
  simp

lemma rightShift_mul (g h : G) :
    rightShift k G (g*h) = (rightShift k G g).comp (rightShift k G h) := by
  apply Finsupp.lhom_ext
  intro x r
  simp [mul_assoc]

def representation : Representation k G (Module k G I) where
  toFun g := LinearMap.pi (fun i => (rightShift k G g).comp (LinearMap.proj i))
  map_one' := by
    apply LinearMap.ext
    intro a
    funext i
    exact LinearMap.congr_fun (rightShift_one k G) (a i)
  map_mul' g h := by
    apply LinearMap.ext
    intro a
    funext i
    exact LinearMap.congr_fun (rightShift_mul k G g h) (a i)

abbrev rep : Rep k G := Rep.of (representation k G I)

end RegularProductR

namespace ProductCriterion
open _root_.CategoryTheory _root_.Representation
open scoped TensorProduct MonoidAlgebra MonoidalCategory
variable {k G I : Type} [CommRing k] [Group G]

lemma rightShift_eq_mul (g : G) (a : G →₀ k) :
    MonoidAlgebra.ofCoeff (RegularProductR.rightShift k G g a) =
      MonoidAlgebra.ofCoeff a * MonoidAlgebra.of k G g⁻¹ := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,MonoidAlgebra.ofCoeff_add,ha,hb,add_mul]
  | single x r => simp [MonoidAlgebra.of_apply,MonoidAlgebra.single_mul_single]

variable (C : Rep k G)

def evalPair (i : I) : RegularProductR.Module k G I →ₗ[k] C →ₗ[k] C :=
  C.ρ.asAlgebraHom.toLinearMap.comp
    ((MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap.comp (LinearMap.proj i))

lemma evalPair_invariant (i : I) (g : G)
    (a : RegularProductR.Module k G I) (c : C) :
    evalPair C i (RegularProductR.representation k G I g a) (C.ρ g c) = evalPair C i a c := by
  change C.ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (RegularProductR.rightShift k G g (a i))) (C.ρ g c) = _
  rw [rightShift_eq_mul,map_mul,Representation.asAlgebraHom_of]
  change C.ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (a i)) ((C.ρ g⁻¹) (C.ρ g c)) = _
  have h : (C.ρ g⁻¹) (C.ρ g c) = c := by
    change (C.ρ g⁻¹ * C.ρ g) c = c
    rw [← map_mul,inv_mul_cancel,map_one]
    rfl
  rw [h]
  rfl

def coordinate (i : I) :
    (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants →ₗ[k] C :=
  Coinvariants.lift _ (TensorProduct.lift (evalPair C i)) (fun g => by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro c
    exact evalPair_invariant C i g a c)

@[simp] lemma coordinate_mk_tmul (i : I)
    (a : RegularProductR.Module k G I) (c : C) :
    coordinate C i (Coinvariants.mk _ (a ⊗ₜ[k] c)) = C.ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (a i)) c := rfl

lemma coordinates_finite_span (y : (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants) :
    ∃ s : Finset C.ρ.asModule, ∀ i : I,
      C.ρ.asModuleEquiv.symm (coordinate C i y) ∈ Submodule.span k[G] (s : Set C.ρ.asModule) := by
  classical
  induction y using Coinvariants.induction_on with
  | h y =>
    induction y using OAI.tensorInductionOn with
    | tmul a c =>
      refine ⟨{C.ρ.asModuleEquiv.symm c},fun i => ?_⟩
      simp only [Finset.coe_singleton]
      apply Submodule.mem_span_singleton.mpr
      refine ⟨MonoidAlgebra.ofCoeff (a i),?_⟩
      apply C.ρ.asModuleEquiv.injective
      rw [Representation.asModuleEquiv_map_smul,LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      rfl
    | add x y hx hy =>
      obtain ⟨sx,hx⟩ := hx
      obtain ⟨sy,hy⟩ := hy
      refine ⟨sx∪sy,fun i => ?_⟩
      simp only [map_add]
      apply Submodule.add_mem
      · exact Submodule.span_mono (by simp only [Finset.coe_union]; exact Set.subset_union_left) (hx i)
      · exact Submodule.span_mono (by simp only [Finset.coe_union]; exact Set.subset_union_right) (hy i)

variable {C} (D : Rep k G)

lemma map_asAlgebraHom (f : C ⟶ D) (a : k[G]) (c : C) :
    f.hom (C.ρ.asAlgebraHom a c) = D.ρ.asAlgebraHom a (f.hom c) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb]
  | single g r => simp [Representation.asAlgebraHom_single,f.hom.isIntertwining]

def tensorMap (f : C ⟶ D) : (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants →ₗ[k]
    (RegularProductR.rep k G I ⊗ D).ρ.Coinvariants :=
  Coinvariants.map _ _ ((IntertwiningMap.id _).tensor f.hom)

lemma coordinate_natural (f : C ⟶ D) (i : I)
    (y : (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants) :
    coordinate D i (tensorMap D f y) = f.hom (coordinate C i y) := by
  induction y using Coinvariants.induction_on with
  | h y =>
    induction y using OAI.tensorInductionOn with
    | add x y hx hy =>
      simp only [map_add]
      exact congrArg₂ (·+·) hx hy
    | tmul a c =>
      change D.ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (a i)) (f.hom c) =
        f.hom (C.ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (a i)) c)
      exact (map_asAlgebraHom D f _ c).symm

variable (α : Type) [DecidableEq α]

omit [DecidableEq α] in
lemma free_algebra_action (a : k[G]) (c : Rep.free k G α) :
    (Rep.free k G α).ρ.asAlgebraHom a c = a • (c : α →₀ k[G]) := by
  exact (congrArg (free k G α).asModuleEquiv
    ((finsuppLEquivFreeAsModule k G α).map_smul a c)).symm

lemma coordinate_free_inverse_single (i : I) (j : α) (a : RegularProductR.Module k G I) :
    coordinate (Rep.free k G α) i
      ((Rep.coinvariantsTensorFreeLEquiv (RegularProductR.rep k G I) α).symm
        (Finsupp.single j a)) = Finsupp.single j (MonoidAlgebra.ofCoeff (a i)) := by
  change coordinate (Rep.free k G α) i
    (Rep.finsuppToCoinvariantsTensorFree _ _ (Finsupp.single j a)) = _
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  change (Rep.free k G α).ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (a i))
    (Finsupp.single j (MonoidAlgebra.single 1 1)) = _
  rw [free_algebra_action,Finsupp.smul_single]
  change Finsupp.single j (MonoidAlgebra.ofCoeff (a i) * 1) = _
  rw [mul_one]

lemma coordinate_free_inverse_apply (i : I) (j : α) (z : α →₀ RegularProductR.Module k G I) :
    coordinate (Rep.free k G α) i
      ((Rep.coinvariantsTensorFreeLEquiv (RegularProductR.rep k G I) α).symm z) j =
      MonoidAlgebra.ofCoeff (z j i) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,Pi.add_apply,MonoidAlgebra.ofCoeff_add,hx,hy]
  | single l a =>
    rw [coordinate_free_inverse_single]
    by_cases h : l=j
    · subst l; simp
    · simp [h]

lemma free_coordinates_injective : Function.Injective
    (fun y : (RegularProductR.rep k G I ⊗ Rep.free k G α).ρ.Coinvariants =>
        fun i : I => coordinate (Rep.free k G α) i y) := by
  intro x y h
  let E := Rep.coinvariantsTensorFreeLEquiv (RegularProductR.rep k G I) α
  apply E.injective
  apply Finsupp.ext
  intro j
  funext i
  apply MonoidAlgebra.ofCoeff_injective
  have hh := congrArg (fun f : I → Rep.free k G α => f i j) h
  have hx := coordinate_free_inverse_apply α i j (E x)
  have hy := coordinate_free_inverse_apply α i j (E y)
  rw [E.symm_apply_apply] at hx hy
  exact hx.symm.trans (hh.trans hy)

lemma free_coordinates_surjective [Finite α] : Function.Surjective
    (fun y : (RegularProductR.rep k G I ⊗ Rep.free k G α).ρ.Coinvariants =>
        fun i : I => coordinate (Rep.free k G α) i y) := by
  intro f
  let z : α →₀ RegularProductR.Module k G I :=
    (Finsupp.linearEquivFunOnFinite k (RegularProductR.Module k G I) α).symm
      (fun j i => (f i j).coeff)
  refine ⟨(Rep.coinvariantsTensorFreeLEquiv (RegularProductR.rep k G I) α).symm z,?_⟩
  funext i
  ext j
  rw [coordinate_free_inverse_apply]
  rfl

variable {D α}

def moduleMap (f : C ⟶ D) : C.ρ.asModule →ₗ[k[G]] D.ρ.asModule :=
  IntertwiningMap.equivLinearMapAsModule _ _ f.hom

@[simp] lemma moduleMap_apply (f : C ⟶ D) (c : C) :
    moduleMap f (C.ρ.asModuleEquiv.symm c) = D.ρ.asModuleEquiv.symm (f.hom c) := rfl

lemma kernel_fg_of_product_exact {α β : Type} [Finite α] (B : Rep k G)
    (f : B ⟶ Rep.free k G α) (g : Rep.free k G α ⟶ Rep.free k G β)
    (hfg : f ≫ g = 0)
    (hexact : ∀ I : Type,
      ∀ x : (RegularProductR.rep k G I ⊗ Rep.free k G α).ρ.Coinvariants,
        tensorMap (Rep.free k G β) g x = 0 →
          ∃ y : (RegularProductR.rep k G I ⊗ B).ρ.Coinvariants,
            tensorMap (Rep.free k G α) f y = x) : (moduleMap g).ker.FG := by
  classical
  let K := (moduleMap g).ker
  let z : K → Rep.free k G α := fun t => (Rep.free k G α).ρ.asModuleEquiv t.val
  obtain ⟨x,hx⟩ := free_coordinates_surjective (k:=k) (G:=G) (I:=K) α z
  have hcycle : tensorMap (Rep.free k G β) g x = 0 := by
    apply free_coordinates_injective β
    funext t
    dsimp only
    rw [coordinate_natural,map_zero]
    have hxt : coordinate (Rep.free k G α) t x = z t := congrFun hx t
    rw [hxt]
    change g.hom (z t) = 0
    have ht := t.property
    change moduleMap g t.val = 0 at ht
    exact congrArg (Rep.free k G β).ρ.asModuleEquiv ht
  obtain ⟨y,hy⟩ := hexact K x hcycle
  obtain ⟨s,hs⟩ := coordinates_finite_span B y
  refine Submodule.fg_def.mpr ⟨moduleMap f '' (s : Set B.ρ.asModule),
    s.finite_toSet.image _,le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨c,hc,rfl⟩
    change moduleMap g (moduleMap f c) = 0
    have h := congrArg (fun l : B ⟶ Rep.free k G β => l.hom (B.ρ.asModuleEquiv c)) hfg
    exact congrArg (Rep.free k G β).ρ.asModuleEquiv.symm h
  · intro t ht
    let t' : K := ⟨t,ht⟩
    have hm := Submodule.mem_map_of_mem (f:=moduleMap f) (hs t')
    rw [Submodule.map_span] at hm
    have he : moduleMap f (B.ρ.asModuleEquiv.symm (coordinate B t' y)) = t := by
      rw [moduleMap_apply]
      apply (Rep.free k G α).ρ.asModuleEquiv.injective
      rw [LinearEquiv.apply_symm_apply,← coordinate_natural,hy]
      exact congrFun hx t'
    exact he ▸ hm

lemma kernel_fg_of_tensor_homology_zero {α β : Type} [Finite α] (B : Rep k G)
    (f : B ⟶ Rep.free k G α) (g : Rep.free k G α ⟶ Rep.free k G β)
    (hfg : f ≫ g = 0)
    (hzero : ∀ I : Type, CategoryTheory.Limits.IsZero
      (((ShortComplex.mk f g hfg).map
        ((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I))).homology)) :
    (moduleMap g).ker.FG := by
  apply kernel_fg_of_product_exact B f g hfg
  intro I x hx
  have he := (ShortComplex.exact_iff_isZero_homology _).mpr (hzero I)
  exact (ShortComplex.moduleCat_exact_iff _).mp he x hx

lemma product_resolution_exact (P : ProjectiveResolution (Rep.trivial k G k)) (n : ℕ)
    (hzero : ∀ I : Type, CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep k G I) n)) (I : Type) :
    (P.complex.coinvariantsTensorObj (RegularProductR.rep k G I)).ExactAt n := by
  classical
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  exact (hzero I).of_iso (groupHomologyIso (RegularProductR.rep k G I) n P).symm

end ProductCriterion

end

end OAI
end

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

def repMap {C D : Rep k G} (f : C.ρ.asModule →ₗ[k[G]] D.ρ.asModule) : C ⟶ D :=
  Rep.ofHom ((IntertwiningMap.equivLinearMapAsModule C.ρ D.ρ).symm f)

@[simp] lemma moduleMap_repMap {C D : Rep k G}
    (f : C.ρ.asModule →ₗ[k[G]] D.ρ.asModule) :
    ProductCriterion.moduleMap (repMap f) = f :=
  (IntertwiningMap.equivLinearMapAsModule C.ρ D.ρ).apply_symm_apply f

@[simp] lemma repMap_moduleMap {C D : Rep k G} (f : C ⟶ D) :
    repMap (ProductCriterion.moduleMap f) = f := by
  apply Rep.hom_injective
  exact (IntertwiningMap.equivLinearMapAsModule C.ρ D.ρ).symm_apply_apply f.hom

abbrev kerRep {C D : Rep k G} (f : C ⟶ D) : Rep k G :=
  Rep.of f.hom.ker.toRepresentation

def kerι {C D : Rep k G} (f : C ⟶ D) : kerRep f ⟶ C :=
  Rep.ofHom ⟨f.hom.ker.toSubmodule.subtype, fun _ => rfl⟩

@[simp] lemma kerι_apply {C D : Rep k G} (f : C ⟶ D) (x : kerRep f) :
    (kerι f).hom x = x.val := rfl

@[reassoc (attr := simp)] lemma kerι_comp {C D : Rep k G} (f : C ⟶ D) :
    kerι f ≫ f = 0 := by
  ext x
  exact x.property

end ProductFiniteResolution

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PartialResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PartialResolution
open _root_.CategoryTheory CategoryTheory.Limits
open ProductFiniteResolution
variable {k G : Type} [CommRing k] [Group G]
variable (C : ChainComplex (Rep k G) ℕ) (N : ℕ)
  (P : ProjectiveResolution (kerRep (C.d N (N-1))))

def obj (i : ℕ) : Rep k G := if i ≤ N then C.X i else P.complex.X (i-(N+1))

def headIso (i : ℕ) (h : i ≤ N) : obj C N P i ≅ C.X i :=
  eqToIso (by simp [obj,h])

def tailIso (i : ℕ) (h : N < i) : obj C N P i ≅ P.complex.X (i-(N+1)) :=
  eqToIso (by simp [obj,Nat.not_le.mpr h])

def seam : obj C N P (N+1) ⟶ obj C N P N :=
  (tailIso C N P (N+1) (by omega)).hom ≫
    eqToHom (by simp) ≫ P.π.f 0 ≫ kerι (C.d N (N-1)) ≫ (headIso C N P N le_rfl).inv

def d (i : ℕ) : obj C N P (i+1) ⟶ obj C N P i :=
  if h : i < N then
    (headIso C N P (i+1) (by omega)).hom ≫ C.d (i+1) i ≫ (headIso C N P i (by omega)).inv
  else if e : i = N then by subst i; exact seam C N P
  else (tailIso C N P (i+1) (by omega)).hom ≫
    P.complex.d ((i+1)-(N+1)) (i-(N+1)) ≫ (tailIso C N P i (by omega)).inv

lemma d_head (i : ℕ) (h : i < N) : d C N P i =
    (headIso C N P (i+1) (by omega)).hom ≫ C.d (i+1) i ≫ (headIso C N P i (by omega)).inv := by
  simp [d,h]

lemma d_seam : d C N P N = seam C N P := by simp [d]

lemma d_tail (i : ℕ) (h : N < i) : d C N P i =
    (tailIso C N P (i+1) (by omega)).hom ≫
      P.complex.d ((i+1)-(N+1)) (i-(N+1)) ≫ (tailIso C N P i h).inv := by
  simp [d,show ¬i<N by omega,show i≠N by omega]

lemma d_comp (hN : 0 < N) (i : ℕ) : d C N P (i+1) ≫ d C N P i = 0 := by
  by_cases h : i+1 < N
  · rw [d_head C N P (i+1) h,d_head C N P i (by omega)]
    simp only [Category.assoc,Iso.inv_hom_id_assoc,HomologicalComplex.d_comp_d_assoc,zero_comp,comp_zero]
  · by_cases e : i+1 = N
    · subst N
      rw [d_seam,d_head C (i+1) P i (by omega)]
      simp [seam,Category.assoc]
      erw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, kerι_comp_assoc,
        zero_comp, comp_zero]
    · by_cases e' : i = N
      · subst i
        rw [d_tail C N P (N+1) (by omega),d_seam]
        simp [seam,Category.assoc]
        rw [show N+1+1-(N+1)=1 by omega]
        erw [P.complex_d_comp_π_f_zero_assoc,zero_comp]
      · rw [d_tail C N P (i+1) (by omega),d_tail C N P i (by omega)]
        simp only [Category.assoc,Iso.inv_hom_id_assoc,HomologicalComplex.d_comp_d_assoc,zero_comp,comp_zero]

def complex (hN : 0 < N) : ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (obj C N P) (d C N P) (d_comp C N P hN)

@[simp] lemma complex_X (hN : 0 < N) (i : ℕ) : (complex C N P hN).X i = obj C N P i := rfl
@[simp] lemma complex_d (hN : 0 < N) (i : ℕ) : (complex C N P hN).d (i+1) i = d C N P i := by
  simp [complex]

lemma exact_seam :
    (ShortComplex.mk (P.π.f 0 ≫ kerι (C.d N (N-1))) (C.d N (N-1))
      (by erw [Category.assoc, kerι_comp, comp_zero])).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y,hy⟩ := ((Rep.epi_iff_surjective (P.π.f 0)).mp inferInstance) ⟨x,hx⟩
  exact ⟨y,congrArg Subtype.val hy⟩

lemma exact_after_seam :
    (ShortComplex.mk (P.complex.d 1 0) (P.π.f 0 ≫ kerι (C.d N (N-1)))
      (by erw [P.complex_d_comp_π_f_zero_assoc, zero_comp])).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : (P.π.f 0).hom x = 0 := by
    apply Subtype.ext
    exact hx
  exact (ShortComplex.moduleCat_exact_iff _).mp
    (P.exact₀.map (forget₂ (Rep k G) (ModuleCat k))) x hx'

def startIso : obj C N P (N+1) ≅ P.complex.X 0 :=
  tailIso C N P (N+1) (by omega) ≪≫ eqToIso (by simp)

def nextIso : obj C N P (N+1+1) ≅ P.complex.X 1 :=
  tailIso C N P (N+1+1) (by omega) ≪≫ eqToIso (by congr 1; omega)

lemma exactAt_succ (hN : 0 < N)
    (hex : ∀ i, 0 < i → i < N → C.ExactAt i) (i : ℕ) :
    (complex C N P hN).ExactAt (i+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',complex,ChainComplex.of_d]
  change (ShortComplex.mk (d C N P (i+1)) (d C N P i) (d_comp C N P hN i)).Exact
  by_cases h : i+1 < N
  · have he := (HomologicalComplex.exactAt_iff' C (i+1+1) (i+1) i (by simp) (by simp)).mp
      (hex (i+1) (by omega) h)
    apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
      (headIso C N P (i+1+1) (by omega)) (headIso C N P (i+1) (by omega))
      (headIso C N P i (by omega)) ?_ ?_)).mpr he
    · simp [d_head C N P (i+1) h,Category.assoc]
      erw [Iso.inv_hom_id, Category.comp_id]
      rfl
    · simp [d_head C N P i (by omega : i<N),Category.assoc]
      erw [Iso.inv_hom_id, Category.comp_id]
      rfl
  · by_cases e : i+1 = N
    · subst N
      apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
        (startIso C (i+1) P) (headIso C (i+1) P (i+1) le_rfl)
        (headIso C (i+1) P i (by omega)) ?_ ?_)).mpr (exact_seam C (i+1) P)
      · simp [d_seam,seam,startIso,Category.assoc]
        erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · simp [d_head C (i+1) P i (by omega),Category.assoc]
    · by_cases e' : i=N
      · subst i
        apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
          (nextIso C N P) (startIso C N P) (headIso C N P N le_rfl) ?_ ?_)).mpr
          (exact_after_seam C N P)
        · simp [d_tail C N P (N+1) (by omega),nextIso,startIso,Category.assoc]
        · simp [d_seam,seam,startIso,Category.assoc]
          erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · have ht : N < i := by omega
        have hp : P.complex.ExactAt (i+1-(N+1)) := by
          have eq : i+1-(N+1) = (i-(N+1))+1 := by omega
          rw [eq]
          exact P.complex_exactAt_succ _
        have he := (HomologicalComplex.exactAt_iff' P.complex
          ((i+1+1)-(N+1)) ((i+1)-(N+1)) (i-(N+1)) (by apply ComplexShape.prev_eq'; change _+1=_; omega)
          (by apply ComplexShape.next_eq'; change _+1=_; omega)).mp hp
        apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
          (tailIso C N P (i+1+1) (by omega)) (tailIso C N P (i+1) (by omega))
          (tailIso C N P i ht) ?_ ?_)).mpr he
        · simp [d_tail C N P (i+1) (by omega),Category.assoc]
          erw [Iso.inv_hom_id, Category.comp_id]
          rfl
        · simp [d_tail C N P i ht,Category.assoc]
          erw [Iso.inv_hom_id, Category.comp_id]
          rfl

instance obj_projective [∀ i, Projective (C.X i)] (i : ℕ) : Projective (obj C N P i) := by
  dsimp [obj]
  split <;> infer_instance

instance complex_projective [∀ i, Projective (C.X i)] (hN : 0<N) (i : ℕ) :
    Projective ((complex C N P hN).X i) := obj_projective C N P i

def augmentation {Z : Rep k G} (hN : 0<N) (ε : C.X 0 ⟶ Z) (hε : C.d 1 0 ≫ ε = 0) :
    complex C N P hN ⟶ (ChainComplex.single₀ (Rep k G)).obj Z :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨(headIso C N P 0 (by omega)).hom ≫ ε, by
    rw [complex_d,d_head C N P 0 hN]
    simp [Category.assoc,hε]
    rfl⟩

def resolution {Z : Rep k G} [∀ i, Projective (C.X i)]
    (hN : 0<N) (ε : C.X 0 ⟶ Z) [Epi ε] (hε : C.d 1 0 ≫ ε = 0)
    (he₀ : (ShortComplex.mk (C.d 1 0) ε hε).Exact)
    (hex : ∀ i, 0 < i → i < N → C.ExactAt i) : ProjectiveResolution Z where
  complex := complex C N P hN
  π := augmentation C N P hN ε hε
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨he₀,inferInstance⟩
        exact ShortComplex.isoMk (headIso C N P 1 (by omega))
          (headIso C N P 0 (by omega)) (Iso.refl _) (by
            simp [complex_d,d_head C N P 0 hN]
            erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])
          (by
            simp only [augmentation,Iso.refl_hom]
            erw [Category.comp_id]
            exact (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
              (C := complex C N P hN) (X := Z) _ _).symm)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact exactAt_succ C N P hN hex n
      · apply ChainComplex.exactAt_succ_single_obj⟩

lemma complex_head_d (hN : 0<N) (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    (complex C N P hN).d i j ≫ (headIso C N P j hj).hom =
      (headIso C N P i hi).hom ≫ C.d i j := by
  by_cases h : j+1=i
  · subst i
    rw [complex_d,d_head C N P j (by omega)]
    simp
  · erw [(complex C N P hN).shape i j h,C.shape i j h,zero_comp,comp_zero]
    rfl

end PartialResolution

namespace ProductCriterion
open _root_.CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
variable {k G : Type} [CommRing k] [Group G]

@[simp] lemma moduleMap_comp {A B C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) :
    moduleMap (f ≫ g) = (moduleMap g).comp (moduleMap f) := rfl
@[simp] lemma moduleMap_id (C : Rep k G) : moduleMap (𝟙 C) = LinearMap.id := rfl

def moduleIso {C D : Rep k G} (e : C ≅ D) : C.ρ.asModule ≃ₗ[k[G]] D.ρ.asModule :=
  LinearEquiv.ofLinearMap (moduleMap e.hom) (moduleMap e.inv) (by
    rw [← moduleMap_comp,e.inv_hom_id,moduleMap_id]) (by
    rw [← moduleMap_comp,e.hom_inv_id,moduleMap_id])

lemma kernel_fg_of_iso {B C D : Rep k G} (f : B ⟶ C) (g : C ⟶ D)
    (hfg : f ≫ g = 0) {α β : Type} [Finite α]
    (eC : C ≅ Rep.free k G α) (eD : D ≅ Rep.free k G β)
    (hex : ∀ I : Type, ((ShortComplex.mk f g hfg).map
      ((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I))).Exact) :
    (moduleMap g).ker.FG := by
  let f' := f ≫ eC.hom
  let g' := eC.inv ≫ g ≫ eD.hom
  have hc : f' ≫ g' = 0 := by
    simp only [f',g',Category.assoc,eC.hom_inv_id_assoc]
    rw [← Category.assoc,hfg,zero_comp]
  have he (I : Type) : ((ShortComplex.mk f' g' hc).map
      ((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I))).Exact := by
    let E : ShortComplex.mk f g hfg ≅ ShortComplex.mk f' g' hc :=
      ShortComplex.isoMk (Iso.refl _) eC eD (by simp [f'])
        (by simp [g'])
    exact (ShortComplex.exact_iff_of_iso
      ((((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I)).mapShortComplex).mapIso E)).mp (hex I)
  have hfg' : (moduleMap g').ker.FG := kernel_fg_of_tensor_homology_zero B f' g' hc
    (fun I => (ShortComplex.exact_iff_isZero_homology _).mp (he I))
  have hmap : ((moduleMap g').ker).map (moduleMap eC.inv) = (moduleMap g).ker := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      have hy' : moduleMap eD.hom (moduleMap g (moduleMap eC.inv y)) = 0 := hy
      apply (moduleIso eD).injective
      change moduleMap eD.hom (moduleMap g (moduleMap eC.inv y)) = moduleMap eD.hom 0
      simpa using hy'
    · intro hx
      refine ⟨moduleMap eC.hom x,?_,?_⟩
      · change moduleMap eD.hom (moduleMap g (moduleMap eC.inv (moduleMap eC.hom x))) = 0
        have hi : moduleMap eC.inv (moduleMap eC.hom x) = x := (moduleIso eC).left_inv x
        rw [hi,show moduleMap g x = 0 from hx,map_zero]
      · exact (moduleIso eC).left_inv x
  rw [← hmap]
  exact hfg'.map _
end ProductCriterion

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PartialResolutionPartialCyclesFg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PartialResolution
open _root_.CategoryTheory CategoryTheory.Limits ProductFiniteResolution ProductCriterion
open scoped MonoidAlgebra
variable {k G : Type} [CommRing k] [Group G]

lemma partial_cycles_fg (C : ChainComplex (Rep k G) ℕ) [∀ i, Projective (C.X i)]
    (N : ℕ) (hN : 0 < N) (ε : C.X 0 ⟶ Rep.trivial k G k) [Epi ε]
    (hε : C.d 1 0 ≫ ε = 0) (he₀ : (ShortComplex.mk (C.d 1 0) ε hε).Exact)
    (hex : ∀ i, 0 < i → i < N → C.ExactAt i)
    {α β : Type} [Finite α] (eC : C.X N ≅ Rep.free k G α)
    (eD : C.X (N-1) ≅ Rep.free k G β)
    (hzero : ∀ I : Type, IsZero (groupHomology (RegularProductR.rep k G I) N)) :
    (moduleMap (C.d N (N-1))).ker.FG := by
  let P := ProjectiveResolution.of (kerRep (C.d N (N-1)))
  let T := resolution C N P hN ε hε he₀ hex
  let f : T.complex.X (N+1) ⟶ C.X N :=
    T.complex.d (N+1) N ≫ (headIso C N P N le_rfl).hom
  have hc : f ≫ C.d N (N-1) = 0 := by
    change (complex C N P hN).d (N+1) N ≫
      (headIso C N P N le_rfl).hom ≫ C.d N (N-1) = 0
    erw [← complex_head_d C N P hN N (N-1) le_rfl (by omega),
      ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]
  apply kernel_fg_of_iso f (C.d N (N-1)) hc eC eD
  intro I
  have he := product_resolution_exact T N hzero I
  rw [HomologicalComplex.exactAt_iff' _ (N+1) N (N-1)
    (by apply ComplexShape.prev_eq'; rfl)
    (by apply ComplexShape.next_eq'; change _+1=N; omega)] at he
  let E : ShortComplex.mk (T.complex.d (N+1) N) (T.complex.d N (N-1))
      (T.complex.d_comp_d _ _ _) ≅ ShortComplex.mk f (C.d N (N-1)) hc :=
    ShortComplex.isoMk (Iso.refl _) (headIso C N P N le_rfl)
      (headIso C N P (N-1) (by omega)) (by simp [f])
      (complex_head_d C N P hN N (N-1) le_rfl (by omega)).symm
  exact (ShortComplex.exact_iff_of_iso
    ((((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I)).mapShortComplex).mapIso E)).mp he
end PartialResolution

namespace CWEquivariant
section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory HomologicalComplex ProductCriterion

attribute [instance] AddCommGroup.toIntModule
end

attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory HomologicalComplex ProductCriterion

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CategoryTheoryShortComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory
namespace CategoryTheory.ShortComplex
open scoped _root_.CategoryTheory _root_.CategoryTheory.ShortComplex
variable {R : Type*} [Ring R] {S T : _root_.CategoryTheory.ShortComplex (ModuleCat R)}

def concreteCyclesMap (φ : S ⟶ T) : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
    intro z
    change T.g (φ.τ₂ z.val) = 0
    have h := congrArg (fun q => q z.val) φ.comm₂₃
    change T.g (φ.τ₂ z.val) = φ.τ₃ (S.g z.val) at h
    rw [h,show S.g z.val=0 from z.property,map_zero])

lemma concreteCyclesMap_range (φ : S ⟶ T) :
    LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap (concreteCyclesMap φ) := by
  rintro z ⟨a,rfl⟩
  refine ⟨φ.τ₁ a,?_⟩
  apply Subtype.ext
  have h := congrArg (fun q => q a) φ.comm₁₂
  exact h

def concreteHomologyMap (φ : S ⟶ T) :
    S.moduleCatLeftHomologyData.H →ₗ[R] T.moduleCatLeftHomologyData.H :=
  (LinearMap.range S.moduleCatToCycles).mapQ (LinearMap.range T.moduleCatToCycles)
    (concreteCyclesMap φ) (concreteCyclesMap_range φ)

def concreteHomologyMapData (φ : S ⟶ T) :
    _root_.CategoryTheory.ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (concreteCyclesMap φ)
  φH := ModuleCat.ofHom (concreteHomologyMap φ)
  commi := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  commf' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact (congrArg (fun q => q z) φ.comm₁₂).symm
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl

end CategoryTheory.ShortComplex

open CategoryTheory

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

def root (i j : n) (h : i≠j) (a : R) : (Matrix n n R)ˣ where
  val := 1+Matrix.single i j a
  inv := 1+Matrix.single i j (-a)
  val_inv := by
    simp [add_mul,mul_add,Matrix.single_mul_single_of_ne _ _ _ _ h.symm,
      ← Matrix.single_neg,add_assoc]
  inv_val := by
    simp [add_mul,mul_add,Matrix.single_mul_single_of_ne _ _ _ _ h.symm,
      ← Matrix.single_neg,add_assoc]

@[simp] lemma root_val (i j : n) (h : i≠j) (a : R) :
    (root i j h a).val=1+Matrix.single i j a := rfl

end NoncommElementary

open scoped commutatorElement

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_Steinberg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace Steinberg
variable (n R : Type*) [Ring R]

structure Root where
  i : n
  j : n
  different : i≠j
  coefficient : R

def letter (i j : n) (h : i≠j) (a : R) : FreeGroup (Root n R) :=
  FreeGroup.of ⟨i,j,h,a⟩

inductive Relation : FreeGroup (Root n R) → Prop
  | add (i j : n) (h : i≠j) (a b : R) :
      Relation (letter n R i j h a*letter n R i j h b*(letter n R i j h (a+b))⁻¹)
  | chain (i j k : n) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
      Relation (⁅letter n R i j hij a,letter n R j k hjk b⁆*(letter n R i k hik (a*b))⁻¹)
  | away (i j k l : n) (hij : i≠j) (hkl : k≠l) (hil : i≠l) (hjk : j≠k) (a b : R) :
      Relation ⁅letter n R i j hij a,letter n R k l hkl b⁆

def relations : Set (FreeGroup (Root n R)) := Relation n R

abbrev Group := PresentedGroup (relations n R)

variable {n R}
def root (i j : n) (h : i≠j) (a : R) : Group n R := PresentedGroup.of ⟨i,j,h,a⟩

lemma root_add (i j : n) (h : i≠j) (a b : R) :
    root i j h a*root i j h b=root i j h (a+b) := by
  apply eq_of_mul_inv_eq_one
  have he := PresentedGroup.one_of_mem (rels:=relations n R) (Relation.add i j h a b)
  simpa only [map_mul,map_inv,letter,PresentedGroup.of,root] using he

lemma root_commutator (i j k : n) (hij : i≠j) (hjk : j≠k) (hik : i≠k)
    (a b : R) : ⁅root i j hij a,root j k hjk b⁆=root i k hik (a*b) := by
  apply eq_of_mul_inv_eq_one
  have he := PresentedGroup.one_of_mem (rels:=relations n R) (Relation.chain i j k hij hjk hik a b)
  simpa only [map_mul,map_inv,map_commutatorElement,letter,PresentedGroup.of,root] using he

lemma root_commute (i j k l : n) (hij : i≠j) (hkl : k≠l)
    (hil : i≠l) (hjk : j≠k) (a b : R) :
    Commute (root i j hij a) (root k l hkl b) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have he := PresentedGroup.one_of_mem (rels:=relations n R) (Relation.away i j k l hij hkl hil hjk a b)
  simpa only [map_commutatorElement,letter,PresentedGroup.of,root] using he

@[simp] lemma root_zero (i j : n) (h : i≠j) : root i j h (0:R)=1 := by
  have h0 := root_add i j h (0:R) 0
  simpa using h0

@[simp] lemma root_neg (i j : n) (h : i≠j) (a : R) :
    root i j h (-a)=(root i j h a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [root_add,neg_add_cancel,root_zero]

def lift {H : Type*} [_root_.Group H] (f : ∀ i j : n, i≠j → R → H)
    (ha : ∀ i j h a b, f i j h a*f i j h b=f i j h (a+b))
    (hc : ∀ i j k hij hjk hik a b, ⁅f i j hij a,f j k hjk b⁆=f i k hik (a*b))
    (hd : ∀ i j k l hij hkl, i≠l → j≠k → ∀ a b, Commute (f i j hij a) (f k l hkl b)) :
    Group n R →* H :=
  PresentedGroup.toGroup (rels:=relations n R) (f:=fun x : Root n R => f x.i x.j x.different x.coefficient) (by
    intro r hr
    cases (show Relation n R r from hr) with
    | add i j h a b => simp [letter,ha]
    | chain i j k hij hjk hik a b =>
      simp only [map_mul,map_inv,map_commutatorElement,letter,FreeGroup.lift_apply_of]
      rw [hc i j k hij hjk hik a b,mul_inv_cancel]
    | away i j k l hij hkl hil hjk a b =>
      simpa [letter] using (hd i j k l hij hkl hil hjk a b).commutator_eq)

@[simp] lemma lift_root {H : Type*} [_root_.Group H] (f : ∀ i j : n, i≠j → R → H)
    (ha hc hd) (i j : n) (h : i≠j) (a : R) :
    lift f ha hc hd (root i j h a)=f i j h a := PresentedGroup.toGroup.of _

@[ext] theorem hom_ext {H : Type*} [_root_.Group H] {f g : Group n R →* H}
    (h : ∀ i j hij a, f (root i j hij a)=g (root i j hij a)) : f=g := by
  apply PresentedGroup.ext
  intro x
  exact h x.i x.j x.different x.coefficient

def map {S : Type*} [Ring S] (φ : R →ₙ+* S) : Group n R →* Group n S :=
  lift (fun i j h a => root i j h (φ a))
    (by intros; rw [root_add,map_add])
    (by intros; rw [root_commutator,map_mul])
    (by intros; apply root_commute <;> assumption)

@[simp] lemma map_root {S : Type*} [Ring S] (φ : R →ₙ+* S) (i j : n) (h : i≠j) (a : R) :
    map φ (root i j h a)=root i j h (φ a) := by simpa only [map,root,lift] using (PresentedGroup.toGroup.of (rels:=relations n R) (x:=⟨i,j,h,a⟩) _)

end Steinberg

namespace CompressedSplittings
variable {R : Type*} [Ring R] (φ : R →ₙ+* R)

structure BinaryData where
  s : Fin 2 → R
  d : Fin 2 → R
  s_left : ∀ i, φ 1*s i=s i
  s_right : ∀ i, s i*φ 1=s i
  d_left : ∀ i, φ 1*d i=d i
  d_right : ∀ i, d i*φ 1=d i
  s_commute : ∀ i x, Commute (s i) (φ x)
  d_commute : ∀ i x, Commute (d i) (φ x)
  ds : ∀ i j, d i*s j=if i=j then φ 1 else 0
  partition : s 0*d 0+s 1*d 1=φ 1
end CompressedSplittings

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RingExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace RingExchange
variable {R : Type*} [Ring R]

structure Data (R : Type*) [Ring R] where
  E : R
  F : R
  a : R
  b : R
  EF : E*F=0
  FE : F*E=0
  aE : a*E=a
  Fa : F*a=a
  bF : b*F=b
  Eb : E*b=b
  ab : a*b=F
  ba : b*a=E

namespace Data
variable (D : Data R)
lemma Ea : D.E*D.a=0 := by rw [← D.Fa,← mul_assoc,D.EF,zero_mul]
lemma aF : D.a*D.F=0 := by rw [← D.aE,mul_assoc,D.EF,mul_zero]
lemma Fb : D.F*D.b=0 := by rw [← D.Eb,← mul_assoc,D.FE,zero_mul]
lemma bE : D.b*D.E=0 := by rw [← D.bF,mul_assoc,D.FE,mul_zero]
lemma aa : D.a*D.a=0 := by
  calc D.a*D.a=(D.a*D.E)*D.a := by rw [D.aE]
       _ = 0 := by rw [mul_assoc,D.Ea,mul_zero]
lemma bb : D.b*D.b=0 := by
  calc D.b*D.b=(D.b*D.F)*D.b := by rw [D.bF]
       _ = 0 := by rw [mul_assoc,D.Fb,mul_zero]
lemma EE : D.E*D.E=D.E := by
  calc D.E*D.E=(D.b*D.a)*D.E := by rw [D.ba]
       _ = D.E := by rw [mul_assoc,D.aE,D.ba]
lemma FF : D.F*D.F=D.F := by
  calc D.F*D.F=(D.a*D.b)*D.F := by rw [D.ab]
       _ = D.F := by rw [mul_assoc,D.bF,D.ab]

def value : R := 1-D.E-D.F+D.a+D.b

lemma square : D.value*D.value=1 := by
  simp only [value,add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,
    D.EE,D.FF,D.EF,D.FE,D.Ea,D.aE,D.Fa,D.aF,D.Eb,D.bE,D.Fb,D.bF,D.aa,D.bb,D.ab,D.ba]
  abel

lemma value_E : D.value*D.E=D.a := by
  simp only [value,add_mul,sub_mul,one_mul,D.EE,D.FE,D.aE,D.bE]
  abel
lemma a_value : D.a*D.value=D.F := by
  simp only [value,mul_add,mul_sub,mul_one,D.aE,D.aF,D.aa,D.ab]
  abel

def unit : Rˣ := ⟨D.value,D.value,D.square,D.square⟩

lemma conjugates : D.unit.val*D.E*D.unit.inv=D.F := by
  change D.value*D.E*D.value=D.F
  rw [D.value_E,D.a_value]

lemma commutes {x : R} (hE : Commute D.E x) (hF : Commute D.F x)
    (ha : Commute D.a x) (hb : Commute D.b x) : Commute D.unit.val x :=
  (((Commute.one_left x).sub_left hE).sub_left hF).add_left ha |>.add_left hb
end Data

def ofPairs (p s d t e : R)
    (hpd : p*d=d) (hpe : p*e=e)
    (hds : d*s=p) (het : e*t=p) (hdt : d*t=0) (hes : e*s=0) : Data R where
  E := s*d
  F := t*e
  a := t*d
  b := s*e
  EF := by rw [mul_assoc,← mul_assoc d,hdt,zero_mul,mul_zero]
  FE := by rw [mul_assoc,← mul_assoc e,hes,zero_mul,mul_zero]
  aE := by rw [mul_assoc,← mul_assoc d,hds,hpd]
  Fa := by rw [mul_assoc,← mul_assoc e,het,hpd]
  bF := by rw [mul_assoc,← mul_assoc e,het,hpe]
  Eb := by rw [mul_assoc,← mul_assoc d,hds,hpe]
  ab := by rw [mul_assoc,← mul_assoc d,hds,hpe]
  ba := by rw [mul_assoc,← mul_assoc e,het,hpd]

end RingExchange

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CompressedSplittings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace CompressedSplittings
section
variable {R : Type*} [Ring R] (φ : R →ₙ+* R)

structure Idempotent where
  val : R
  idem : val*val=val
  commute : ∀ x, Commute val (φ x)

namespace Idempotent
@[ext] lemma ext {E F : Idempotent φ} (h : E.val=F.val) : E=F := by
  cases E; cases F; cases h; rfl

variable {φ}

def coefficient (E : Idempotent φ) : R →ₙ+* R where
  toFun x := φ x*E.val
  map_zero' := by simp
  map_add' x y := by simp [add_mul]
  map_mul' x y := by
    change φ (x*y)*E.val=(φ x*E.val)*(φ y*E.val)
    rw [map_mul,mul_assoc,mul_assoc,← mul_assoc E.val (φ y),E.commute y |>.eq,
      mul_assoc (φ y), E.idem]

end Idempotent

end

variable {R : Type*} [Ring R] (φ : R →ₙ+* R)

namespace BinaryData
variable {φ} (D : BinaryData φ)
@[simp] lemma ds_same (i : Fin 2) : D.d i*D.s i=φ 1 := by simp [D.ds]
lemma ds_cross (i j : Fin 2) (h : i≠j) : D.d i*D.s j=0 := by simp [D.ds,h]

lemma dd_ss (i j : Fin 2) : (D.d j*D.d i)*(D.s i*D.s j)=φ 1 := by
  rw [mul_assoc,← mul_assoc (D.d i),D.ds_same,← mul_assoc,D.d_right,D.ds_same]

def firstExchange : RingExchange.Data R :=
  RingExchange.ofPairs (φ 1) (D.s 0) (D.d 0) (D.s 1) (D.d 1)
    (D.d_left 0) (D.d_left 1) (D.ds_same 0) (D.ds_same 1)
    (D.ds_cross 0 1 (by decide)) (D.ds_cross 1 0 (by decide))

def secondExchange (j : Fin 2) : RingExchange.Data R :=
  RingExchange.ofPairs (φ 1) (D.s 0*D.s j) (D.d j*D.d 0) (D.s 1) (D.d 1)
    (by rw [← mul_assoc,D.d_left]) (D.d_left 1) (D.dd_ss 0 j) (D.ds_same 1)
    (by rw [mul_assoc,D.ds_cross 0 1 (by decide),mul_zero])
    (by rw [← mul_assoc,D.ds_cross 1 0 (by decide),zero_mul])

lemma firstExchange_commutes (x : R) : Commute D.firstExchange.unit.val (φ x) := by
  apply RingExchange.Data.commutes
  · exact (D.s_commute 0 x).mul_left (D.d_commute 0 x)
  · exact (D.s_commute 1 x).mul_left (D.d_commute 1 x)
  · exact (D.s_commute 1 x).mul_left (D.d_commute 0 x)
  · exact (D.s_commute 0 x).mul_left (D.d_commute 1 x)

lemma secondExchange_commutes (i : Fin 2) (x : R) :
    Commute (D.secondExchange i).unit.val (φ x) := by
  apply RingExchange.Data.commutes
  · exact ((D.s_commute 0 x).mul_left (D.s_commute i x)).mul_left
      ((D.d_commute i x).mul_left (D.d_commute 0 x))
  · exact (D.s_commute 1 x).mul_left (D.d_commute 1 x)
  · exact (D.s_commute 1 x).mul_left ((D.d_commute i x).mul_left (D.d_commute 0 x))
  · exact ((D.s_commute 0 x).mul_left (D.s_commute i x)).mul_left (D.d_commute 1 x)

end BinaryData
end CompressedSplittings

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace CWUniverse
open Set Metric Topology
universe u
variable {X : Type} [TopologicalSpace X] [CWComplex (univ : Set X)]

def chart {A : Type} (p : PartialEquiv A X) : PartialEquiv A (ULift.{u} X) where
  toFun a := ⟨p a⟩
  invFun x := p.symm x.down
  source := p.source
  target := ULift.down ⁻¹' p.target
  map_source' _ h := p.map_source h
  map_target' _ h := p.map_target h
  left_inv' _ h := p.left_inv h
  right_inv' _ h := ULift.ext _ _ (p.right_inv h)

omit [TopologicalSpace X] [CWComplex (univ : Set X)] in
lemma chart_image [TopologicalSpace X] [CWComplex (univ : Set X)]
    {A : Type} (p : PartialEquiv A X) (s : Set A) :
    chart.{u} p '' s = ULift.up '' (p '' s) := by
  rw [Set.image_image]; rfl

omit [CWComplex (univ : Set X)] in
lemma chart_continuous [CWComplex (univ : Set X)]
    {A : Type} [TopologicalSpace A] (p : PartialEquiv A X)
    (s : Set A) (h : ContinuousOn p s) : ContinuousOn (chart.{u} p) s :=
  Homeomorph.ulift.symm.continuous.comp_continuousOn h

omit [CWComplex (univ : Set X)] in
lemma chart_symm_continuous [CWComplex (univ : Set X)]
    {A : Type} [TopologicalSpace A] (p : PartialEquiv A X)
    (h : ContinuousOn p.symm p.target) :
    ContinuousOn (chart.{u} p).symm (chart.{u} p).target :=
  h.comp Homeomorph.ulift.continuous.continuousOn (fun _ hx => hx)

@[instance_reducible] def cw : CWComplex (univ : Set (ULift.{u} X)) where
  cell n := ULift.{u} (Topology.CWComplex.cell (univ : Set X) n)
  map n i := chart (Topology.CWComplex.map n i.down)
  source_eq n i := Topology.CWComplex.source_eq n i.down
  continuousOn n i := chart_continuous _ _ (Topology.CWComplex.continuousOn n i.down)
  continuousOn_symm n i := chart_symm_continuous _ (Topology.CWComplex.continuousOn_symm n i.down)
  pairwiseDisjoint' := by
    rintro ⟨n,⟨i⟩⟩ _ ⟨m,⟨j⟩⟩ _ hij
    have hne : (⟨n,i⟩ : Σ n, Topology.CWComplex.cell (univ : Set X) n) ≠ ⟨m,j⟩ := by
      intro h
      cases h
      exact hij rfl
    have hd := @Topology.CWComplex.pairwiseDisjoint' X _ (univ : Set X) _
      ⟨n,i⟩ (mem_univ _) ⟨m,j⟩ (mem_univ _) hne
    apply Set.disjoint_left.mpr
    rintro z ⟨a,ha,he⟩ ⟨b,hb,hf⟩
    exact Set.disjoint_left.mp hd ⟨a,ha,congrArg ULift.down he⟩ ⟨b,hb,congrArg ULift.down hf⟩
  mapsTo' n i := by
    classical
    obtain ⟨I,hI⟩ := Topology.CWComplex.mapsTo' n i.down
    refine ⟨fun m => (I m).map ⟨ULift.up,ULift.up_injective⟩,?_⟩
    intro a ha
    have hh := hI ha
    simp only [Set.mem_iUnion,Set.mem_image] at hh ⊢
    obtain ⟨m,hm,j,hj,b,hb,hba⟩ := hh
    refine ⟨m,hm,⟨j⟩,Finset.mem_map.mpr ⟨j,hj,rfl⟩,b,hb,?_⟩
    exact congrArg ULift.up hba
  closed' A _ hA := by
    have h : IsClosed (ULift.up ⁻¹' A : Set X) := by
      apply Topology.CWComplex.closed' _ (subset_univ _)
      intro n i
      have h' := (hA n ⟨i⟩).preimage Homeomorph.ulift.symm.continuous
      change IsClosed (ULift.up ⁻¹' (A ∩ chart.{u} (Topology.CWComplex.map n i) '' closedBall 0 1)) at h'
      simpa only [chart_image,Set.preimage_inter,Set.preimage_image_eq _ ULift.up_injective] using h'
    have h' := Homeomorph.ulift.symm.isClosedMap _ h
    change IsClosed (ULift.up '' (ULift.up ⁻¹' A) : Set (ULift.{u} X)) at h'
    rwa [Set.image_preimage_eq _ ULift.up_surjective] at h'
  union' := by
    apply Set.Subset.antisymm (subset_univ _)
    rintro ⟨x⟩ _
    have hx : x ∈ ⋃ n, ⋃ i : Topology.CWComplex.cell (univ : Set X) n,
        Topology.CWComplex.map n i '' closedBall 0 1 := by rw [Topology.CWComplex.union']; trivial
    simp only [Set.mem_iUnion,Set.mem_image] at hx ⊢
    obtain ⟨n,i,a,ha,rfl⟩ := hx
    exact ⟨n,⟨i⟩,a,ha,rfl⟩
end CWUniverse

namespace CWUniverse
open Set Topology
universe u
variable {X : Type} [TopologicalSpace X] [CWComplex (univ : Set X)]

variable (x : X)
def piOne : FundamentalGroup X x ≃* FundamentalGroup (ULift.{u} X) (ULift.up x) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (Homeomorph.ulift (X:=X)).symm.toHomotopyEquiv
  let f := FundamentalGroup.map (⟨ULift.up,Homeomorph.ulift.symm.continuous⟩ : C(X,ULift.{u} X)) x
  exact { e.fullyFaithfulFunctor.homEquiv (X:=FundamentalGroupoid.mk x)
           (Y:=FundamentalGroupoid.mk x) with
    map_mul' := f.map_mul }
end CWUniverse

end
end

end OAI
end


