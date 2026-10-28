-- Prove2me | Definitions.Def_OAIQ031A073
-- name    : OAIQ031A073
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:18:33.675483+00:00
-- url     : https://prove2.me/theorems/b5cdf790-d878-461d-8d69-d5235d8dde99
-- title:
--   Definitions bundle OAIQ031A073 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 4 definitions and 10 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.envelopingSemilinear`, `OAI.ArExplicit.TwistedBimodule.tensorUntwistMap`, `OAI.ArExplicit.VectorCochain.homologyCoordinates`, `OAI.ArExplicit.VectorCochain.totalTermCoordinates`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_ConeConnectingCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeConnectingCoordinates.lean), [`AuslanderReiten_Homology_VectorCochainKunnethMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorCochainKunnethMap.lean), [`AuslanderReiten_Tensor_ExternalEnveloping`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalEnveloping.lean), [`AuslanderReiten_Tensor_ExternalTensorComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorComplex.lean), [`AuslanderReiten_Tensor_ExternalTensorDegreeZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorDegreeZero.lean), [`AuslanderReiten_Tensor_ExternalTensorHomPairTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHomPairTransport.lean), [`AuslanderReiten_Tensor_ExternalTensorTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorTransport.lean), [`AuslanderReiten_Tensor_TwistedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensor.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A046`, `OAIQ031A047`, `OAIQ031A048`, `OAIQ031A049`, `OAIQ031A051`, `OAIQ031A052`, `OAIQ031A056` and `OAIQ031A057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A086` and `OAIQ031A087`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A046
import Definitions.Def_OAIQ031A047
import Definitions.Def_OAIQ031A048
import Definitions.Def_OAIQ031A049
import Definitions.Def_OAIQ031A051
import Definitions.Def_OAIQ031A052
import Definitions.Def_OAIQ031A056
import Definitions.Def_OAIQ031A057

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeConnectingCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable (H : CochainComplex (ModuleCat.{u} R) ℤ)

variable {H} {F G : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (κ : H ⟶ mappingCone φ)

variable (hi : Function.Injective (cochainCokernelMap φ))

theorem coneLiftKernel_square :
    (cochainCokernelMap φ).comp (coneLiftKernel φ κ hi) =
      (coneLiftMiddle φ κ).comp (rawSyzygyInclusion H) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (H.d (-2) (-1)).hom) z
  exact DFunLike.congr_fun (coneLiftKernelComponent_square φ κ) z

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

variable [Module.Finite k A] [Module.Finite k B]
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Finite B (Q.X n)]

theorem term_finite (n : ℕ) : Module.Finite (A ⊗[k] B) ((complex k A B P Q).X n) := by
  let (index : ℕ) : Module.Finite k (P.X index) := Module.Finite.trans A (P.X index)
  let (index : ℕ) : Module.Finite k (Q.X index) := Module.Finite.trans B (Q.X index)
  let (index : Diagonal n) : Module.Finite (A ⊗[k] B) (summands k A B P Q n index) :=
    Module.Finite.of_restrictScalars_finite k (A ⊗[k] B) _
  exact Module.Finite.equiv (termPiEquiv k A B P Q n).symm

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainKunnethMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.VectorCochain
universe u
variable (k : Type u) [Field k]
local notation "T" => MonoidalCategory.curriedTensor (ModuleCat k)
variable (P Q : CochainComplex (ModuleCat.{u} k) ℕ)

def totalTermCoordinates (n : ℕ) :
    (mapBifunctor P Q T (.up ℕ)).X n ≃ₗ[k]
      (∀ p : Diagonal n, P.X p.val.1 ⊗[k] Q.X p.val.2) :=
  (ModuleCat.coprodIsoDirectSum (fun p : Diagonal n =>
    ((T).obj (P.X p.val.1)).obj (Q.X p.val.2))).toLinearEquiv.trans
      DFinsupp.linearEquivFunOnFintype

theorem totalTermCoordinates_inclusion (i j n : ℕ) (h : i+j=n)
    (x : P.X i ⊗[k] Q.X j) :
    totalTermCoordinates k P Q n ((ιMapBifunctor P Q T (.up ℕ) i j n h).hom x) =
      Pi.single ⟨(i,j),h⟩ x := by
  have hi := ModuleCat.ι_coprodIsoDirectSum_hom
    (fun p : Diagonal n => ((T).obj (P.X p.val.1)).obj (Q.X p.val.2)) ⟨(i,j),h⟩
  exact congrArg (fun y => DFinsupp.linearEquivFunOnFintype (R := k) y)
    (congrArg (fun f => f.hom x) hi)

variable {P Q} {P' Q' : CochainComplex (ModuleCat.{u} k) ℕ}

theorem totalTermCoordinates_natural (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ)
    (x : (mapBifunctor P Q T (.up ℕ)).X n) :
    totalTermCoordinates k P' Q' n (((mapBifunctorMap f g T (.up ℕ)).f n).hom x) =
      diagonalTermMap k f g n (totalTermCoordinates k P Q n x) := by
  have hh : (mapBifunctorMap f g T (.up ℕ)).f n ≫
      ModuleCat.ofHom (totalTermCoordinates k P' Q' n).toLinearMap =
    ModuleCat.ofHom ((diagonalTermMap k f g n).comp
      (totalTermCoordinates k P Q n).toLinearMap) := by
    apply mapBifunctor.hom_ext
    intro i j hij
    erw [← Category.assoc, ι_mapBifunctorMap]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change totalTermCoordinates k P' Q' n
      ((ιMapBifunctor P' Q' T (.up ℕ) i j n hij).hom
        (TensorProduct.map LinearMap.id (g.f j).hom
          (TensorProduct.map (f.f i).hom LinearMap.id z))) =
      diagonalTermMap k f g n (totalTermCoordinates k P Q n
        ((ιMapBifunctor P Q T (.up ℕ) i j n hij).hom z))
    rw [TensorProduct.map_map]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    rw [totalTermCoordinates_inclusion, totalTermCoordinates_inclusion,
      diagonalTermMap_single]
  exact congrArg (fun a => a.hom x) hh

def homologyCoordinates (n : ℕ) :
    (mapBifunctor P Q T (.up ℕ)).homology n ≃ₗ[k]
      (∀ p : Diagonal n, P.homology p.val.1 ⊗[k] Q.homology p.val.2) :=
  (kunnethIso k T P Q n).toLinearEquiv.trans
    (totalTermCoordinates k (gradedHomology k P) (gradedHomology k Q) n)

theorem homologyCoordinates_natural (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ)
    (x : (mapBifunctor P Q T (.up ℕ)).homology n) :
    homologyCoordinates k n ((homologyMap (mapBifunctorMap f g T (.up ℕ)) n).hom x) =
      diagonalTermMap k (gradedMap k f) (gradedMap k g) n (homologyCoordinates k n x) := by
  have hn := congrArg (fun a => a.hom x) (kunnethIso_natural k T f g n)
  change (kunnethIso k T P' Q' n).hom.hom
      ((homologyMap (mapBifunctorMap f g T (.up ℕ)) n).hom x) =
    ((mapBifunctorMap (gradedMap k f) (gradedMap k g) T (.up ℕ)).f n).hom
      ((kunnethIso k T P Q n).hom.hom x) at hn
  change totalTermCoordinates k (gradedHomology k P') (gradedHomology k Q') n
    ((kunnethIso k T P' Q' n).hom.hom
      ((homologyMap (mapBifunctorMap f g T (.up ℕ)) n).hom x)) = _
  rw [hn]
  exact totalTermCoordinates_natural k (gradedMap k f) (gradedMap k g) n _

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalEnveloping
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def envelopingSemilinear (M : ModuleCat.{u} (ProductEnveloping k A B)) :
    LinearEquiv (envelopingEquiv k A B).toRingHom
      (σ' := (envelopingEquiv k A B).symm.toRingHom) M (envelopingObject k A B M) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change a • x = ((envelopingEquiv k A B).symm ((envelopingEquiv k A B) a)) • x
    rw [AlgEquiv.symm_apply_apply]

theorem enveloping_projective (M : ModuleCat.{u} (ProductEnveloping k A B))
    [Module.Projective (ProductEnveloping k A B) M] :
    Module.Projective (EnvelopingProduct k A B) (envelopingObject k A B M) :=
  Module.Projective.of_equiv (envelopingSemilinear k A B M)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorDegreeZero
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

theorem bottomProjection_zero_injective : Function.Injective (bottomProjection k A B P Q 0) := by
  intro x y h
  apply (termDirectSumEquiv k A B P Q 0).injective
  apply DFinsupp.ext
  intro ij
  obtain ⟨⟨i,j⟩,hij⟩ := ij
  have hi : i = 0 := by omega
  have hj : j = 0 := by omega
  subst i; subst j
  exact h

theorem bottomInsert_projection_zero (x : (complex k A B P Q).X 0) :
    cubicInsert k A B P Q 0 ⟨(0,0),rfl⟩ (bottomProjection k A B P Q 0 x) = x := by
  apply bottomProjection_zero_injective k A B P Q
  exact bottomProjection_bottom k A B P Q 0 _

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomPairTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable {M N U V : Type u}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup U] [AddCommGroup V]
variable [Module k M] [Module k N] [Module k U] [Module k V]
variable [Module A M] [Module B N] [Module A U] [Module B V]
variable [IsScalarTower k A M] [IsScalarTower k B N] [IsScalarTower k A U] [IsScalarTower k B V]
variable (a : M →ₗ[k] M) (b : N →ₗ[k] N) (e : U ≃ₗ[k] U) (f : V ≃ₗ[k] V)
variable (α : (M →ₗ[A] U) →ₗ[k] (M →ₗ[A] U))
variable (β : (N →ₗ[B] V) →ₗ[k] (N →ₗ[B] V))
variable (hα : ∀ c x, α c x = e.symm (c (a x)))
variable (hβ : ∀ d y, β d y = f.symm (d (b y)))
include hα hβ

theorem homMap_transport (c : (M →ₗ[A] U) ⊗[k] (N →ₗ[B] V))
    (z : moduleObject k A B M N) :
    homMap k A B (TensorProduct.map α β c) z =
      (TensorProduct.congr e f).symm (homMap k A B c (TensorProduct.map a b z)) := by
  induction c using OAI.tensorInductionOn with
  | add c d hc hd =>
    erw [map_add, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, map_add]
    rw [hc, hd]
    rfl
  | tmul c d =>
    induction z using OAI.tensorInductionOn with
    | add x y hx hy =>
      erw [map_add, map_add, map_add, map_add]
      rw [hx, hy]
      rfl
    | tmul x y =>
      simp only [TensorProduct.map_tmul, homMap_tmul, map_tmul,
        TensorProduct.congr_symm, TensorProduct.congr_tmul, hα, hβ]
      rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (h : A ≃ₐ[k] A) (j : B ≃ₐ[k] B)

local notation "F" => tensorRestriction k A B h j

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (e : ∀ n, P.X n →ₗ[k] P.X n) (f : ∀ n, Q.X n →ₗ[k] Q.X n)
variable (he : ∀ n a x, e n (a • x) = h a • e n x)
variable (hf : ∀ n b x, f n (b • x) = j b • f n x)

variable (hdP : ∀ n x, (P.d (n+1) n).hom (e (n+1) x) = e n ((P.d (n+1) n).hom x))
variable (hdQ : ∀ n x, (Q.d (n+1) n).hom (f (n+1) x) = f n ((Q.d (n+1) n).hom x))

include hdP in
theorem horizontal_transport (i j' n : ℕ) (hij : i+j'=n+1) :
    horizontal k A B P Q i j' n ≫ transportTerm k A B h j P Q e f he hf n =
      transportSummand k A B h j P Q e f he hf i j' ≫
        (F).map (horizontal k A B P Q i j' n) := by
  cases i with
  | zero => simp only [horizontal_zero, Functor.map_zero, zero_comp, comp_zero]
  | succ i =>
    have hi : i+j'=n := by omega
    rw [horizontal_succ k A B P Q i j' n hi, Category.assoc,
      inclusion_transportTerm, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    apply congrArg (fun t => t ≫ (F).map (inclusion k A B P Q i j' n hi))
    exact (tensorSemilinear_natural k A B h j (e (i+1)) (e i) (f j') (f j')
      (he (i+1)) (he i) (hf j') (hf j') (P.d (i+1) i) (𝟙 (Q.X j'))
      (hdP i) (fun _ => rfl)).symm

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedBimodule

variable {k R M : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]
variable (σ : R ≃ₐ[k] R)

def tensorUntwistMap : BalancedTensor k R (TwistedBimodule k R σ) M →ₗ[R]
    TwistedLeftModule k R σ M :=
  BalancedTensor.liftLeft (untwistBilinear σ) (untwist_balanced σ) (untwist_left σ)

end TwistedBimodule
end ArExplicit

end OAI
end


