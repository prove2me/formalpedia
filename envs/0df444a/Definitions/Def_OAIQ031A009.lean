-- Prove2me | Definitions.Def_OAIQ031A009
-- name    : OAIQ031A009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:00:01.570014+00:00
-- url     : https://prove2.me/theorems/b8998652-691c-4a74-b3dc-50d8d3d9814c
-- title:
--   Definitions bundle OAIQ031A009 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 20 definitions, 1 inductive type or structure, 5 instances and 15 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.leftAction`, `OAI.ArExplicit.BalancedTensor.rightAction`, `OAI.ArExplicit.CompleteComparison.shiftedCocycleHom`, `OAI.ArExplicit.DualTensor.coefficientRight`, `OAI.ArExplicit.DualTensor.precomposeRight`, `OAI.ArExplicit.ResolutionProducts.natCubicCochain`, `OAI.ArExplicit.RightDual`, `OAI.ArExplicit.RightDual.congr`, `OAI.ArExplicit.RightDual.coordinates`, `OAI.ArExplicit.RightDual.map`, `OAI.ArExplicit.RightDual.scalarEquiv`, `OAI.ArExplicit.RightDualHomology.DualHomology`, `OAI.ArExplicit.RightDualHomology.Homology`, `OAI.ArExplicit.RightDualHomology.boundaries`, `OAI.ArExplicit.RightDualHomology.cycleMap`, `OAI.ArExplicit.RightDualHomology.cyclesToDualHomology`, `OAI.ArExplicit.RightDualHomology.dualBoundaries`, `OAI.ArExplicit.RightDualHomology.dualCycleMap`, `OAI.ArExplicit.RightDualHomology.dualHomologyEquiv`, `OAI.ArExplicit.TrivialExtension.inlHom`, `OAI.ArExplicit.leftTensorIdeal`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_TensorRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorRadical.lean), [`AuslanderReiten_Algebras_TrivialExtension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TrivialExtension.lean), [`AuslanderReiten_Duality_DualTensorEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualTensorEvaluation.lean), [`AuslanderReiten_Duality_DualTensorModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualTensorModule.lean), [`AuslanderReiten_Duality_RightDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/RightDual.lean), [`AuslanderReiten_Duality_RightDualHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/RightDualHomology.lean), [`AuslanderReiten_HomComplex_FullHomProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomProducts.lean), [`AuslanderReiten_Homology_ConcentratedNatDerived`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ConcentratedNatDerived.lean), [`AuslanderReiten_Resolutions_NatResolutionCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/NatResolutionCubic.lean), [`AuslanderReiten_Tensor_BalancedTensorProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorProjective.lean), [`AuslanderReiten_Tensor_BalancedTensorUnit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorUnit.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A032`, `OAIQ031A033`, `OAIQ031A034` and `OAIQ031A040`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A000

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def leftTensorIdeal (I : Ideal R) : Ideal (R ⊗[k] S) :=
  I.map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S)

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TrivialExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

namespace TrivialExtension

variable {k A}

def inlHom : A →ₐ[k] TrivialExtension k A where
  toFun := inl
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    apply TrivialExtension.ext
    · rfl
    · ext d; simp [inl]
  map_mul' a b := by
    apply TrivialExtension.ext
    · rfl
    · ext d; simp [inl]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    apply TrivialExtension.ext
    · rfl
    · ext d; simp [inl]

end TrivialExtension

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BalancedTensor

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

section Left

variable {M : Type*} [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M]

def leftAction : R →ₗ[k] M →ₗ[k] M where
  toFun r :=
    { toFun := fun m => r • m
      map_add' := smul_add r
      map_smul' := fun c m => smul_comm r c m }
  map_add' r s := by ext m; exact add_smul r s m
  map_smul' c r := by ext m; exact smul_assoc c r m

end Left

section Right

variable {F : Type*} [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F]

def rightAction : F →ₗ[k] R →ₗ[k] F where
  toFun f :=
    { toFun := fun r => MulOpposite.op r • f
      map_add' r s := by simp [add_smul]
      map_smul' c r := by simp [MulOpposite.op_smul, smul_assoc] }
  map_add' f g := by ext r; exact smul_add _ _ _
  map_smul' c f := by ext r; exact smul_comm _ _ _

end Right

end ArExplicit.BalancedTensor

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

instance finitePiProjective {S P ι : Type*} [Ring S] [AddCommGroup P]
    [Module S P] [Module.Projective S P] [Fintype ι] : Module.Projective S (ι → P) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype :
    (Π₀ _ : ι, P) ≃ₗ[S] (ι → P))

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
namespace DualTensor

variable {k R V W : Type*} [CommRing k] [Ring R] [Algebra k R]
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
  [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower k R W]

variable {n : ℕ}

def coefficientRight (s : V →ₗ[R] (Fin n → R)) (i : Fin n) : R →ₗ[k] (V →ₗ[R] R) where
  toFun r :=
    { toFun v := s v i * r
      map_add' v w := by simp [add_mul]
      map_smul' a v := by simp [mul_assoc] }
  map_add' r t := by ext v; simp [mul_add]
  map_smul' a r := by ext v; simp

omit [Module k V] [IsScalarTower k R V] in
@[simp] theorem coefficientRight_apply (s : V →ₗ[R] (Fin n → R)) (i : Fin n) (r : R) (v : V) :
    coefficientRight (k := k) s i r v = s v i * r := rfl

theorem sum_coefficients (s : V →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] V)
    (h : p.comp s = LinearMap.id) (v : V) :
    (∑ i, s v i • p (Pi.single i 1)) = v := by
  calc
    _ = ∑ i, p (Pi.single i (s v i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← p.map_smul]
      congr 1
      ext j
      by_cases hij : j = i
      · subst j; simp
      · simp [hij]
    _ = p (s v) := by rw [← map_sum, Finset.univ_sum_single]
    _ = v := LinearMap.congr_fun h v

omit [Module k V] [IsScalarTower k R V] in
theorem sum_coefficientRight (s : V →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] V)
    (h : p.comp s = LinearMap.id) (f : V →ₗ[R] R) :
    (∑ i, coefficientRight (k := k) s i (f (p (Pi.single i 1)))) = f := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sum_apply, coefficientRight_apply]
  simpa only [map_sum, map_smul, smul_eq_mul] using congrArg f (sum_coefficients s p h v)

end DualTensor
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_RightDual
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

@[ext] structure RightDual (k R V : Type*) [CommRing k] [Ring R]
    [AddCommGroup V] [Module k V] [Module Rᵐᵒᵖ V] where
  functional : Module.Dual k V

namespace RightDual
variable {k R V W U : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup V] [Module k V] [Module Rᵐᵒᵖ V] [IsScalarTower k Rᵐᵒᵖ V]
variable [AddCommGroup W] [Module k W] [Module Rᵐᵒᵖ W] [IsScalarTower k Rᵐᵒᵖ W]
variable [AddCommGroup U] [Module k U] [Module Rᵐᵒᵖ U] [IsScalarTower k Rᵐᵒᵖ U]

def coordinates : RightDual k R V ≃ Module.Dual k V where
  toFun := functional
  invFun := RightDual.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (RightDual k R V) := coordinates.addCommGroup
instance instModule : Module k (RightDual k R V) := coordinates.addEquiv.module k

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ V] in
@[simp] theorem functional_zero : (0 : RightDual k R V).functional = 0 := rfl
omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ V] in
@[simp] theorem functional_add (φ ψ : RightDual k R V) :
    (φ + ψ).functional = φ.functional + ψ.functional := rfl
omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ V] in
@[simp] theorem functional_smul (a : k) (φ : RightDual k R V) :
    (a • φ).functional = a • φ.functional := rfl

def scalarEquiv : RightDual k R V ≃ₗ[k] Module.Dual k V :=
  coordinates.addEquiv.linearEquiv k

instance instSMul : SMul R (RightDual k R V) :=
  ⟨fun r φ => ⟨{
    toFun := fun v => φ.functional (MulOpposite.op r • v)
    map_add' := fun v w => by simp
    map_smul' := fun a v => by simp [smul_comm (MulOpposite.op r) a v] }⟩⟩

@[simp] theorem functional_action (r : R) (φ : RightDual k R V) (v : V) :
    (r • φ).functional v = φ.functional (MulOpposite.op r • v) := rfl

instance instModule_1 : Module R (RightDual k R V) where
  one_smul φ := by ext v; simp
  mul_smul r s φ := by ext v; simp [MulOpposite.op_mul, mul_smul]
  smul_zero r := by ext v; simp
  smul_add r φ ψ := by ext v; simp
  zero_smul φ := by ext v; simp
  add_smul r s φ := by ext v; simp [add_smul]

def map (f : V →ₗ[Rᵐᵒᵖ] W) : RightDual k R W →ₗ[R] RightDual k R V where
  toFun φ := ⟨φ.functional.comp (f.restrictScalars k)⟩
  map_add' φ ψ := by ext v; rfl
  map_smul' r φ := by ext v; simp

@[simp] theorem map_apply (f : V →ₗ[Rᵐᵒᵖ] W) (φ : RightDual k R W) (v : V) :
    (map f φ).functional v = φ.functional (f v) := rfl

def congr (e : V ≃ₗ[Rᵐᵒᵖ] W) : RightDual k R W ≃ₗ[R] RightDual k R V where
  __ := map e.toLinearMap
  invFun := map e.symm.toLinearMap
  left_inv φ := by ext w; simp
  right_inv φ := by ext v; simp

end RightDual

namespace RightDual
variable {k R U V W : Type*} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup U] [Module k U] [Module Rᵐᵒᵖ U] [IsScalarTower k Rᵐᵒᵖ U]
variable [AddCommGroup V] [Module k V] [Module Rᵐᵒᵖ V] [IsScalarTower k Rᵐᵒᵖ V]
variable [AddCommGroup W] [Module k W] [Module Rᵐᵒᵖ W] [IsScalarTower k Rᵐᵒᵖ W]

theorem map_exact (f : U →ₗ[Rᵐᵒᵖ] V) (g : V →ₗ[Rᵐᵒᵖ] W) (h : Function.Exact f g) :
    Function.Exact (map (k := k) g) (map f) := by
  intro φ
  constructor
  · intro hφ
    have ha : φ.functional ∈ (LinearMap.ker (g.restrictScalars k)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      obtain ⟨u, rfl⟩ := (h v).mp hv
      exact congrArg (fun ψ : RightDual k R U => ψ.functional u) hφ
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at ha
    obtain ⟨ψ, hψ⟩ := ha
    exact ⟨⟨ψ⟩, RightDual.ext hψ⟩
  · rintro ⟨ψ, rfl⟩
    ext u
    change ψ.functional (g (f u)) = 0
    rw [(h (f u)).mpr ⟨u, rfl⟩, map_zero]

theorem map_surjective (f : U →ₗ[Rᵐᵒᵖ] V) (hf : Function.Injective f) :
    Function.Surjective (map (k := k) f) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := LinearMap.dualMap_surjective_of_injective
    (f := f.restrictScalars k) hf φ.functional
  exact ⟨⟨ψ⟩, RightDual.ext hψ⟩

end RightDual
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.DualTensor
variable {k R V W : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
variable [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower k R W]

def precomposeRight (a : V →ₗ[R] W) : (W →ₗ[R] R) →ₗ[Rᵐᵒᵖ] (V →ₗ[R] R) where
  toFun f := f.comp a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ArExplicit.DualTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_RightDualHomology
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.RightDualHomology
universe u
variable {k R U V W : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup U] [Module k U] [Module Rᵐᵒᵖ U] [IsScalarTower k Rᵐᵒᵖ U]
variable [AddCommGroup V] [Module k V] [Module Rᵐᵒᵖ V] [IsScalarTower k Rᵐᵒᵖ V]
variable [AddCommGroup W] [Module k W] [Module Rᵐᵒᵖ W] [IsScalarTower k Rᵐᵒᵖ W]

variable (f : U →ₗ[Rᵐᵒᵖ] V) (g : V →ₗ[Rᵐᵒᵖ] W) (h : g.comp f = 0)

def cycleMap : U →ₗ[Rᵐᵒᵖ] LinearMap.ker g :=
  f.codRestrict (LinearMap.ker g) (fun x => LinearMap.congr_fun h x)

def boundaries : Submodule Rᵐᵒᵖ (LinearMap.ker g) := LinearMap.range (cycleMap f g h)

abbrev Homology := LinearMap.ker g ⧸ boundaries f g h

def cyclesToDualHomology : LinearMap.ker (RightDual.map (k := k) f) →ₗ[R]
    RightDual k R (Homology f g h) where
  toFun φ := ⟨((boundaries f g h).restrictScalars k).liftQ
    (φ.val.functional.comp ((LinearMap.ker g).subtype.restrictScalars k)) (by
      rintro _ ⟨x, rfl⟩
      exact congrArg (fun ψ : RightDual k R U => ψ.functional x) φ.property)⟩
  map_add' φ ψ := by
    apply RightDual.ext
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    rfl
  map_smul' r φ := by
    apply RightDual.ext
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    rfl

omit [Module k W] [IsScalarTower k Rᵐᵒᵖ W] in
@[simp] theorem cyclesToDualHomology_mk
    (φ : LinearMap.ker (RightDual.map (k := k) f)) (x : LinearMap.ker g) :
    (cyclesToDualHomology f g h φ).functional ((boundaries f g h).mkQ x) =
      φ.val.functional x.val := rfl

omit [Module k W] [IsScalarTower k Rᵐᵒᵖ W] in
theorem cyclesToDualHomology_surjective :
    Function.Surjective (cyclesToDualHomology (k := k) f g h) := by
  intro l
  let ℓ : ((LinearMap.ker g).restrictScalars k) →ₗ[k] k :=
    l.functional.comp ((boundaries f g h).mkQ.restrictScalars k)
  obtain ⟨φ, hφ⟩ := ℓ.exists_extend
  have hp : (RightDual.mk φ : RightDual k R V) ∈ LinearMap.ker (RightDual.map (k := k) f) := by
    apply RightDual.ext
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hφ (cycleMap f g h x)
    change φ (f x) = 0
    change φ (f x) = l.functional ((boundaries f g h).mkQ (cycleMap f g h x)) at hx
    rw [show (boundaries f g h).mkQ (cycleMap f g h x) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero] at hx
    exact hx
  refine ⟨⟨⟨φ⟩, hp⟩, ?_⟩
  apply RightDual.ext
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
  exact LinearMap.congr_fun hφ x

def dualCycleMap : RightDual k R W →ₗ[R] LinearMap.ker (RightDual.map (k := k) f) :=
  (RightDual.map g).codRestrict _ (by
    intro ψ
    apply RightDual.ext
    ext x
    change ψ.functional (g (f x)) = 0
    have hx : g (f x) = 0 := LinearMap.congr_fun h x
    rw [hx, map_zero])

def dualBoundaries : Submodule R (LinearMap.ker (RightDual.map (k := k) f)) :=
  LinearMap.range (dualCycleMap f g h)

abbrev DualHomology := LinearMap.ker (RightDual.map (k := k) f) ⧸ dualBoundaries f g h

theorem cyclesToDualHomology_kernel :
    LinearMap.ker (cyclesToDualHomology (k := k) f g h) = dualBoundaries f g h := by
  ext φ
  constructor
  · intro hφ
    have ha : φ.val.functional ∈ (LinearMap.ker (g.restrictScalars k)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      exact congrArg (fun l : RightDual k R (Homology f g h) =>
        l.functional ((boundaries f g h).mkQ ⟨x, hx⟩)) hφ
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at ha
    obtain ⟨ψ, hψ⟩ := ha
    exact ⟨⟨ψ⟩, Subtype.ext (RightDual.ext hψ)⟩
  · rintro ⟨ψ, rfl⟩
    apply RightDual.ext
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    change ψ.functional (g x.val) = 0
    rw [x.property, map_zero]

def dualHomologyEquiv : RightDual k R (Homology f g h) ≃ₗ[R] DualHomology (k := k) f g h :=
  ((Submodule.quotEquivOfEq _ _ (cyclesToDualHomology_kernel f g h).symm).trans
    ((cyclesToDualHomology f g h).quotKerEquivOfSurjective
      (cyclesToDualHomology_surjective f g h))).symm

end ArExplicit.RightDualHomology

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProducts
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u

section Cochains

variable {C : Type*} [Category* C] [Preadditive C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

def shiftedCocycleHom (y : Cocycle L M m) (n : ℤ) : L⟦n⟧ ⟶ M⟦n + m⟧ :=
  (Cocycle.equivHomShift.symm y)⟦n⟧' ≫
    (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) m n (n + m)
      (add_comm m n)).inv.app M

end Cochains

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ConcentratedNatDerived
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem concentratedNat_exact (K : ChainComplex C ℕ) (n : ℕ)
    (hex : ∀ m : ℕ, m ≠ n → K.ExactAt m) (i : ℤ) (hi : i ≠ -(n : ℤ)) :
    (K.extend ComplexShape.embeddingDownNat).ExactAt i := by
  by_cases hh : ∃ m : ℕ, -(m : ℤ) = i
  · obtain ⟨m, rfl⟩ := hh
    exact (K.extend_exactAt_iff ComplexShape.embeddingDownNat (j := m) rfl).mpr
      (hex m (by omega))
  · exact K.extend_exactAt ComplexShape.embeddingDownNat i (by intro m hm; exact hh ⟨m, hm⟩)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_NatResolutionCubic
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (f : ∀ n : ℕ, P.complex.X (n+3) ⟶ P.complex.X n)

def natCubicCochain : Cochain P.cochainComplex P.cochainComplex 3 :=
  Cochain.mk (fun p q hpq => if hq : q ≤ 0 then
    let m := (-q).toNat
    (P.cochainComplexXIso p (m+3) (by dsimp [m]; omega)).hom ≫ f m ≫
      (P.cochainComplexXIso q m (by dsimp [m]; omega)).inv
    else 0)

theorem natCubicCochain_v (m : ℕ) :
    (natCubicCochain P f).v (-((m+3 : ℕ) : ℤ)) (-(m : ℤ)) (by omega) =
      (P.cochainComplexXIso (-((m+3 : ℕ) : ℤ)) (m+3) rfl).hom ≫ f m ≫
        (P.cochainComplexXIso (-(m : ℤ)) m rfl).inv := by
  cases m <;> rfl

end ArExplicit.ResolutionProducts

end

end OAI
end


