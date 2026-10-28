-- Prove2me | Definitions.Def_OAIQ031A044
-- name    : OAIQ031A044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:02:37.234071+00:00
-- url     : https://prove2.me/theorems/64003de1-e05f-4775-8057-db5bbed5c551
-- title:
--   Definitions bundle OAIQ031A044 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 16 definitions, 2 instances and 25 theorems. The definitions and types are `OAI.ArExplicit.A.barZeroCoordinate`, `OAI.ArExplicit.A.beta`, `OAI.ArExplicit.A.betaDetector`, `OAI.ArExplicit.A.simpleCoordinateEquiv`, `OAI.ArExplicit.EnvelopingBimodule.regularEquiv`, `OAI.ArExplicit.EnvelopingBimodule.stableEvaluation`, `OAI.ArExplicit.EnvelopingBimodule.tensorHom`, `OAI.ArExplicit.EnvelopingBimodule.tensorPiCoordinates`, `OAI.ArExplicit.EnvelopingBimodule.tensorPiRecombine`, `OAI.ArExplicit.ModuleBar.moduleObject`, `OAI.ArExplicit.Resolution.simpleCoordinateEquiv`, `OAI.ArExplicit.StableHom.classOfLinear`, `OAI.ArExplicit.StableHom.comp`, `OAI.ArExplicit.StableHom.identity`, `OAI.ArExplicit.StableHom.postcompHom`, `OAI.ArExplicit.projectiveMapsSubmodule`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_SimpleModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleModule.lean), [`AuslanderReiten_Algebras_TensorSimple`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorSimple.lean), [`AuslanderReiten_Bar_ModuleBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBar.lean), [`AuslanderReiten_Evaluation_TensorBeta`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorBeta.lean), [`AuslanderReiten_Evaluation_TensorBetaEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorBetaEvaluation.lean), [`AuslanderReiten_Stable_StableHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableHom.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedProjective.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedRegular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedRegular.lean), [`AuslanderReiten_Tensor_EnvelopingStableEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingStableEvaluation.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A025`, `OAIQ031A026`, `OAIQ031A027` and `OAIQ031A030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A061`, `OAIQ031A063`, `OAIQ031A064`, `OAIQ031A065`, `OAIQ031A067` and `OAIQ031A074`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A025
import Definitions.Def_OAIQ031A026
import Definitions.Def_OAIQ031A027
import Definitions.Def_OAIQ031A030

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

theorem simpleCoordinate_eq_zero_iff (hq : 1 + q ≠ 0) (a : Simple q) :
    simpleCoordinate q a = 0 ↔ a = 0 := by
  refine Submodule.Quotient.induction_on _ a ?_
  intro b
  rw [simpleCoordinate_mk, Submodule.Quotient.mk_eq_zero]
  exact (mem_range_dU_iff q hq b).symm

theorem simpleCoordinate_injective (hq : 1 + q ≠ 0) : Function.Injective (simpleCoordinate q) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (simpleCoordinate_eq_zero_iff q hq (a - b)).mp
  simp [map_sub, hab]

def simpleCoordinateEquiv (hq : 1 + q ≠ 0) : Simple q ≃ₗ[k] k :=
  LinearEquiv.ofBijective (simpleCoordinate q)
    ⟨simpleCoordinate_injective q hq, simpleCoordinate_surjective q⟩

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace ArExplicit

variable (R : Type u) [Ring R]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

variable {R M N}

variable {L P : Type u} [AddCommGroup L] [Module R L] [AddCommGroup P] [Module R P]

variable (R M N)

namespace StableHom

variable {R M N}

def postcompHom : (N →ₗ[R] P) →+ (StableHom R M N →+ StableHom R M P) where
  toFun := postcomp
  map_zero' := by
    apply AddMonoidHom.ext
    intro f
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp
  map_add' := by
    intro g h
    apply AddMonoidHom.ext
    intro f
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp only [AddMonoidHom.add_apply, postcomp_classOf]
    rw [show (g + h).comp f = g.comp f + h.comp f by ext x; rfl]
    exact map_add (classOf R M P) _ _

def comp : StableHom R N P →+ (StableHom R M N →+ StableHom R M P) :=
  QuotientAddGroup.lift (projectiveMaps R N P) postcompHom (by
    intro g hg
    change postcomp g = 0
    apply AddMonoidHom.ext
    intro f
    obtain ⟨f, rfl⟩ := classOf_surjective f
    exact (classOf_eq_zero_iff (g.comp f)).mpr (hg.precomp f))

@[simp]
theorem comp_classOf (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    comp (classOf R N P g) (classOf R M N f) = classOf R M P (g.comp f) := by
  change postcomp g (classOf R M N f) = _
  exact postcomp_classOf g f

def identity : StableHom R M M := classOf R M M LinearMap.id

@[simp]
theorem identity_comp (f : StableHom R M N) : comp identity f = f := by
  obtain ⟨f, rfl⟩ := classOf_surjective f
  simp [identity]

@[simp]
theorem comp_identity (f : StableHom R M N) : comp f identity = f := by
  obtain ⟨f, rfl⟩ := classOf_surjective f
  simp [identity]

end StableHom

section CentralScalars

variable {R M N}
variable (k : Type u) [CommRing k] [Algebra k R]
variable [Module k N] [IsScalarTower k R N]

def projectiveMapsSubmodule : Submodule k (M →ₗ[R] N) where
  __ := projectiveMaps R M N
  smul_mem' := fun a _ hf => hf.smul k a

instance stableHomModule : Module k (StableHom R M N) :=
  inferInstanceAs (Module k ((M →ₗ[R] N) ⧸ projectiveMapsSubmodule k))

namespace StableHom

def classOfLinear : (M →ₗ[R] N) →ₗ[k] StableHom R M N :=
  (projectiveMapsSubmodule k).mkQ

@[simp]
theorem classOfLinear_apply (f : M →ₗ[R] N) :
    classOfLinear k f = classOf R M N f := rfl

@[simp]
theorem classOf_smul (a : k) (f : M →ₗ[R] N) :
    classOf R M N (a • f) = a • classOf R M N f :=
  (classOfLinear k).map_smul a f

end StableHom

end CentralScalars

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def moduleObject (n : ℕ) : ModuleCat.{u} R :=
  letI := leftModule k R M n
  ModuleCat.of R (object k R M n)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorSimple
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

def simpleCoordinateEquiv (hq1 : 1 + q ≠ 0) : Simple q ≃ₗ[k] k :=
  (TensorProduct.congr (Resolution.simpleCoordinateEquiv q hq1)
    (Resolution.simpleCoordinateEquiv q hq1)).trans (TensorProduct.lid k k)

theorem simpleCoordinate_injective (hq1 : 1 + q ≠ 0) :
    Function.Injective (simpleCoordinate q) := (simpleCoordinateEquiv q hq1).injective

theorem simpleCoordinate_smul (a : A k q) (x : Simple q) :
    simpleCoordinate q (a • x) = simpleCharacter q a * simpleCoordinate q x := by
  let w : S ⊗[k] S := x
  change simpleCoordinate q (ExternalTensor.representation k R R S S a w) =
    simpleCharacter q a * simpleCoordinate q w
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_mul]
  | tmul a b =>
    induction w using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, mul_add]
    | tmul s t =>
      change Resolution.simpleCoordinate q (a • s) * Resolution.simpleCoordinate q (b • t) =
        (T.simpleCharacter q a * T.simpleCharacter q b) *
          (Resolution.simpleCoordinate q s * Resolution.simpleCoordinate q t)
      rw [Resolution.t_simple_character, Resolution.t_simple_character]
      change (a.base.coeff .f * _) * (b.base.coeff .f * _) =
        (a.base.coeff .f * b.base.coeff .f) * (_ * _)
      ring

theorem augmentationIdeal_annihilates (hq1 : 1 + q ≠ 0)
    (a : A k q) (ha : a ∈ augmentationIdeal q) (x : Simple q) : a • x = 0 := by
  apply simpleCoordinate_injective q hq1
  rw [simpleCoordinate_smul, show simpleCharacter q a = 0 from ha, zero_mul]
  change 0 = simpleCoordinate q (0 : S ⊗[k] S)
  exact (map_zero _).symm

theorem socleMap_mem (x : Simple q) : socleMap q x ∈ augmentationIdeal q := by
  let w : S ⊗[k] S := x
  let F : S ⊗[k] S →ₗ[k] A k q :=
    TensorProduct.map ((T.socleMap q).restrictScalars k) ((T.socleMap q).restrictScalars k)
  change simpleCharacter q (F w) = 0
  induction w using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul s t =>
    change simpleCharacter q (T.socleMap q s ⊗ₜ[k] T.socleMap q t) = 0
    rw [simpleCharacter_tmul]
    have hz (u : S) : T.simpleCharacter q (T.socleMap q u) = 0 := by
      change ((Resolution.simpleCoordinate q u) • T.upper q .f).base.coeff .f = 0
      simp [T.upper, TrivialExtension.inr]
    rw [hz, zero_mul]

def beta : Simple q →ₗ[A k q] augmentationIdeal q :=
  (socleMap q).codRestrict (augmentationIdeal q) (socleMap_mem q)

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorBeta
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)

theorem augmentation_kernel (hq1 : 1 + q ≠ 0) :
    LinearMap.ker (augmentation q) = augmentationIdeal q := by
  ext a
  change augmentation q a = 0 ↔ simpleCharacter q a = 0
  constructor
  · intro h
    have hh := congrArg (simpleCoordinate q) h
    change simpleCoordinate q (a • simpleGenerator q) = simpleCoordinate q (0 : Simple q) at hh
    simpa only [simpleCoordinate_smul, simpleGenerator_coordinate, mul_one, simpleCoordinate_zero] using hh
  · intro h
    apply simpleCoordinate_injective q hq1
    change simpleCoordinate q (a • simpleGenerator q) = simpleCoordinate q (0 : Simple q)
    rw [simpleCoordinate_smul, h, zero_mul, simpleCoordinate_zero]

def betaDetector : A k q →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp
    (TensorProduct.map (T.coefficient q (true, .f)) (T.coefficient q (true, .f)))

@[simp] theorem betaDetector_socle :
    betaDetector q (T.upper q .f ⊗ₜ[k] T.upper q .f) = 1 := by
  simp [betaDetector]

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorBetaEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)

def barZeroCoordinate : (A k q) ⊗[k] (Resolution.Simple q ⊗[k] Resolution.Simple q) →ₗ[k] A k q :=
  (TensorProduct.rid k (A k q)).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : A k q →ₗ[k] A k q) (simpleCoordinate q))

@[simp] theorem barZeroCoordinate_tmul (a : A k q) (x : Simple q) :
    barZeroCoordinate q (a ⊗ₜ[k] x) = simpleCoordinate q x • a := by
  change (TensorProduct.rid k (A k q)) (a ⊗ₜ[k] simpleCoordinate q x) = _
  exact TensorProduct.rid_tmul _ _

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedRegular
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule

universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]

omit [IsScalarTower k R X] in
@[simp] theorem regularInverse_tmul (a : R) (x : X) :
    regularInverse k R X (a ⊗ₜ[k] x) =
      BalancedTensor.tmul (⟨a ⊗ₜ[k] (1 : Rᵐᵒᵖ)⟩ : EnvelopingBimodule k R (regularObject k R)) x := rfl

theorem regularInverse_evaluation
    (z : BalancedTensor k R (EnvelopingBimodule k R (regularObject k R)) X) :
    regularInverse k R X (regularEvaluation k R X z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [_root_.map_zero]
  | add z w hz hw => simp only [_root_.map_add, hz, hw]
  | tmul f x =>
    rcases f with ⟨f⟩
    induction f using OAI.tensorInductionOn with
    | add f g hf hg =>
      change regularInverse k R X (regularEvaluation k R X
        (BalancedTensor.tmul ((⟨f⟩ : EnvelopingBimodule k R (regularObject k R)) + ⟨g⟩) x)) =
          BalancedTensor.tmul ((⟨f⟩ : EnvelopingBimodule k R (regularObject k R)) + ⟨g⟩) x
      simpa only [BalancedTensor.add_tmul, _root_.map_add] using congrArg₂ (· + ·) hf hg
    | tmul a b =>
      rw [regularEvaluation_tmul, regularInverse_tmul, ← BalancedTensor.balance]
      congr 1
      apply EnvelopingBimodule.ext
      change (((1 : R) ⊗ₜ[k] MulOpposite.op b.unop) * (a ⊗ₜ[k] (1 : Rᵐᵒᵖ))) = a ⊗ₜ[k] b
      simp only [MulOpposite.op_unop, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem regularEvaluation_inverse (z : R ⊗[k] X) :
    regularEvaluation k R X (regularInverse k R X z) = z := by
  induction z using OAI.tensorInductionOn with
  | add z w hz hw => simp only [_root_.map_add, hz, hw]
  | tmul a x => simp only [regularInverse_tmul, regularEvaluation_tmul, MulOpposite.unop_one, one_smul]

def regularEquiv :
    BalancedTensor k R (EnvelopingBimodule k R (regularObject k R)) X ≃ₗ[R] R ⊗[k] X where
  __ := regularEvaluation k R X
  invFun := regularInverse k R X
  left_inv := regularInverse_evaluation k R X
  right_inv := regularEvaluation_inverse k R X

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]

instance regular_projective :
    Module.Projective R (BalancedTensor k R (EnvelopingBimodule k R (regularObject k R)) X) :=
  Module.Projective.of_equiv (regularEquiv k R X).symm

variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]

def tensorPiCoordinates (n : ℕ) :
    BalancedTensor k R (EnvelopingBimodule k R (piObject M n)) X →ₗ[R]
      (Fin n → BalancedTensor k R (EnvelopingBimodule k R M) X) :=
  LinearMap.pi fun i => tensorMap X (piProjection M n i)

def tensorPiRecombine (n : ℕ) :
    (Fin n → BalancedTensor k R (EnvelopingBimodule k R M) X) →ₗ[R]
      BalancedTensor k R (EnvelopingBimodule k R (piObject M n)) X :=
  ∑ i, (tensorMap X (piInclusion M n i)).comp (LinearMap.proj i)

omit [IsScalarTower k R X] in
@[simp] theorem tensorPiRecombine_apply (n : ℕ)
    (v : Fin n → BalancedTensor k R (EnvelopingBimodule k R M) X) :
    tensorPiRecombine X M n v = ∑ i, tensorMap X (piInclusion M n i) (v i) := by
  simp only [tensorPiRecombine, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem pi_reconstruct (n : ℕ) (f : EnvelopingBimodule k R (piObject M n)) :
    ∑ i, map (piInclusion M n i) (map (piProjection M n i) f) = f := by
  apply EnvelopingBimodule.ext
  change (scalarEquiv (piObject M n)) (∑ i, map (piInclusion M n i) (map (piProjection M n i) f)) = f.value
  rw [_root_.map_sum]
  change (∑ i, Pi.single i (f.value i)) = f.value
  exact Finset.univ_sum_single f.value

omit [IsScalarTower k R X] in
theorem tensorPi_retraction (n : ℕ) :
    (tensorPiRecombine X M n).comp (tensorPiCoordinates X M n) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  change tensorPiRecombine X M n (tensorPiCoordinates X M n z) = z
  induction z using BalancedTensor.induction_on with
  | zero => simp only [_root_.map_zero]
  | add z w hz hw => simp only [_root_.map_add, hz, hw]
  | tmul f x =>
    rw [tensorPiRecombine_apply]
    change (∑ i, tensorMap X (piInclusion M n i)
      (tensorMap X (piProjection M n i) (BalancedTensor.tmul f x))) = BalancedTensor.tmul f x
    simp only [tensorMap_tmul]
    change (∑ i, ((BalancedTensor.mk (k := k) (R := R)).flip x)
      (map (piInclusion M n i) (map (piProjection M n i) f))) = _
    rw [← _root_.map_sum, pi_reconstruct]
    rfl

omit [IsScalarTower k R X] in
theorem tensorPi_projective
    [Module.Projective R (BalancedTensor k R (EnvelopingBimodule k R M) X)] (n : ℕ) :
    Module.Projective R (BalancedTensor k R (EnvelopingBimodule k R (piObject M n)) X) :=
  Module.Projective.of_split (R := R) (tensorPiCoordinates X M n) (tensorPiRecombine X M n)
    (tensorPi_retraction X M n)

theorem tensor_projective [Module.Finite (R ⊗[k] Rᵐᵒᵖ) M]
    [Module.Projective (R ⊗[k] Rᵐᵒᵖ) M] :
    Module.Projective R (BalancedTensor k R (EnvelopingBimodule k R M) X) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' (R ⊗[k] Rᵐᵒᵖ) M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p
    (LinearMap.id : M →ₗ[R ⊗[k] Rᵐᵒᵖ] M) hp
  let := regular_projective (k := k) (R := R) X
  let : Module.Projective R (BalancedTensor k R
      (EnvelopingBimodule k R (piObject (regularObject k R) n)) X) :=
    tensorPi_projective X (regularObject k R) n
  apply Module.Projective.of_split (tensorMap X (ModuleCat.ofHom s))
    (tensorMap X (ModuleCat.ofHom p))
  rw [← tensorMap_comp]
  have hsp : ModuleCat.ofHom s ≫ ModuleCat.ofHom p = 𝟙 M := by
    apply ModuleCat.hom_ext
    exact hs
  rw [hsp, tensorMap_id]

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingStableEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]
variable {M N P : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable [Module k P] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) P]

omit [IsScalarTower k R X] in
theorem tensorMap_smul_linear (c : k) (f : M →ₗ[R ⊗[k] Rᵐᵒᵖ] N) :
    tensorMap X (ModuleCat.ofHom (c • f)) = c • tensorMap X (ModuleCat.ofHom f) := by
  have hm : map (ModuleCat.ofHom (c • f)) = c • map (ModuleCat.ofHom f) := by
    apply LinearMap.ext
    intro z
    rfl
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z w hz hw => simp_all
  | tmul m x => simp only [tensorMap_tmul, hm, LinearMap.smul_apply,
      BalancedTensor.scalar_tmul]

def tensorHom : (M →ₗ[R ⊗[k] Rᵐᵒᵖ] N) →ₗ[k]
    (BalancedTensor k R (EnvelopingBimodule k R M) X →ₗ[R]
      BalancedTensor k R (EnvelopingBimodule k R N) X) where
  toFun f := tensorMap X (ModuleCat.ofHom f)
  map_add' _ _ := tensorMap_add X _ _
  map_smul' := tensorMap_smul_linear X

variable [Module.Finite k R] [Module.Finite k X]

theorem tensorHom_projective {f : M →ₗ[R ⊗[k] Rᵐᵒᵖ] N}
    (hf : FactorsThroughFiniteProjective (R ⊗[k] Rᵐᵒᵖ) M N f) :
    FactorsThroughFiniteProjective R
      (BalancedTensor k R (EnvelopingBimodule k R M) X)
      (BalancedTensor k R (EnvelopingBimodule k R N) X) (tensorHom X f) := by
  obtain ⟨Q, hQ, hAQ, hp, hfin, i, p, rfl⟩ := hf
  let Q' : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ) := ModuleCat.of _ Q
  let : Module k Q := ModuleCat.moduleOfAlgebraModule Q'
  let : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) Q := ModuleCat.isScalarTower_of_algebra_moduleCat Q'
  let : Module.Finite k Q := Module.Finite.trans (R ⊗[k] Rᵐᵒᵖ) Q
  let : Module.Finite k (BalancedTensor k R (EnvelopingBimodule k R Q') X) := inferInstance
  let : Module.Finite R (BalancedTensor k R (EnvelopingBimodule k R Q') X) :=
    Module.Finite.of_restrictScalars_finite k R _
  refine ⟨BalancedTensor k R (EnvelopingBimodule k R Q') X,
    inferInstance, inferInstance, tensor_projective X Q', inferInstance,
    tensorMap X (ModuleCat.ofHom i), tensorMap X (ModuleCat.ofHom p), ?_⟩
  exact (tensorMap_comp X (ModuleCat.ofHom i) (ModuleCat.ofHom p)).symm

def stableEvaluation : StableHom (R ⊗[k] Rᵐᵒᵖ) M N →+
    StableHom R (BalancedTensor k R (EnvelopingBimodule k R M) X)
      (BalancedTensor k R (EnvelopingBimodule k R N) X) :=
  QuotientAddGroup.map _ _ (tensorHom (k := k) (M := M) (N := N) X).toAddMonoidHom (by
    intro f hf
    exact (factorsThroughFiniteFree_iff_projective _).mpr
      (tensorHom_projective X ((factorsThroughFiniteFree_iff_projective _).mp hf)))

@[simp]
theorem stableEvaluation_classOf (f : M →ₗ[R ⊗[k] Rᵐᵒᵖ] N) :
    stableEvaluation X (StableHom.classOf _ _ _ f) =
      StableHom.classOf R _ _ (tensorMap X (ModuleCat.ofHom f)) :=
  QuotientAddGroup.map_mk' _ _ _ _ _

end ArExplicit.EnvelopingBimodule

end

end OAI
end


