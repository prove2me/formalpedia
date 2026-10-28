-- Prove2me | Definitions.Def_OAIQ031A047
-- name    : OAIQ031A047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:04:41.886896+00:00
-- url     : https://prove2.me/theorems/41ef4a3e-1e46-48f0-8b29-b3ea7181b373
-- title:
--   Definitions bundle OAIQ031A047 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 15 definitions, 5 instances and 23 theorems. The definitions and types are `OAI.ArExplicit.AFrobeniusTrace`, `OAI.ArExplicit.ExternalTensor.forgetTermEquiv`, `OAI.ArExplicit.ExternalTensor.forgetTermIso`, `OAI.ArExplicit.ExternalTensor.freeFlatEquiv`, `OAI.ArExplicit.ExternalTensor.homCochainInclusion`, `OAI.ArExplicit.ExternalTensor.homCochainSummand`, `OAI.ArExplicit.ExternalTensor.homCochainTermCoordinates`, `OAI.ArExplicit.ExternalTensor.homCochainTotal`, `OAI.ArExplicit.ExternalTensor.homFreeCoordinates`, `OAI.ArExplicit.ExternalTensor.homMap`, `OAI.ArExplicit.ExternalTensor.homOutTerm`, `OAI.ArExplicit.ExternalTensor.homPair`, `OAI.ArExplicit.ExternalTensor.scalarInclusion`, `OAI.ArExplicit.ExternalTensor.scalarTermDirectSumEquiv`, `OAI.ArExplicit.ModuleBar.contraction`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Algebras_SymmetricSocle`, `AuslanderReiten_Algebras_TensorFrobenius`, `AuslanderReiten_Algebras_TensorSimple`, `AuslanderReiten_Algebras_TensorStructure`, `AuslanderReiten_Bar_BarComplex`, `AuslanderReiten_Bar_ModuleBar`, `AuslanderReiten_Bar_TCasimir`, `AuslanderReiten_Bar_TCasimirAugmentation`, `AuslanderReiten_Cocycles_CocycleTwist`, `AuslanderReiten_Complete_CompleteShiftDual`, `AuslanderReiten_Resolutions_Resolution`, `AuslanderReiten_Stable_StableHom`, `AuslanderReiten_Tensor_ExternalTensorForget`, `AuslanderReiten_Tensor_ExternalTensorHom`, `AuslanderReiten_Tensor_ExternalTensorHomComplex`, `AuslanderReiten_Tensor_ExternalTensorModule`.
--
--   **Imports.** It imports the bundles `OAIQ031A008`, `OAIQ031A025`, `OAIQ031A027`, `OAIQ031A028`, `OAIQ031A029`, `OAIQ031A030` and `OAIQ031A031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A063`, `OAIQ031A064`, `OAIQ031A065`, `OAIQ031A066`, `OAIQ031A068`, `OAIQ031A071`, `OAIQ031A072`, `OAIQ031A073` and `OAIQ031A075`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A008
import Definitions.Def_OAIQ031A025
import Definitions.Def_OAIQ031A027
import Definitions.Def_OAIQ031A028
import Definitions.Def_OAIQ031A029
import Definitions.Def_OAIQ031A030
import Definitions.Def_OAIQ031A031

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem identity_eq_zero_iff [Module.Finite R M] :
    classOf R M M LinearMap.id = 0 ↔ Module.Projective R M := by
  rw [classOf_eq_zero_iff_projective]
  constructor
  · rintro ⟨P, hP, hRP, hprojective, hfinite, i, p, h⟩
    exact Module.Projective.of_split i p h
  · intro h
    exact ⟨M, inferInstance, inferInstance, h, inferInstance,
      LinearMap.id, LinearMap.id, rfl⟩

end StableHom

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SymmetricSocle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable (J : Ideal R) [J.IsTwoSided]

include τ hs

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (hM : ∀ j ∈ J, ∀ x : M, j • x = 0)
variable (ι : N →ₗ[R] R) (hι : Function.Injective ι) (hN : ∀ x : N, ι x ∈ J)

include hM hι hN

theorem factor_fin_zero (n : ℕ) (g : M →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] N) :
    p.comp g = 0 := by
  apply LinearMap.ext
  intro x
  apply hι
  change ι (p (g x)) = ι 0
  rw [map_zero]
  have he : g x = ∑ j : Fin n, g x j • Pi.single j (1 : R) := by
    ext j
    simp [Pi.single_apply]
  rw [he, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  simp only [map_smul, smul_eq_mul]
  apply τ.annihilator_right hs J _ (hN _)
  intro r hr
  let gj : M →ₗ[R] R := (LinearMap.proj j).comp g
  change r • gj x = 0
  rw [← gj.map_smul, hM r hr x, map_zero]

theorem projective_factor_zero (f : M →ₗ[R] N)
    (hf : FactorsThroughFiniteProjective R M N f) : f = 0 := by
  rcases hf with ⟨P, hP, hRP, hp, hfinite, i, p, rfl⟩
  let := hP
  let := hRP
  let := hp
  let := hfinite
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hspl⟩ := Module.projective_lifting_property π (LinearMap.id : P →ₗ[R] P) hπ
  have hz := τ.factor_fin_zero hs J hM ι hι hN n (s.comp i) (p.comp π)
  have he : (p.comp π).comp (s.comp i) = p.comp i := by
    apply LinearMap.ext
    intro x
    have hh := LinearMap.congr_fun hspl (i x)
    change π (s (i x)) = i x at hh
    exact congrArg p hh
  rw [he] at hz
  exact hz

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorStructure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

namespace A

variable {k : Type*} [Field k] (q : k)

theorem diagonalAlg_surjective : Function.Surjective (diagonalAlg q) :=
  (quotientCoordinates (k := k)).surjective.comp
    (Algebra.TensorProduct.map_surjective (T.diagonalAlg q) (T.diagonalAlg q)
      (T.diagonalAlg_surjective q) (T.diagonalAlg_surjective q))

end A
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorFrobenius
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

noncomputable def AFrobeniusTrace (k : Type*) [Field k] (q : k) : FrobeniusTrace k (A k q) :=
  (trivialExtensionFrobeniusTrace k (BaseAlgebra k q)).tensor
    (trivialExtensionFrobeniusTrace k (BaseAlgebra k q))

theorem A_trace_symmetric (k : Type*) [Field k] (q : k) (a b : A k q) :
    (AFrobeniusTrace k q).trace (a * b) = (AFrobeniusTrace k q).trace (b * a) :=
  FrobeniusTrace.tensorTrace_mul_comm _ _ TrivialExtension.trace_mul_comm
    TrivialExtension.trace_mul_comm a b

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_Resolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

theorem finite_fixedRight (p : C) (hp : p * p = p) :
    Module.Finite k (fixedRight q p) :=
  Module.Finite.of_surjective ((projection q p hp).restrictScalars k)
    (projection_surjective q p hp)

instance instFiniteSubtypeBaseAlgebraMemSubmoduleF : Module.Finite k (F q) :=
  finite_fixedRight q _ (by simpa [multiplicationTable] using basis_mul q f f)

end ArExplicit.Resolution

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

variable [CharP k 2]

theorem boundary_exact (n : ℕ) :
    LinearMap.range (boundary k R (n + 1)) = LinearMap.ker (boundary k R n) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact boundary_squared k R n x
  · intro x hx
    refine ⟨contraction k R (n + 1) x, ?_⟩
    have h := contraction_identity k R n x
    rw [show boundary k R n x = 0 from hx, map_zero, add_zero] at h
    exact h

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable [CharP k 2]

def contraction (n : ℕ) : object k R M n →ₗ[k] object k R M (n + 1) :=
  TensorProduct.mk k R (object k R M n) 1

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.freeFree _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module k M] [Module k N] [Module A M] [Module B N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

instance tower : IsScalarTower k (A ⊗[k] B) (moduleObject k A B M N) :=
  IsScalarTower.of_algebraMap_smul (A := A ⊗[k] B) fun a x => by
    change representation k A B M N (algebraMap k (A ⊗[k] B) a) x = a • x
    rw [AlgHom.commutes]
    rfl

instance finite [Module.Finite k M] [Module.Finite k N] :
    Module.Finite k (moduleObject k A B M N) :=
  inferInstanceAs (Module.Finite k (M ⊗[k] N))

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorSimple
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)

instance instIsTwoSidedAugmentationIdeal : (augmentationIdeal q).IsTwoSided := inferInstanceAs
  (RingHom.ker (simpleCharacter q)).IsTwoSided

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleTwist
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

theorem coefficient_z (H : k) (a : T k q) (i : TIndex) :
    T.coefficient q i (z q H a) =
      if selected i then (H * q) * T.coefficient q i a else 0 := by
  conv_lhs => rw [T.expand q a]
  simp only [map_sum, map_smul, z_vector]
  rw [Finset.sum_eq_single i]
  · by_cases hi : selected i <;> simp [hi, mul_comm]
  · intro j _ hj
    by_cases hs : selected j
    · simp only [ite_eq_left hs, map_smul, T.coefficient_vector, ite_eq_right (Ne.symm hj), smul_zero]
    · simp only [ite_eq_right hs, map_zero, smul_zero]
  · simp

theorem twist_vector (H : kˣ) (i : TIndex) :
    TrivialExtension.twist H (T.vector q i) = (H : k) ^ i.weight • T.vector q i := by
  apply T.coordinate_ext q
  intro j
  rw [coefficient_twist]
  by_cases hj : j = i <;> simp [hj]

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimir
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

theorem trace_mul_star (a : R) (i : TIndex) :
    TrivialExtension.trace (a * vector q i.star) = coefficient q i a := by
  obtain ⟨b, i⟩ := i
  cases b <;> simp [TIndex.star, vector, lower, upper,
    TrivialExtension.inl, TrivialExtension.inr, coefficient, coordinateFunctional]
  rfl

theorem coefficient_right_product (a : R) (i j : TIndex) :
    coefficient q i (vector q j.star * a) = coefficient q j (a * vector q i.star) := by
  rw [← trace_mul_star, ← trace_mul_star]
  rw [mul_assoc, TrivialExtension.trace_mul_comm]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimirAugmentation
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

theorem lower_upper_same (i : Letter) :
    lower q i * upper q i = upper q (if TIndex.lowerSource i then .f else .e) := by
  apply TrivialExtension.ext
  · simp [lower, upper, TrivialExtension.inl, TrivialExtension.inr]
  · apply LinearMap.ext
    intro a
    cases i <;> simp [lower, upper, TrivialExtension.inl, TrivialExtension.inr,
      TIndex.lowerSource, BaseAlgebra.product]

theorem upper_lower_same (i : Letter) :
    upper q i * lower q i = upper q (if TIndex.lowerTarget i then .f else .e) := by
  apply TrivialExtension.ext
  · simp [lower, upper, TrivialExtension.inl, TrivialExtension.inr]
  · apply LinearMap.ext
    intro a
    cases i <;> simp [lower, upper, TrivialExtension.inl, TrivialExtension.inr,
      TIndex.lowerTarget, BaseAlgebra.product]

variable [CharP k 2]

theorem six_four_zero (x y : R) :
    x + x + x + x + x + x + y + y + y + y = 0 := by
  have hx := SparseParity.module_add_self_eq_zero (k := k) x
  have hy := SparseParity.module_add_self_eq_zero (k := k) y
  calc
    _ = (x + x) + (x + x) + (x + x) + (y + y) + (y + y) := by abel
    _ = 0 := by rw [hx, hy]; simp

theorem lower_upper_sum : (∑ i : Letter, lower q i * upper q i) = 0 := by
  simp only [lower_upper_same, Letter.sum_univ, TIndex.lowerSource, Bool.false_eq_true,
    reduceIte]
  exact six_four_zero q _ _

theorem upper_lower_sum : (∑ i : Letter, upper q i * lower q i) = 0 := by
  simp only [upper_lower_same, Letter.sum_univ, TIndex.lowerTarget, Bool.false_eq_true,
    reduceIte]
  refine Eq.trans ?_ (six_four_zero q (upper q .e) (upper q .f))
  abel

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShiftDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace DualExactCochain

open CompleteComparison

theorem shift {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : DualExactCochain K) (a : ℤ) :
    DualExactCochain (K⟦a⟧) := by
  intro i
  let E := (CochainComplex.shiftShortComplexFunctor' (ModuleCat.{u} R) a (i - 1) i (i + 1)
    (i + a - 1) (i + a) (i + a + 1) (by omega) (by omega) (by omega)).app K
  exact HomExactAt.of_shortComplex_iso E.symm (hK (i + a))

end DualExactCochain

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorForget
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

def scalarTermDirectSumEquiv (n : ℕ) :
    (scalarTotal k A B P Q).X n ≃ₗ[k] (Π₀ p : Diagonal n, scalarSummands k A B P Q n p) :=
  CategoryTheory.Iso.toLinearEquiv (ModuleCat.coprodIsoDirectSum (scalarSummands k A B P Q n))

def forgetTermEquiv (n : ℕ) :
    (forgetComplex k (A ⊗[k] B) (complex k A B P Q)).X n ≃ₗ[k] (scalarTotal k A B P Q).X n :=
  ((termDirectSumEquiv k A B P Q n).restrictScalars k).trans
    (scalarTermDirectSumEquiv k A B P Q n).symm

abbrev scalarInclusion (i j n : ℕ) (h : i+j=n) :
    scalarSummands k A B P Q n ⟨(i,j),h⟩ ⟶ (scalarTotal k A B P Q).X n :=
  ιMapBifunctor (forgetComplex k A P) (forgetComplex k B Q)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i j n h

def forgetTermIso (n : ℕ) :
    (forgetComplex k (A ⊗[k] B) (complex k A B P Q)).X n ≅ (scalarTotal k A B P Q).X n :=
  (forgetTermEquiv k A B P Q n).toModuleIso

theorem scalarTermDirectSumEquiv_inclusion (i j n : ℕ) (h : i+j=n) :
    (scalarTermDirectSumEquiv k A B P Q n).toLinearMap.comp
      (scalarInclusion k A B P Q i j n h).hom =
      DFinsupp.lsingle (R := k) (M := fun p : Diagonal n => scalarSummands k A B P Q n p)
        ⟨(i,j),h⟩ := by
  exact congrArg (fun f => f.hom)
    (ModuleCat.ι_coprodIsoDirectSum_hom (scalarSummands k A B P Q n) ⟨(i,j),h⟩)

@[reassoc] theorem scalarInclusion_forgetTermIso_inv (i j n : ℕ) (h : i+j=n) :
    scalarInclusion k A B P Q i j n h ≫ (forgetTermIso k A B P Q n).inv =
      ModuleCat.ofHom ((inclusion k A B P Q i j n h).hom.restrictScalars k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (termDirectSumEquiv k A B P Q n).injective
  change (termDirectSumEquiv k A B P Q n)
    ((termDirectSumEquiv k A B P Q n).symm
      ((scalarTermDirectSumEquiv k A B P Q n)
        ((scalarInclusion k A B P Q i j n h).hom x))) = _
  exact (LinearEquiv.apply_symm_apply (termDirectSumEquiv k A B P Q n) _).trans
    ((LinearMap.congr_fun (scalarTermDirectSumEquiv_inclusion k A B P Q i j n h) x).trans
      (LinearMap.congr_fun (termDirectSumEquiv_inclusion k A B P Q i j n h) x).symm)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def homPair : (M →ₗ[A] U) →ₗ[k] (N →ₗ[B] V) →ₗ[k]
    (moduleObject k A B M N →ₗ[A ⊗[k] B] moduleObject k A B U V) :=
  LinearMap.mk₂ k (map k A B)
    (fun f f' g => by
      apply LinearMap.restrictScalars_injective k
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact TensorProduct.add_tmul _ _ _)
    (fun a f g => by
      apply LinearMap.restrictScalars_injective k
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact TensorProduct.smul_tmul' a (f x) (g y))
    (fun f g g' => by
      apply LinearMap.restrictScalars_injective k
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact TensorProduct.tmul_add _ _ _)
    (fun a f g => by
      apply LinearMap.restrictScalars_injective k
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact TensorProduct.tmul_smul a (f x) (g y))

def homMap : (M →ₗ[A] U) ⊗[k] (N →ₗ[B] V) →ₗ[k]
    (moduleObject k A B M N →ₗ[A ⊗[k] B] moduleObject k A B U V) :=
  TensorProduct.lift (homPair k A B)

@[simp] theorem homMap_tmul (f : M →ₗ[A] U) (g : N →ₗ[B] V) :
    homMap k A B (f ⊗ₜ[k] g) = map k A B f g := rfl

def freeFlatEquiv (n m : ℕ) :
    moduleObject k A B (Fin n → A) (Fin m → B) ≃ₗ[A ⊗[k] B]
      (Fin n × Fin m → A ⊗[k] B) :=
  (freeEquiv k A B n m).trans (LinearEquiv.curry _ _ (Fin n) (Fin m)).symm

@[simp] theorem freeFlatEquiv_tmul (n m : ℕ) (a : Fin n → A) (b : Fin m → B)
    (i : Fin n) (j : Fin m) :
    freeFlatEquiv k A B n m (a ⊗ₜ[k] b) (i,j) = a i ⊗ₜ[k] b j :=
  freeCoordinates_tmul k A B n m a b i j

theorem freeFlatEquiv_symm_single (n m : ℕ) (i : Fin n) (j : Fin m) :
    (freeFlatEquiv k A B n m).symm (Pi.single (i,j) 1) =
      (Pi.single i (1 : A)) ⊗ₜ[k] (Pi.single j (1 : B)) := by
  apply (freeFlatEquiv k A B n m).injective
  rw [LinearEquiv.apply_symm_apply]
  funext ⟨i',j'⟩
  rw [freeFlatEquiv_tmul]
  by_cases hi : i'=i <;> by_cases hj : j'=j <;>
    simp [hi, hj, Prod.mk.injEq, Algebra.TensorProduct.one_def]

def homFreeCoordinates (n m : ℕ) :
    (moduleObject k A B (Fin n → A) (Fin m → B) →ₗ[A ⊗[k] B] moduleObject k A B U V) ≃ₗ[k]
      (Fin n × Fin m → moduleObject k A B U V) :=
  (LinearEquiv.congrLeft (moduleObject k A B U V) k (freeFlatEquiv k A B n m)).trans
    (LinearEquiv.piRing (A ⊗[k] B) (moduleObject k A B U V) (Fin n × Fin m) k)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

instance hasHomCochainTotal : HasMapBifunctor (homCochain k A P U) (homCochain k B Q V)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) := fun _ => inferInstance

abbrev homCochainTotal : CochainComplex (ModuleCat.{u} k) ℕ :=
  mapBifunctor (homCochain k A P U) (homCochain k B Q V)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)

def homOutTerm (n : ℕ) :
    ((complex k A B P Q).X n →ₗ[A ⊗[k] B] moduleObject k A B U V) →ₗ[k]
      (∀ p : Diagonal n, summands k A B P Q n p →ₗ[A ⊗[k] B] moduleObject k A B U V) where
  toFun f p := f.comp (inclusion k A B P Q p.val.1 p.val.2 n p.property).hom
  map_add' f g := by funext p; exact LinearMap.add_comp _ _ _
  map_smul' a f := by funext p; exact LinearMap.smul_comp _ _ _

abbrev homCochainSummand (n : ℕ) (p : Diagonal n) : ModuleCat.{u} k :=
  ModuleCat.of k ((P.X p.val.1 →ₗ[A] U) ⊗[k] (Q.X p.val.2 →ₗ[B] V))

def homCochainTermCoordinates (n : ℕ) :
    (homCochainTotal k A B P Q U V).X n ≃ₗ[k]
      (∀ p : Diagonal n, homCochainSummand k A B P Q U V n p) :=
  (ModuleCat.coprodIsoDirectSum (homCochainSummand k A B P Q U V n)).toLinearEquiv.trans
    DFinsupp.linearEquivFunOnFintype

variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

abbrev homCochainInclusion (i j n : ℕ) (h : i+j=n) :
    homCochainSummand k A B P Q U V n ⟨(i,j),h⟩ ⟶ (homCochainTotal k A B P Q U V).X n :=
  ιMapBifunctor (homCochain k A P U) (homCochain k B Q V)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) i j n h

omit [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
  [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)] in
theorem homCochainTermCoordinates_inclusion (i j n : ℕ) (h : i+j=n)
    (x : (P.X i →ₗ[A] U) ⊗[k] (Q.X j →ₗ[B] V)) :
    homCochainTermCoordinates k A B P Q U V n (homCochainInclusion k A B P Q U V i j n h x) =
      Pi.single ⟨(i,j),h⟩ x := by
  have hh := congrArg (fun f => f.hom x)
    (ModuleCat.ι_coprodIsoDirectSum_hom (homCochainSummand k A B P Q U V n) ⟨(i,j),h⟩)
  exact congrArg (fun y => DFinsupp.linearEquivFunOnFintype (R := k) y) hh

end ArExplicit.ExternalTensor

end

end OAI
end


