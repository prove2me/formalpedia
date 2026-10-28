-- Prove2me | Definitions.Def_OAIQ66So033
-- name    : OAIQ66So033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:49:50.553899+00:00
-- url     : https://prove2.me/theorems/6b27f9d1-0e4c-4f3c-b095-e01ed4c4bc65
-- title:
--   Definitions bundle OAIQ66So033 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 10 definitions, 1 inductive type or structure and 7 theorems. The definitions and types are `OAI.SimpleFInftyOvergroups.SourceRingData`, `OAI.SimpleFInftyOvergroups.SourceRingProducerObligation`, `OAI.StageConstruction.LimitGroup`, `OAI.StageConstruction.LimitPoints`, `OAI.StageConstruction.beta`, `OAI.StageConstruction.block`, `OAI.StageConstruction.delta`, `OAI.StageConstruction.exchange`, `OAI.StageConstruction.sigma`, `OAI.StageGeometry.shift`, `OAI.StageGeometry.trans`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`FiniteType_AscendingHNNInnerTwist`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/AscendingHNNInnerTwist.lean), [`FiniteType_StageConstruction`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/StageConstruction.lean), [`FiniteType_TorusAction`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TorusAction.lean), [`SimpleOvergroups_SourceRingReduction`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/SourceRingReduction.lean).
--
--   **Imports.** It imports the published bundle `Def_SimpleOvergroups`; the bundle `OAIQ66So030` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ66So034`; the statement `OAI.SimpleFInftyOvergroups.SourceRingData.realize`; the proof of `OAI.SimpleFInftyOvergroups.SourceRingData.realize`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_SimpleOvergroups
import Definitions.Def_OAIQ66So030

section
-- module Solutions.OAIQ066_SO.FiniteType_StageConstruction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.StageConstruction.columnMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace StageConstruction
variable {R : Type*} [Ring R]

def block : Steinberg.Group (Fin 6) R →* Q R :=
  Steinberg.pi.comp (Steinberg.reindex Function.Embedding.inl)

lemma block_matrix (g : Steinberg.Group (Fin 6) R) :
    (block g).val=Steinberg.matrixBlock (p:=Unit) (Steinberg.matrix g) :=
  Steinberg.matrix_reindex_inl g

lemma block_fixes (g : Steinberg.Group (Fin 6) R) (a : R) :
    action (block g) (Pi.single first a)=Pi.single first a := by
  rw [action_apply,block_matrix]
  ext i
  cases i <;> simp [Steinberg.matrixBlock,Matrix.mulVec,dotProduct,
    Matrix.fromBlocks,first,Pi.single_apply]

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

def exchange (d : R) : Q R :=
  ⟨NoncommElementary.exchange first second first_ne_second d,
    NoncommElementary.exchange_mem _ _ _ _⟩

lemma exchange_fixes (d a : R) (ha : d*a=0) :
    action (exchange d) (Pi.single first a)=Pi.single first a :=
  NoncommElementary.exchange_fixes _ _ _ _ _ ha

end StageConstruction

namespace StageConstruction
variable {R : Type*} [Ring R]

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

lemma transitionUnits_injective (hφ : Function.Injective φ) :
    Function.Injective (transitionUnits φ D) := by
  intro u v h
  apply NonunitalCompression.units_injective (φ.comp φ) (hφ.comp hφ)
  apply Units.ext
  have he := congrArg (fun q : Q R => action q (Pi.single first 1) first) h
  simpa only [action_apply,transitionUnits_val,NoncommElementary.position_mulVec,
    mul_one,Pi.single_eq_same] using he

def beta {Y : Type*} (S : Y → R) (y : Y) : X R := Pi.single first (φ (φ (S y)))

lemma transitionUnits_beta {Y : Type*} (S : Y → R) (v : Rˣ) (y z : Y)
    (h : v.val*S y=S z) : action (transitionUnits φ D v) (beta φ S y)=beta φ S z := by
  rw [action_apply,transitionUnits_val,beta,NoncommElementary.position_mulVec]
  congr 1
  exact (NonunitalCompression.unitValue_mul_image (φ.comp φ) v.val (S y)).trans
    (congrArg (φ.comp φ) h)

variable {Y : Type*} [DecidableEq Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)

variable {W : Type*} [Group W] [MulAction W Y]
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (action q x))

def delta : Q R →* Q R := (transitionUnits φ D).comp (ρ.comp ι)
def sigma : X R → X R := beta φ S ∘ point

lemma delta_injective (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
    (hι : Function.Injective ι) : Function.Injective (delta φ D ρ ι) :=
  (transitionUnits_injective φ D hφ).comp (hρ.comp hι)

include hρS hpoint in
omit [DecidableEq Y] in
lemma transition_equivariant (q : Q R) (x : X R) :
    action (delta φ D ρ ι q) (sigma φ S point x)=sigma φ S point (action q x) := by
  change action (transitionUnits φ D (ρ (ι q))) (beta φ S (point x))=_
  rw [transitionUnits_beta φ D S (ρ (ι q)) (point x) (ι q • point x) (hρS _ _),hpoint]
  rfl

end StageConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TorusAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement

namespace StageConstruction
variable {R : Type*} [Ring R]

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable {Y W : Type*} [DecidableEq Y] [Group W] [MulAction W Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point)

abbrev LimitGroup := AscendingHNN.Torus (delta φ D ρ ι) (delta_injective φ D ρ ι hφ hρ hι)
abbrev LimitPoints := SequentialLimit.Limit (sigma φ S point)

end StageConstruction

end

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNNInnerTwist
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise

namespace StageGeometry
open StageConstruction

variable {R Y W : Type} [Ring R] [Group W] [MulAction W Y]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (S : Y → R) (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι)

abbrev trans := delta φ D ρ ι
abbrev shift := sigma φ S point

end StageGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SourceRingReduction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SimpleFInftyOvergroups.SemanticEncoding.IdempotentNames.instFintypeElemSubtypeEndSpaceMemSubalgebraAlgebraIndexOfFinite _root_.OAI.SimpleFInftyOvergroups.SemanticEncoding.IdempotentNames.instPrimcodableElemSubtypeEndSpaceMemSubalgebraAlgebraIndexOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SimpleFInftyOvergroups
open StageConstruction SourceEnlargement
open scoped Classical

structure SourceRingData (G : Type) [Group G] where
  R : Type
  [ringR : Ring R]
  [nontrivialR : Nontrivial R]
  [algebraR : Algebra (ZMod 2) R]
  φ : R →ₙ+* R
  φ_injective : Function.Injective φ
  binary : CompressedSplittings.BinaryData φ
  e : R
  e_idempotent : IsIdempotentElem e
  e_nonzero : e ≠ 0
  S : Double.Y (Q := Q R) (X := X R) → e_idempotent.Corner
  T : Double.Y (Q := Q R) (X := X R) → e_idempotent.Corner
  TS : ∀ y z, T y * S z = if y = z then 1 else 0
  ρ : Double.W (Q R) →* e_idempotent.Cornerˣ
  ρ_injective : Function.Injective ρ
  ρS : ∀ w y, (ρ w).val * S y = S (w • y)
  Tρ : ∀ w y, T y * (ρ w).val = T (w⁻¹ • y)
  A : Type
  [finiteA : Finite A]
  π : FreeAlgebra (ZMod 2) A →ₐ[ZMod 2] R
  π_surjective : Function.Surjective π
  rel : Set (FreeAlgebra (ZMod 2) A)
  rel_finite : rel.Finite
  ker_π : TwoSidedIdeal.ker π.toRingHom = TwoSidedIdeal.span rel
  g : G →* e_idempotent.Cornerˣ
  g_injective : Function.Injective g

def SourceRingProducerObligation : Prop :=
  ∀ (G : Type) [Group G], HasDecidableWordProblem G → Nonempty (SourceRingData G)

universe u

end SimpleFInftyOvergroups
end

end OAI
end


