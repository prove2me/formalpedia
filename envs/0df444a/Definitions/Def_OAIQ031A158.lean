-- Prove2me | Definitions.Def_OAIQ031A158
-- name    : OAIQ031A158
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:45:43.098228+00:00
-- url     : https://prove2.me/theorems/7b82a1d6-f0fb-4970-bf28-84ec1e12325d
-- title:
--   Definitions bundle OAIQ031A158 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 1 definition and 2 theorems. The definitions and types are `OAI.ArExplicit.Resolution.inverseTwistScalarProof`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Ext_ATwistExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ATwistExt.lean), [`AuslanderReiten_Ext_TTensorTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorTwist.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A156` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A159`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A156

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorTwist
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : NoPositivePowerOne q)
include hq hq1 hp

theorem tTensorInverseTwist_scalar (n : ℕ) (x : tTensorCoefficients q (3*n)) :
    tTensorInverseTwist q H (3*n) x = (((H⁻¹ : kˣ) : k)^n) • x := by
  classical
  funext p
  by_cases hi : ∃ i, polynomialDiagonal n i=p
  · obtain ⟨i,rfl⟩ := hi
    exact tTensorInverseTwist_diagonal q H hq hq1 hp n i x
  · have hx := tTensorCoefficient_off_diagonal q hq hq1 hp n p hi (x p)
    rw [tTensorInverseTwist_apply]
    simp only [Pi.smul_apply, hx, map_zero, smul_zero]

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ATwistExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "T" => ArExplicit.T k q
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : NoPositivePowerOne q)
include hq hq1 hp

abbrev inverseTwistScalarProof (n : ℕ) (x : ASelfExt q (3*n)) :=
  ModuleBar.tensorTwist_scalar k T T (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (tInverseTwistExt q H) (tInverseTwistExt q H)
    (tInverseTwistExt_factor q H) (tInverseTwistExt_factor q H)
    (tTensorInverseTwist q H) (tTensorInverseTwist_apply q H)
    (3*n) (((H⁻¹ : kˣ) : k)^n) (tTensorInverseTwist_scalar q H hq hq1 hp n) x

theorem aInverseTwistExt_scalar (n : ℕ) (x : ASelfExt q (3*n)) :
    type_of% (inverseTwistScalarProof q H hq hq1 hp n x) :=
  inverseTwistScalarProof q H hq hq1 hp n x

end ArExplicit.Resolution

end

end OAI
end


