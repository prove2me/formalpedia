-- Prove2me | Definitions.Def_OAIQ031A090
-- name    : OAIQ031A090
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:28:55.569984+00:00
-- url     : https://prove2.me/theorems/089219d8-16ce-4b5f-9318-f9cd6fc0801f
-- title:
--   Definitions bundle OAIQ031A090 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 1 definition, 2 instances and 1 theorem. The definitions and types are `OAI.ArExplicit.TriangularModule.coordinateLinearEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Stable_StableExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableExt.lean), [`AuslanderReiten_Triangular_TriangularModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularModule.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A064` and `OAIQ031A075` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A117`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A064
import Definitions.Def_OAIQ031A075

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ}
variable {N : Type u} [AddCommGroup N] [Module R N]

theorem positiveExtVanish_of_stableCokernels (hP : TotallyAcyclicComplex P)
    (h : ∀ n : ℕ, Subsingleton (StableHom R (Cokernel P ((n + 1 : ℕ) : ℤ)) N)) :
    PositiveExtVanish R (Cokernel P 0) N := by
  apply (positiveExtVanish_iff_completeResolution R (Cokernel P 0) N P
    hP.projective hP.exactAt (LinearEquiv.refl R _)).mpr
  intro n f hf
  have hi : ((n + 1 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) := by omega
  have hf' : f.comp (P.d (((n + 1 : ℕ) : ℤ) + 1) ((n + 1 : ℕ) : ℤ)).hom = 0 := by
    rw [hi]
    exact hf
  have := h n
  have hz : StableHom.classOf R _ N (completeExtCocycleMap ((n + 1 : ℕ) : ℤ) f hf') = 0 :=
    Subsingleton.elim _ _
  have hgex := (completeExtCocycleMap_stable_zero_iff hP _ f hf').mp hz
  have hn : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
  rw [hn] at hgex
  obtain ⟨g, hg⟩ := hgex
  exact ⟨g, hg.symm⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable (k R F M N : Type*) [CommRing k] [Ring R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [AddCommGroup N] [Module R N]

namespace TriangularModule

variable {k R F M N}
variable (φ : BalancedTensor k R F M →ₗ[R] N)

section Scalars

variable [Module k N]

variable [Algebra k R] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k Rᵐᵒᵖ F]
variable [IsScalarTower k R M] [IsScalarTower k R N]

instance instSMulCommClassTriangular [SMulCommClass k R M] [SMulCommClass k R N] :
    SMulCommClass k (Triangular R F) (TriangularModule k R F M N φ) where
  smul_comm c a x := by
    ext
    · exact smul_comm c a.top x.top
    · simp only [bottom_scalar, bottom_smul, top_scalar, BalancedTensor.tmul_scalar,
        LinearMap.map_smul_of_tower, smul_add, smul_comm c a.bottom]

def coordinateLinearEquiv : TriangularModule k R F M N φ ≃ₗ[k] M × N :=
  (coordinateAddEquiv φ).linearEquiv k

instance instFinite [Module.Finite k M] [Module.Finite k N] :
    Module.Finite k (TriangularModule k R F M N φ) :=
  Module.Finite.equiv (coordinateLinearEquiv φ).symm

end Scalars

end TriangularModule
end ArExplicit

end OAI
end


