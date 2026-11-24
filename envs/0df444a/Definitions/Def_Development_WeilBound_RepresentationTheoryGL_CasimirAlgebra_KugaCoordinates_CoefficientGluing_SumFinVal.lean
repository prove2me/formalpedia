-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:11.281976+00:00
-- url     : https://prove2.me/theorems/6b39e900-a6e3-4011-bc0c-5b2e2d3f23ed
-- title:
--   Sum Fin Val
-- statement:
--   Definitions and structural lemmas for Sum Fin Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Formalism.REAL
open scoped TensorProduct
namespace PositivityTheory.Rg.Cz.CGlue
section Tens
variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]
def colAnti {C : Type} (col : P → C) : Submodule ℂ (TV n ℂ P) where
  carrier := {f | ∀ p p', col p = col p' → p ≠ p' → pm (Equiv.swap p p') f = -f}
  add_mem' := fun {f g} hf hg p p' h1 h2 => by rw [map_add, hf p p' h1 h2, hg p p' h1 h2, neg_add]
  zero_mem' := fun p p' _ _ => by simp
  smul_mem' := fun c f hf p p' h1 h2 => by rw [map_smul, hf p p' h1 h2, smul_neg]
variable {M : Type} [AddCommGroup M] [Module ℂ M] {d : ℕ}
def tmap (Jh : Matrix (Fin d) (P → Fin n) ℂ) : TV n M P →ₗ[ℂ] M ⊗[ℂ] (Fin d → ℂ) :=
  ∑ I, (TensorProduct.mk ℂ M (Fin d → ℂ)).flip (fun m => Jh m I) ∘ₗ LinearMap.proj I
end Tens
end PositivityTheory.Rg.Cz.CGlue


