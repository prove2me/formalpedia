-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducible
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:40.472957+00:00
-- url     : https://prove2.me/theorems/6315ec41-719e-43ba-9957-91fb34fa44b0
-- title:
--   Separable Irreducible
-- statement:
--   Definitions and structural lemmas for Separable Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeparableIrreducible.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
noncomputable section
namespace GlobalTheory.CompanionTheory.FinRep
variable {Γ : Type} [Group Γ] [Fintype Γ]
def leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) : Representation ℂ Γ N where
  toFun g :=
    { toFun := fun n => MonoidAlgebra.of ℂ Γ g • n
      map_add' := smul_add _
      map_smul' := fun c n => smul_comm _ c n }
  map_one' := by
    ext n
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro n
    change MonoidAlgebra.of ℂ Γ (g * h) • n = MonoidAlgebra.of ℂ Γ g • MonoidAlgebra.of ℂ Γ h • n
    rw [map_mul, mul_smul]
instance finiteDimensional_leftIdeal (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) :
    FiniteDimensional ℂ N :=
  inferInstanceAs (FiniteDimensional ℂ (N.restrictScalars ℂ))
end GlobalTheory.CompanionTheory.FinRep


