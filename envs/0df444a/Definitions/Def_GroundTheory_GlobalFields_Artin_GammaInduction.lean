-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_GammaInduction
-- name    : GroundTheory_GlobalFields_Artin_GammaInduction
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:47:30.201889+00:00
-- url     : https://prove2.me/theorems/f1da9834-0ca1-4416-8b86-c572c87a8c18
-- title:
--   Gamma Induction
-- statement:
--   Definitions and structural lemmas for Gamma Induction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/GammaInduction.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_IsProjEigenspaceNegOneOfMulSelfEqOne
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField NumberField.InfinitePlace IntermediateField Module GroundTheory.LocalField _root_.Complex
namespace GroundTheory.Global.Artin
section IndFun
variable {Γ Δ : Type*} [Group Γ] [Group Δ] [Fintype Γ] [Fintype Δ]
end IndFun
section Stabilizer
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
end Stabilizer
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
section Conj
end Conj
section Mackey
variable (w : InfinitePlace L)
end Mackey
section Character
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ Gal(L/fixedField H) V)
def charOnSubgroup (h : H) : ℂ :=
  ρ.character (fixedFieldMulEquiv H h)
end Character
section Gamma
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ Gal(L/fixedField H) V)
end Gamma
end GroundTheory.Global.Artin


