-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:24:43.973704+00:00
-- url     : https://prove2.me/theorems/b245fac9-db52-4a2a-84e1-82f84791653b
-- title:
--   Len Coker Of Det Ne Zero
-- statement:
--   Definitions and structural lemmas for Len Coker Of Det Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LenCokerOfDetNeZero.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module IsDiscreteValuationRing Matrix
noncomputable section
namespace Formalism.NG
section HomQuotAux
variable {R O M NN : Type*} [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
  [SMulCommClass R O M] [AddCommGroup NN] [Module R NN] {g : Type} [Fintype g]
def evalGens (n : g → NN) : (NN →ₗ[R] M) →ₗ[O] (g → M) where
  toFun φ j := φ (n j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end HomQuotAux
section KerHomAux
variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {g d : Type} [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O)
def uncurryEquiv : (g → LatQ O d ρ) ≃ₗ[O] (g × d → KO O) where
  toFun v p := v p.1 p.2
  invFun w j b := w (j, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
variable [SMulCommClass R O (LatQ O d ρ)]
end KerHomAux
section LenCokerAux
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {ι : Type} [Fintype ι] [DecidableEq ι]
def dotLin (u : ι → O) : (ι → O) →ₗ[O] O where
  toFun x := u ⬝ᵥ x
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp [dotProduct_smul]
end LenCokerAux
end Formalism.NG


