-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:25.330984+00:00
-- url     : https://prove2.me/theorems/934e3f0b-1cfa-4fcd-b859-bd9fa6c2956d
-- title:
--   Global Concrete Of
-- statement:
--   Definitions and structural lemmas for Global Concrete Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GlobalConcreteOf.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_DetTri
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_VccSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
namespace GlobalDeterminantRelations
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
  {d : Type} [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
  (x' : X')
instance : SMulCommClass R' (FractionRing O) (EvalSp O d R' x') where
  smul_comm r c v := by
    funext a
    change (∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (c * (v : d → FractionRing O) b)) =
      c * ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
instance : FiniteDimensional (FractionRing O) (EvalSp O d R' x') :=
  inferInstanceAs (FiniteDimensional (FractionRing O) (d → FractionRing O))
def curryE (g : Type) : (g × d → FractionRing O) ≃ₗ[FractionRing O] (g → EvalSp O d R' x') where
  toFun v i a := v (i, a)
  invFun w q := (w q.1 : d → FractionRing O) q.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
end GlobalDeterminantRelations
universe u v w
end Formalism.NG


