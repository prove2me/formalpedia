-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:18:24.8177+00:00
-- url     : https://prove2.me/theorems/9aa81db0-1bd7-436d-8b0d-abc6edd9a756
-- title:
--   Length Ker Of Det Eq Zero
-- statement:
--   Definitions and structural lemmas for Length Ker Of Det Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Matrix
noncomputable section
namespace Formalism.NG
namespace IdempotentNormalFormsLenFacts
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev AK (A : Matrix ι ι O) : Matrix ι ι (FractionRing O) := A.map (algebraMap O (FractionRing O))
def phi (A : Matrix ι ι O) : (ι → O) →ₗ[O] (ι → KO O) where
  toFun x i := Submodule.Quotient.mk (((AK A)⁻¹ *ᵥ (fun j => algebraMap O (FractionRing O) (x j))) i)
  map_add' x y := by
    ext i
    have : (fun j => algebraMap O (FractionRing O) (x j + y j)) =
        (fun j => algebraMap O (FractionRing O) (x j)) +
          (fun j => algebraMap O (FractionRing O) (y j)) := by
      ext j; simp
    simp only [Pi.add_apply]
    rw [this, Matrix.mulVec_add, Pi.add_apply, Submodule.Quotient.mk_add]
  map_smul' r x := by
    ext i
    have : (fun j => algebraMap O (FractionRing O) (r • x j)) =
        algebraMap O (FractionRing O) r • (fun j => algebraMap O (FractionRing O) (x j)) := by
      ext j; simp
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [this, Matrix.mulVec_smul, ← Submodule.Quotient.mk_smul]
    congr 1
    simp [Algebra.smul_def]
end IdempotentNormalFormsLenFacts
open IdempotentNormalFormsLenFacts
end Formalism.NG


