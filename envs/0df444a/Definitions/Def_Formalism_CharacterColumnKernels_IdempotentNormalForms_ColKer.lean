-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:35.549354+00:00
-- url     : https://prove2.me/theorems/263beab2-3298-4bd5-b0c3-1cc5dcfb0a2c
-- title:
--   Col Ker
-- statement:
--   Definitions and structural lemmas for Col Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
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
namespace ColumnGeneratorDecomposition
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ι → ℕ}
abbrev fNu (l : ι) : ColFreeJ A r χ E ι j := colGenJ 0 l 1 0 0
abbrev fSig (l : ι) (a : Fin (j l)) : ColFreeJ A r χ E ι j := colGenJ 0 l 0 (Pi.single a 1) 0
abbrev fSig0 (l : ι) : ColFreeJ A r χ E ι j := colGenJ 0 l 0 0 1
variable {M : Type*} [AddCommGroup M] [Module A M]
end ColumnGeneratorDecomposition
open ColumnGeneratorDecomposition
end Formalism.NG


