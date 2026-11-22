-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKerChiOne
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKerChiOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:57.157671+00:00
-- url     : https://prove2.me/theorems/15393d2d-f69a-4568-b0dc-6be54ac5c198
-- title:
--   Col Ker Chi One
-- statement:
--   Definitions and structural lemmas for Col Ker Chi One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKerChiOne.lean

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
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
namespace ColKerChi
open ColumnGeneratorDecomposition
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ι → ℕ}
  {M : Type*} [AddCommGroup M] [Module A M]
end ColKerChi
open ColumnGeneratorDecomposition ColKerChi
end Formalism.NG


