-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:53:13.220051+00:00
-- url     : https://prove2.me/theorems/ed72a2bf-0219-4016-bf6e-387979a1288c
-- title:
--   Forall Aeval Line Vanishing Ideal Iff
-- statement:
--   Definitions and structural lemmas for Forall Aeval Line Vanishing Ideal Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallAevalLineVanishingIdealIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
namespace GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
def lineVanishingIdeal {k : Type} [Field k] {N : ℕ} (y : Fin N → k) : Ideal (MvPolynomial (Fin N) k) :=
  (Ideal.homogeneousCore (homogeneousSubmodule (Fin N) k)
    (vanishingIdeal k (Submodule.span k {y} : Set (Fin N → k)))).toIdeal
end GlobalTheory.ChowHt


