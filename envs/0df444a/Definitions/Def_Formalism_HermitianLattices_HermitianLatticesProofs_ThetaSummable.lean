-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:08.556795+00:00
-- url     : https://prove2.me/theorems/e3189ee3-dbb2-4b00-bf6c-bb56997b7305
-- title:
--   Theta Summable
-- statement:
--   Definitions and structural lemmas for Theta Summable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Alg
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
end Alg
section Mat
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Mat
section Mat2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Mat2
section Main
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
end Main
end Formalism.HermitianLatticesTheory


