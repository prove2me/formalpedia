-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T13:11:56.557519+00:00
-- url     : https://prove2.me/theorems/d39e3128-51ac-4368-96e0-f80585a8eebe
-- title:
--   Extension Inter Subspace
-- statement:
--   Definitions and structural lemmas for Extension Inter Subspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExtensionInterSubspace.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
namespace Formalism.HermitianLatticeCounting.P
section Frob
open scoped Matrix.Norms.Frobenius
end Frob
noncomputable def n2 {N : ℕ} (v : Fin N → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)
section FrobG
open scoped Matrix.Norms.Frobenius
end FrobG
noncomputable def n2G {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)
end Formalism.HermitianLatticeCounting.P


