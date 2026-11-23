-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTraceZeroAdjustmentOfHermitianLattice
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTraceZeroAdjustmentOfHermitianLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:33:07.680156+00:00
-- url     : https://prove2.me/theorems/de8863c0-0e30-4330-bf84-18a5b12a966d
-- title:
--   Exists Trace Zero Adjustment Of Hermitian Lattice
-- statement:
--   Definitions and structural lemmas for Exists Trace Zero Adjustment Of Hermitian Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTraceZeroAdjustmentOfHermitianLattice.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMulVecMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
namespace GlobalTheory.TvAdjust
end GlobalTheory.TvAdjust


