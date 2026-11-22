-- Prove2me | Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage
-- name    : Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:55.168126+00:00
-- url     : https://prove2.me/theorems/400b039b-fdaa-4f99-b178-05b29d2e7ff9
-- title:
--   Fundamental Domain Eq Preimage
-- statement:
--   Definitions and structural lemmas for Fundamental Domain Eq Preimage, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/FundamentalDomainEqPreimage.lean

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
namespace Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]
abbrev boxIco (ι : Type*) : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1
end Formalism.H


