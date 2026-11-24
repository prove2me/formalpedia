-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:11.515434+00:00
-- url     : https://prove2.me/theorems/cdb83d19-dbee-4d99-a5d2-592043647fac
-- title:
--   Lift Old Chart Monomial Mem Prime Compl
-- statement:
--   Definitions and structural lemmas for Lift Old Chart Monomial Mem Prime Compl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace SectionCycle
section Local
variable {S : Type*} [CommRing S]
end Local
section Cycle
variable {K : Type*} {κ : K → Type*} {R : Type*} [CommRing R]
end Cycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
section AddBlock
variable {P : ArithVariety n} (D : AddBlockData P)
variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
end AddBlock
end SectionCycle
end
end GroundTheory.Heights₂.Heights


