-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeylRowActionMemWeylLatticeSquare
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeylRowActionMemWeylLatticeSquare
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:56.6093+00:00
-- url     : https://prove2.me/theorems/49851a44-5494-44f4-974c-749a291f00d0
-- title:
--   Weyl Row Action Mem Weyl Lattice Square
-- statement:
--   Definitions and structural lemmas for Weyl Row Action Mem Weyl Lattice Square, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeylRowActionMemWeylLatticeSquare.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace GlobalTheory.WeylRowAll
def coeffMap {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R) (F : MvPolynomial σ S) :
    MvPolynomial σ R :=
  ∑ m ∈ F.support, monomial m (c (coeff m F))
def toInv (R : Type) [CommRing R] : Polynomial R →+* HahnSeries ℤ R :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1 : ℤ) (1 : R))
end GlobalTheory.WeylRowAll


