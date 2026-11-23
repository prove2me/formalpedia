-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreAnnApply
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreAnnApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:43.655804+00:00
-- url     : https://prove2.me/theorems/8c712c4f-2ae9-41be-87bf-102d35d79b63
-- title:
--   Cre Ann Apply
-- statement:
--   Definitions and structural lemmas for Cre Ann Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CreAnnApply.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
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
namespace GlobalTheory.CompanionTheory.GopEntries
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}
def sgR (i : NC ε) (A : Finset (NC ε)) : ℝ := (-1) ^ (A.filter fun j => key j < key i).card
def hh (i j : NC ε) (A B : Finset (NC ε)) : ℝ :=
  if i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j then sgR i (A.erase i) * sgR j (B.erase j) else 0
def coef (c d : Fin n) (i j : NC ε) : ℝ :=
  (if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) -
    (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0)
def gg (c d : Fin n) (A B : Finset (NC ε)) : ℝ := ∑ i : NC ε, ∑ j : NC ε, coef c d i j * hh i j A B
end GlobalTheory.CompanionTheory.GopEntries


