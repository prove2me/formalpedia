-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:06.398324+00:00
-- url     : https://prove2.me/theorems/72096d2d-a485-4908-a0cf-12dc4377ed87
-- title:
--   Double Sum Eq Zero
-- statement:
--   Definitions and structural lemmas for Double Sum Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
namespace CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
def rem (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) : ∀ k, Finset (ι k) :=
  Function.update I p.1 ((I p.1).erase p.2)
variable (S : Type) [CommRing S] [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]
open Classical in

def ext (m : ℕ) (t : Cell K ι m → Ω) (J : ∀ k, Finset (ι k)) : Ω :=
  if h : (∀ l, (J l).Nonempty) ∧ ∑ l, ((J l).card - 1) = m then t ⟨J, h⟩ else 0
end CellDSq
end
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


