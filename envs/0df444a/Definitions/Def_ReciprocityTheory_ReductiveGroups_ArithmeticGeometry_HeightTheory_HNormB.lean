-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormB
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:46:17.78049+00:00
-- url     : https://prove2.me/theorems/9231660b-9798-4be5-9521-7b45df669520
-- title:
--   HNorm B
-- statement:
--   Definitions and structural lemmas for HNorm B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
namespace HNm
open IsDedekindDomain IsLocalRing
variable {R F L : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L]
variable (R F L) in

def OverR (p : Ideal R) : Set (AddValuation L (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ x : R, 0 ≤ w (algebraMap F L (algebraMap R F x)) ∧
    (0 < w (algebraMap F L (algebraMap R F x)) ↔ x ∈ p)}
variable (F) in

noncomputable def fz (w : AddValuation L (WithTop ℤ)) : ℕ :=
  letI := resAlg (F := F) w
  Module.finrank (ResidueField ((vRing w).comap (algebraMap F L))) (ResidueField (vRing w))
end HNm
end ReciprocityTheory.ChartRestriction.G.T0


