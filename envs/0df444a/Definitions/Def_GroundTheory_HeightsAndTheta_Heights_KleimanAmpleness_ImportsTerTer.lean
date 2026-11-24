-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsTerTer
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsTerTer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:00.774024+00:00
-- url     : https://prove2.me/theorems/55d6f4ab-6680-4f43-b51c-7d2c8c727735
-- title:
--   Imports Ter Ter
-- statement:
--   Definitions and structural lemmas for Imports Ter Ter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ImportsTerTer.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AmpleSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_ModelSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CellMeets
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
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)
def CellLocEval.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ),
    Nonempty (cellH S y γ n ≃ₗ[S] cechHc ι (quotPart S (mIdealOver S y)) γ n)
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


