-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_SemistableReduction__SemistableReductionSt_184d2c70c106979e
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_SemistableReduction__SemistableReductionSt_184d2c70c106979e
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:02:53.75674+00:00
-- url     : https://prove2.me/theorems/fa3ff5b2-4562-5b73-9c58-429f20942878
-- title:
--   Semistable Reduction St
-- statement:
--   Definitions and structural lemmas for Semistable Reduction St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/SemistableReduction₂/SemistableReductionSt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Published
def SemistableReductionSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (P : Out.PolAV (Sp K)),
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (G : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G), IsSemiAbelian G ∧
        ∃ φ : pullback G.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶ P.A.left,
          IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G) P.A
            (spMap (IntermediateField.inclusion h).toRingHom) φ
namespace SemistableReductionSt
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
end SemistableReductionSt
end GlobalTheory.Published
end


