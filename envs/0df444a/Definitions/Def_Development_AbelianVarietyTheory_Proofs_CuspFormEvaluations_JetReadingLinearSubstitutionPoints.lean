-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:09.468802+00:00
-- url     : https://prove2.me/theorems/350427ce-1aeb-48da-82a5-cb2db95599b1
-- title:
--   Jet Reading Linear Substitution Points
-- statement:
--   Definitions and structural lemmas for Jet Reading Linear Substitution Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetReadingLinearSubstitutionPoints.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetLinSub
def flatL {n n' g : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) :
    (Fin (n' * g) → ℂ) →L[ℂ] (Fin (n * g) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v k => B (colsOf n' g v) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
      map_add' := fun v w => by
        funext k
        have : colsOf n' g (v + w) = colsOf n' g v + colsOf n' g w := rfl
        rw [this, map_add]; rfl
      map_smul' := fun c v => by
        funext k
        have : colsOf n' g (c • v) = c • colsOf n' g v := rfl
        rw [this, map_smul]; rfl }
section Main
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
end Main
end GlobalTheory.JetLinSub


