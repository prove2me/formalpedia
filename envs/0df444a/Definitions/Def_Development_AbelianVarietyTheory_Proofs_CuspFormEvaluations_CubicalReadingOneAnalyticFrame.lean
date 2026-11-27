-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-27T05:00:07.233368+00:00
-- url     : https://prove2.me/theorems/2af4d5d2-467c-5b7d-b735-76465b2370f3
-- title:
--   Cubical Reading One Analytic Frame
-- statement:
--   Definitions and structural lemmas for Cubical Reading One Analytic Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CubicalReadingOneAnalyticFrame.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.CubeReading
def colsEquiv (n g : ℕ) : (Fin (n * g) → ℂ) ≃ₗ[ℂ] (Fin n → Fin g → ℂ) where
  toFun := colsOf n g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x k := x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv v := by
    funext k
    simp only [colsOf, Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv x := by
    funext i j
    simp only [colsOf, Equiv.symm_apply_apply]
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
  (Φ : AnFr A L x0 g)
def tri (x : Fin 3 → Fin g → ℂ) : Over.mk x0 ⟶ G3 A := lift (Φ.e (x 0)) (lift (Φ.e (x 1)) (Φ.e (x 2)))
def lat3 : AddSubgroup (Fin (3 * g) → ℂ) :=
  (AddSubgroup.pi Set.univ fun _ : Fin 3 => Φ.lat).comap (colsEquiv 3 g).toLinearMap.toAddMonoidHom
end GlobalTheory.CubeReading


