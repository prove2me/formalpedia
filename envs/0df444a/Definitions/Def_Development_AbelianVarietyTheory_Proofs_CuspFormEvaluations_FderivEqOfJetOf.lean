-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T18:30:47.107328+00:00
-- url     : https://prove2.me/theorems/672dd927-910b-5dd3-adbd-8c47346efb1e
-- title:
--   Fderiv Eq Of Jet Of
-- statement:
--   Definitions and structural lemmas for Fderiv Eq Of Jet Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FderivEqOfJetOf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
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
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnVal.JetUniq
def renInv (n g m : ℕ) : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (n * g)) m :=
  jetMap (fun p => MvPolynomial.X ((0 : Fin 1), finProdFinEquiv p)) fun _ => X_mem_orig _
def colsL (n g : ℕ) : (Fin (n * g) → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ) where
  toFun := colsOf n g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end GlobalTheory.AnVal.JetUniq


