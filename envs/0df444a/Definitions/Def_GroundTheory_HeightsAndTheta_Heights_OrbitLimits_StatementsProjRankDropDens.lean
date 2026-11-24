-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankDropDens
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankDropDens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:19.459976+00:00
-- url     : https://prove2.me/theorems/408ddc01-39cd-40b1-951f-3590f94832b3
-- title:
--   Statements Proj Rank Drop Dens
-- statement:
--   Definitions and structural lemmas for Statements Proj Rank Drop Dens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsProjRankDropDens.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
def ProjRankDropDens.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (V : Set R.X) (BV : FinHolAtlas n V),
    (∀ j, IsSmoothHerm (L j)) → HoloMap BV R.A Subtype.val →
    ∀ j, ∀ u ∈ (BV.chart j).target, ∀ p : (k : K) → ι k,
      (∀ k, R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0) →
      Module.finrank ℂ (LinearMap.range (fderiv ℂ
        (fun y => ReciprocityTheory.ChartRestriction.G.Geo.affCoord p
          (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm y).1)) u :
          (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) < n →
      locDens BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val) j u = 0
end GroundTheory.Heights₂.Heights.Targets


