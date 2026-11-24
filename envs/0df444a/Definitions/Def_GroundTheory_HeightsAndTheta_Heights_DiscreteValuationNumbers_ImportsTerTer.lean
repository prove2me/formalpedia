-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerTer
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerTer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:55.688734+00:00
-- url     : https://prove2.me/theorems/e74abafd-516d-44d0-8780-7f3c7e875868
-- title:
--   Imports Ter Ter
-- statement:
--   Definitions and structural lemmas for Imports Ter Ter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsTerTer.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)
def JoinPointFlagModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∃ (EB E'B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) N E)
      (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))
          EB E'B),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d ∧
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))) =
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O y ∧
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O y (ptCoord (Ω := Ω)) B EB ∧
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O y (ptCoord (Ω := Ω)) B' E'B ∧
        φ.deg = (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i)) ∧
        φ.deg' = (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i)) ∧
        φ.f = (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i)) ∧
        φ.g = (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
end GroundTheory.Heights₂.Heights.NumbersDVR


