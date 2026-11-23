-- Prove2me | Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SubmoduleSlopeLowerOfFiltration
-- name    : Formalism_MonomialMeanResidues_MonomialMeanProofs_SubmoduleSlopeLowerOfFiltration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:38.08516+00:00
-- url     : https://prove2.me/theorems/08452cca-75f8-4dec-94ee-94fb042b13c7
-- title:
--   Submodule Slope Lower Of Filtration
-- statement:
--   Definitions and structural lemmas for Submodule Slope Lower Of Filtration, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SubmoduleSlopeLowerOfFiltration.lean

import Mathlib
import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
namespace Formalism.HermiteSiegelSlopes
open Formalism.HN
namespace GradedDegree
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
section Alg
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Alg
end GradedDegree
namespace FiltrationSlope
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end
end FiltrationSlope
namespace PositionDegree
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def unc (K σ κ : Type) [Field K] [NumberField K] : (σ → κ → K) →ₗ[𝓞 K] (σ × κ → K) where
  toFun g p := g p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def emb (K σ κ : Type) [Field K] [DecidableEq σ] (α : σ) : (κ → K) →ₗ[K] (σ × κ → K) where
  toFun x p := if p.1 = α then x p.2 else 0
  map_add' x y := by
    funext p
    by_cases h : p.1 = α <;> simp [h]
  map_smul' a x := by
    funext p
    by_cases h : p.1 = α <;> simp [h]
end PositionDegree
end Formalism.HermiteSiegelSlopes


