-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TransExists
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TransExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:40.348156+00:00
-- url     : https://prove2.me/theorems/d3aa1be5-bade-49e5-841d-936e173834b3
-- title:
--   Trans Exists
-- statement:
--   Definitions and structural lemmas for Trans Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FoldingUnfolding/TransExists.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
namespace PI.FoldDCUnfold.W
universe u
def TransExists : Prop :=
  ∀ (G : Type u) [Group G] (K H : Subgroup G), H ≤ K → ∃ E : Set G, IsRightTransversal K H E
def TransIndep : Prop :=
  ∀ (G : Type u) [Group G] (Γ H : Subgroup G) (T T' : Set G),
    IsRightTransversal Γ H T → IsRightTransversal Γ H T' →
    ∀ c ∈ Γ, ∀ f : G → ℝ≥0∞, (∀ s ∈ H, ∀ y : G, f (s * y) = f y) →
      ∑' η : T, f ((η : G) * c) = ∑' η : T', f (η : G)
def TransProd : Prop :=
  ∀ (G : Type u) [Group G] (Γ S H : Subgroup G) (E D : Set G), H ≤ S → S ≤ Γ →
    IsRightTransversal S H E → IsRightTransversal Γ S D →
    Function.Injective (fun p : E × D => (p.1 : G) * (p.2 : G)) ∧
      IsRightTransversal Γ H (Set.range (fun p : E × D => (p.1 : G) * (p.2 : G)))
def DCTrans : Prop :=
  ∀ (G : Type u) [Group G] (Γ S S' : Subgroup G), S ≤ Γ → S' ≤ Γ →
    ∀ (R : Set G), IsDoubleTransversal Γ S S' R →
    ∀ (E : G → Set G), (∀ r ∈ R, IsRightTransversal S (stab S S' r) (E r)) →
      Function.Injective (fun p : (Σ r : R, E (r : G)) => (p.1 : G)⁻¹ * (p.2 : G)) ∧
        IsRightTransversal Γ S'
          (Set.range (fun p : (Σ r : R, E (r : G)) => (p.1 : G)⁻¹ * (p.2 : G)))
end PI.FoldDCUnfold.W


