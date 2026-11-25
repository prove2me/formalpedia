-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSmoothHermConstLine
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSmoothHermConstLine
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:28:57.175943+00:00
-- url     : https://prove2.me/theorems/53fa4403-5cf1-542a-b1e5-1336434bed10
-- title:
--   Is Smooth Herm Const Line
-- statement:
--   Definitions and structural lemmas for Is Smooth Herm Const Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSmoothHermConstLine.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
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
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def invLine (A : Geo.HermLine ι) : Geo.HermLine ι where
  a := -A.a
  h z := (A.h z)⁻¹
  pos z hz := inv_pos.mpr (A.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.neg_apply, zpow_neg]
def constLine (M : ℝ) (hM : 0 < M) : Geo.HermLine ι where
  a := 0
  h _ := M
  pos _ _ := hM
  smul c z hc := by simp
def powLine (A : Geo.HermLine ι) : ℕ → Geo.HermLine ι
  | 0 => constLine 1 one_pos
  | m + 1 => (powLine A m).tensor A
def chartMon (c : (k : K) → ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k
variable (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet


