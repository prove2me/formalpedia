-- Prove2me | Definitions.Def_Yukon_1a92fd39ba829710bd7f764c
-- name    : Yukon_1a92fd39ba829710bd7f764c
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T07:58:12.172105+00:00
-- url     : https://prove2.me/theorems/20740e18-767d-418e-9c6c-73d174dbe65d
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailComponent.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailComponent.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailComponent.lean
--
--   yukon-proof-operation:foundation-direct-b127ab6a298257770702f9abafc9eac9aa10dbb9d780ab1d628d25963695a9a9
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMTg3ZWQ4MDk3YmUyZDI3NzdjOWI3ZmRiNGExNDg1Yjk3MjdmM2Q5Zjg1YzhkZDU4YjRlYjE5ZjE5ZTRiMDA4YiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWIxMjdhYjZhMjk4MjU3NzcwNzAyZjlhYmFmYzllYWM5YWExMGRiYjlkNzgwYWIxZDYyOGQyNTk2MzY5NWE5YTkiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8xYTkyZmQzOWJhODI5NzEwYmQ3Zjc2NGMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_f9834d5864a4621af5a0e925

import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailComponent
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open BoundaryTailAlgebra RCN057
set_option Elab.async false
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailComponent.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailComponent.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable [CharP K p]
variable {stageErrorCap : ℕ}

set_option maxHeartbeats 1000000 in
theorem component_moving_card_le_delay
    (t y r : Nat) (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (hchar : 2 * (w - 1) < p)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (C : FirstTailComponent S)
    (budget : MovingPoleBudget C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (base : SeparableLiteralCoordinate C.1)
    (delay : ℕ) (hdelay : 1 ≤ delay) (factor : ℕ)
    (hfactor : w + 1 + delay ≤ 2 * factor)
    (htail : globalTailCut (polynomialEmbedding K) S.F
      (w + 1 + delay) ∉ C.1) :
    (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      budget.weightedCost (BoundaryTailAlgebra.normalFlag (w - 1 + delay) r (y-r) (t-y)) +
        factor * budget.movingCost := by
  classical
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  have hs : cellS r + 2 = r := by dsimp [cellS]; omega
  have hys : cellB y r + cellS r + 3 = r + (y-r) := by
    dsimp [cellB, cellS]; omega
  have htot : cellA t y + cellB y r + cellS r + 3 = r + (y-r) + (t-y) := by
    dsimp [cellA, cellB, cellS]; omega
  have hR : WeightBound residualSWeights S.F (r : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualSWeights S.F ≤ r by
      simpa only [cellSupport, RCN198.support, hs] using Hsupport.s_weight)
  have hYR : WeightBound residualYSWeights S.F ((r + (y-r) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualYSWeights S.F ≤ r + (y-r) by
      simpa only [cellSupport, RCN198.support, hys] using Hsupport.ys_weight)
  have hAll : WeightBound residualTotalWeights S.F ((r + (y-r) + (t-y) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualTotalWeights S.F ≤ r + (y-r) + (t-y) by
      simpa only [cellSupport, RCN198.support, htot] using Hsupport.total_weight)
  have hHnot : regularitySurface (polynomialEmbedding K) S.F ∉ C.1 :=
    regularComponent_H_not_mem (GenericField K) S.G _ _ C
  have hfirst : globalTailCut (polynomialEmbedding K) S.F (w + 1) ∈ C.1 :=
    regularComponent_T_mem (GenericField K) S.G _ _ C
  have hzero : FiniteRegularZeroSetBound C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay))
      (budget.weightedCost (BoundaryTailAlgebra.normalFlag (w - 1 + delay) r (y-r) (t-y)) +
        factor * budget.movingCost) := by
    have hlevel : w - 1 + delay + 2 = w + 1 + delay := by norm_num [w]; omega
    have hfirstlevel : w - 1 + 2 = w + 1 := by norm_num [w]
    have hf : w - 1 + delay + 2 ≤ 2 * factor := by omega
    have hfirst0 : globalTailCut (polynomialEmbedding K) S.F (w-1+2) ∈ C.1 := by
      rw [hfirstlevel]
      exact hfirst
    have hlater0 : globalTailCut (polynomialEmbedding K) S.F (w-1+delay+2) ∉ C.1 := by
      rw [hlevel]
      exact htail
    have hz := BoundaryTailAlgebra.global_tail_zero_count C.1
      (polynomialEmbedding K) (polynomialEmbedding_injective K) S.F
      (w-1) (w-1+delay) r (y-r) (t-y) p factor
      (by norm_num [w]) (by norm_num [w]; omega) hchar hr3 (by omega)
      hf hR hYR hAll budget base hHnot hfirst0 hlater0
    rwa [hlevel] at hz
  let seeds := componentSeeds (GenericField K) S.G
    (globalTailCut (polynomialEmbedding K) S.F (w + 1))
    (regularitySurface (polynomialEmbedding K) S.F) Gamma
    (selectedPoint (polynomialEmbedding K) S.selected) C
  let pts : Finset (Fin 3 → GenericField K) :=
    seeds.image (selectedPoint (polynomialEmbedding K) S.selected)
  have hprime : ∀ v ∈ pts,
      C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C gamma hgamma
  have hHne : ∀ v ∈ pts, MvPolynomial.aeval v
      (regularitySurface (polynomialEmbedding K) S.F) ≠ 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    show MvPolynomial.eval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (regularitySurface (polynomialEmbedding K) S.F) ≠ 0
    exact (selectedPoint_evaluation (polynomialEmbedding K) S.selected gamma
      (MvPolynomial.pderiv (2 : Fin 4) S.F)).symm ▸ S.regular gamma hGamma
  have hAzero : ∀ v ∈ pts, MvPolynomial.aeval v
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    have hz : MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (globalTailCut (polynomialEmbedding K) S.F
          (w + 1 + delay)) = 0 :=
      selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
        S.selected gamma w (w + 1 + delay)
        (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
    exact hz
  have hbound : pts.card ≤
      budget.weightedCost (BoundaryTailAlgebra.normalFlag (w - 1 + delay) r (y-r) (t-y)) +
        factor * budget.movingCost :=
    hzero pts hprime hHne hAzero
  have hcard : pts.card = seeds.card :=
    Finset.card_image_of_injective seeds
      (selectedPoint_injective (polynomialEmbedding K) S.selected)
  show seeds.card ≤ _
  omega


end
end ProximityPrize.SubmissionLower.BoundaryTailComponent


