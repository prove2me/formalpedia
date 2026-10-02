-- Prove2me | Definitions.Def_Yukon_52f7c2cb3790c155905697c9
-- name    : Yukon_52f7c2cb3790c155905697c9
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T08:27:30.931839+00:00
-- url     : https://prove2.me/theorems/c029a1a3-f460-47ae-a6c5-d2648168484c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailProvider.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailProvider.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailProvider.lean
--
--   yukon-proof-operation:foundation-direct-6dcf44e8aef8d7afd2522dd49046376c28503c06fa37398cd1b274c55a11f321
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiN2FkOTU2MDEyYzBlZGZlZjUxOGEwOGJlYzIxNGExYzA0YjkxZGYxYzQ5MDMyODRjODYyYWFiZWU0ZTU0YzI4NiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTZkY2Y0NGU4YWVmOGQ3YWZkMjUyMmRkNDkwNDYzNzZjMjg1MDNjMDZmYTM3Mzk4Y2QxYjI3NGM1NWExMWYzMjEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81MmY3YzJjYjM3OTBjMTU1OTA1Njk3YzkiLCJ2IjoyfQ]

import Definitions.Def_Yukon_1a92fd39ba829710bd7f764c

import Definitions.Def_Yukon_2b53363ce911cc63f4bdfb1b














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailProvider
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
open BoundaryTailAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailProvider.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailProvider.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap : ℕ}

def cellNormal (t y r : ℕ) : FlagDegree :=
  BoundaryTailAlgebra.normalFlag w r (y-r) (t-y)

theorem exists_provider_on_active_components
    (t y r : Nat) (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (hchar : 2 * (w - 1) < p)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (tail1 : FlagDegree)
    (B : PrimeFlagBudgetFamily
      (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F
        (w + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F) flag tail1)
    (base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1)
    (budget : ∀ C : FirstTailComponent S,
      MovingPoleBudget C.1
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (hcost : ∀ C : FirstTailComponent S,
      (budget C).zCost = B.zCost C ∧ (budget C).yzCost = B.yzCost C ∧
        (budget C).allCost = B.allCost C)
    (active : Finset (FirstTailComponent S)) (movingTotal : ℕ)
    (hinactive : ∀ C : FirstTailComponent S, C ∉ active →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card = 0)
    (hmovingSum : (∑ C ∈ active, (budget C).movingCost) ≤ movingTotal)
    (hgate : stageErrorCap + 1 ≤ (cellNormal t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) * B.yzCost C)
    (hresultants : RegularComponentWeightedInertiaResultantCertificate B
      (fun C => localMultiplicity (loosenStageGeneral S)
        (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C)) :
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := tail1)
      (tailFlag2 := cellNormal t y r) S
      (flagMixed flag tail1 (cellNormal t y r) +
        65539 * movingTotal)) := by
  classical
  have hry : r < y := by omega
  have hr2 : 2 ≤ r := by omega
  let S0 := loosenStageGeneral S
  let multiplicity : FirstTailComponent S → ℕ := fun C =>
    localMultiplicity S0 (canonicalLocalDVRFamily S0 hfirstProper) C
  have hone : ∀ C, 1 ≤ multiplicity C :=
    loosenStageGeneral_one_le_localMultiplicity S hfirstProper
  have hwcEq : ∀ (C : FirstTailComponent S) (f : FlagDegree),
      (budget C).weightedCost f = B.weightedCost f C := by
    intro C f
    obtain ⟨hz, hy', ha⟩ := hcost C
    simp only [MovingPoleBudget.weightedCost,
      PrimeFlagBudgetFamily.weightedCost, hz, hy', ha]
  have hscale : ∀ (m : ℕ) (f : FlagDegree) (C : FirstTailComponent S),
      B.weightedCost (m • f) C = m * B.weightedCost f C := by
    intro m f C
    simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly, nsmul_yz,
      nsmul_all]
    ring
  have hnormal : ∀ C : FirstTailComponent S,
      B.weightedCost (cellHybridCoordinateC1 t y r) C ≤
        B.weightedCost (cellNormal t y r) C := by
    intro C
    unfold cellNormal
    rw [normalFlag_eq_cell t y r hr3 hb]
    apply weightedCost_mono B C
    all_goals simp only [add_zOnly, add_yz, add_all, nsmul_zOnly,
      nsmul_yz, nsmul_all, unitAllFlag]
    all_goals omega
  let cost : FirstTailComponent S → ℕ := fun C =>
    multiplicity C * B.weightedCost (cellNormal t y r) C +
      65539 * (budget C).movingCost
  have hcost_pointwise : ∀ C, cost C ≤
      multiplicity C * B.weightedCost (cellNormal t y r) C +
        65539 * (budget C).movingCost := fun _ => le_rfl
  have hbound : ∀ C,
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤ cost C := by
    intro C
    have dichotomy := local_order_tail_dichotomy S0
      (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
    rcases dichotomy.2 with hproper | htangentBranch
    · obtain ⟨delay, hdelay, hdelayMu, htail⟩ := hproper
      by_cases hm : 6 ≤ multiplicity C
      · have hzero : ∀ gamma ∈ componentSeeds (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (w + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C,
            MvPolynomial.aeval
              (selectedPoint (polynomialEmbedding K) S.selected gamma)
              (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) = 0 := by
          intro gamma hgamma
          have hGamma := componentSeeds_subset (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (w + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
          exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K)
            S.F S.selected gamma w (w + 1 + delay)
            (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
        have hflagMod : PolynomialInFlagMod C.1
            (multiplicity C • cellHybridCoordinateC1 t y r)
            (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
          refine ⟨globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay),
            laterTail_in_hybridFlagC1 t y r hr3 hry S delay
              (multiplicity C) hdelay hdelayMu hm, ?_⟩
          simp
        have hcount := component_secondTail_card_le_mod (Seed := K) B C Gamma
          (selectedPoint (polynomialEmbedding K) S.selected)
          (selectedPoint_injective (polynomialEmbedding K) S.selected)
          hflagMod htail hzero
        rw [hscale] at hcount
        exact hcount.trans ((Nat.mul_le_mul_left _ (hnormal C)).trans
          (Nat.le_add_right _ _))
      · have hdm : delay ≤ multiplicity C := hdelayMu
        have hcount := BoundaryTailComponent.component_moving_card_le_delay
          t y r hr3 hb hyt hchar S C (budget C) (base C) delay hdelay
          65539 (low_delay_factor delay (multiplicity C) hdm (by omega)) htail
        simp only [hwcEq] at hcount
        have hmono := normalFlag_delay_le_smul w (multiplicity C) delay r
          (y-r) (t-y) (by norm_num [w]) (hone C) hdm (by omega)
        have hcostle := weightedCost_mono B C hmono.1 hmono.2.1 hmono.2.2
        rw [hscale] at hcostle
        exact hcount.trans (Nat.add_le_add_right hcostle _)
    · have hcount := htangent C htangentBranch
      calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
        _ ≤ B.weightedCost (cellNormal t y r) C :=
          yzCost_mul_le_weightedCost B (cellNormal t y r) C
            (stageErrorCap + 1) hgate
        _ ≤ multiplicity C * B.weightedCost (cellNormal t y r) C := by
          simpa only [one_mul] using Nat.mul_le_mul_right
            (B.weightedCost (cellNormal t y r) C) (hone C)
        _ ≤ cost C := Nat.le_add_right _ _
  let activeCost : FirstTailComponent S → ℕ := fun C => if C ∈ active then cost C else 0
  have hactiveBound : ∀ C,
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤ activeCost C := by
    intro C
    by_cases hC : C ∈ active
    · simpa only [activeCost,if_pos hC] using hbound C
    · simp only [activeCost,if_neg hC,hinactive C hC,le_refl]
  have hsum : (∑ C, activeCost C) ≤
      flagMixed flag tail1 (cellNormal t y r) + 65539*movingTotal := by
    have ha : (∑ C, activeCost C) = ∑ C ∈ active, cost C := by simp only [activeCost,Finset.sum_ite_mem,Finset.univ_inter]
    rw [ha]
    calc
      (∑ C ∈ active, cost C) ≤
          ∑ C ∈ active, (multiplicity C *
            B.weightedCost (cellNormal t y r) C +
            65539*(budget C).movingCost) :=
        Finset.sum_le_sum (fun C _ => hcost_pointwise C)
      _ = (∑ C ∈ active, multiplicity C *
            B.weightedCost (cellNormal t y r) C) +
          65539*(∑ C ∈ active, (budget C).movingCost) := by
        rw [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ (∑ C, multiplicity C *
            B.weightedCost (cellNormal t y r) C) +
          65539*movingTotal :=
        Nat.add_le_add (Finset.sum_le_sum_of_subset (Finset.subset_univ active))
          (Nat.mul_le_mul_left _ hmovingSum)
      _ ≤ _ := Nat.add_le_add (hresultants.divisor_le B multiplicity) (le_refl _)
  have providerDichotomy := loosenStageGeneral_dichotomy_with_tangent S
    hfirstProper B htangent
  exact ⟨{
    budgetFamily := B
    multiplicity := multiplicity
    cost := activeCost
    one_le_multiplicity := hone
    tangentYZGate := hgate
    cost_sum_le := hsum
    componentBound := hactiveBound
    dichotomy := providerDichotomy }⟩


end
end ProximityPrize.SubmissionLower.BoundaryTailProvider


