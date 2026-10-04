-- Prove2me | Definitions.Def_Yukon_e1a1d0c7582a0e3bb14b33e7
-- name    : Yukon_e1a1d0c7582a0e3bb14b33e7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T19:13:42.214398+00:00
-- url     : https://prove2.me/theorems/a951204e-9e85-4eee-b650-f96214510591
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberRegularData6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberRegularData6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberRegularData6814.lean
--
--   yukon-proof-operation:certificate-split-bbd76044110c217c39776fe244de63594bce2f21bf25ba1c94459e53e12c2713
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODQzYTRhZjFmNjEwZjAzYjg5NTc5NTJmMjg3MmI0YTA0MTViZTU4YjgxODRkMTZmYTQ1ODA2MDAzN2ZlZGZlNyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LWJiZDc2MDQ0MTEwYzIxN2MzOTc3NmZlMjQ0ZGU2MzU5NGJjZTJmMjFiZjI1YmExYzk0NDU5ZTUzZTEyYzI3MTMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9lMWExZDBjNzU4MmEwZTNiYjE0YjMzZTciLCJ2IjoyfQ]

import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561

import Definitions.Def_Yukon_63a16e90b7724a1f71186e13

import Definitions.Def_Yukon_52f7c2cb3790c155905697c9

import Definitions.Def_Yukon_1024a69a825a921d7eaeaebc













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberRegularData6814
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN260 RCN174 RCN275 RCN327
open RCN156 RCN234 LocatorHybridCells LocatorHybridCellsC1 RCN130 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberRegularData6814.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberRegularData6814.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I

structure Data (nodes : I ↪ K) (u0 u1 : I → K) where
  D : ℕ
  t : ℕ
  y : ℕ
  r : ℕ
  Dlow : 131072 ≤ D
  Dchar : D < 2130706433
  tbound : t ≤ 7501
  ybound : y ≤ 142
  rbound : r ≤ 31
  rpos : 3 ≤ r
  ry : r+2 ≤ y
  yt : y+2 ≤ t
  F : MvPolynomial (Fin 4) K
  irreducible : Irreducible F
  rdegree : 0 < F.degreeOf 2
  box : F ∈ globalCoefficientBox K D w t r
  support : ResidualSupportData (cellSupport t y r) F
  selected : K → Polynomial K
  seeds : Finset K
  degree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w
  agreement : ∀ gamma ∈ seeds, 181255 ≤
    (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card
  solution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0
  regular : ∀ gamma ∈ seeds,
    specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0
  noPencil : NoLargeSelectedPencil selected seeds w 80889

namespace Data
variable {nodes : I ↪ K} {u0 u1 : I → K}

def restrict (S : Data nodes u0 u1) (Delta : Finset K) (hsub : Delta ⊆ S.seeds) :
    Data nodes u0 u1 :=
  { S with seeds := Delta
           degree := fun gamma h => S.degree gamma (hsub h)
           agreement := fun gamma h => S.agreement gamma (hsub h)
           solution := fun gamma h => S.solution gamma (hsub h)
           regular := fun gamma h => S.regular gamma (hsub h)
           noPencil := noLargeSelectedPencil_mono S.selected S.seeds Delta w 80889 hsub S.noPencil }

def pair (S : Data nodes u0 u1) (R capY T : ℕ) : UnequalParameters :=
  ⟨262144,131071,181255,S.y,S.r,S.t,capY,R,T⟩

def PairGates (S : Data nodes u0 u1) (R capY T : ℕ) : Prop :=
  (S.pair R capY T).mixedCost.y < 2130706433 ∧
  (S.pair R capY T).mixedCost.r < 2130706433 ∧
  (S.pair R capY T).mixedCost.z < 2130706433

theorem weights (S : Data nodes u0 u1) :
    wt residualSWeights S.F ≤ S.r ∧ wt residualYSWeights S.F ≤ S.y ∧
      wt residualTotalWeights S.F ≤ S.t := by
  have hs : cellS S.r+2 = S.r := by have := S.rpos; dsimp [cellS]; omega
  have hy : cellB S.y S.r+cellS S.r+3 = S.y := by have := S.ry; dsimp [cellB,cellS]; omega
  have ht : cellA S.t S.y+cellB S.y S.r+cellS S.r+3 = S.t := by
    have := S.yt; dsimp [cellA]; omega
  have h := S.support
  exact ⟨by simpa only [cellSupport,RCN198.support,hs] using h.s_weight,
    by simpa only [cellSupport,RCN198.support,hy] using h.ys_weight,
    by simpa only [cellSupport,RCN198.support,ht] using h.total_weight⟩

theorem proper_count_left (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (Q : MvPolynomial (Fin 4) K) (R capY T : ℕ) (hrel : IsRelPrime S.F Q)
    (hQ : Q.degreeOf 1 ≤ capY ∧ Q.degreeOf 2 ≤ R ∧ Q.degreeOf 3 ≤ T)
    (hgates : S.PairGates R capY T)
    (hzero : ∀ gamma ∈ S.seeds, specialization K (S.selected gamma) gamma Q=0) :
    S.seeds.card ≤ AsymmetricHelper.leftRegularCountCap (S.pair R capY T) := by
  have hF := SecondJetPairBounds.degree_caps_of_weights S.F S.r S.y S.t S.weights
  have hcount := SecondJetProperCounting.regular_seed_bound_left
    (S.pair R capY T) S.F Q S.irreducible S.rdegree hrel 2130706433
    hF.1 hF.2.1 hF.2.2 hQ.1 hQ.2.1 hQ.2.2 (by have := S.rpos; dsimp [pair]; omega)
    (by have := S.ybound; dsimp [pair]; omega)
    (by have := S.rbound; dsimp [pair]; omega)
    (by have := S.tbound; dsimp [pair]; omega)
    hgates.1 hgates.2.1 hgates.2.2 S.selected S.seeds Finset.univ nodes u0 u1
    nodes.injective.injOn (by simpa only [Finset.card_univ,pair] using hI)
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    S.degree S.agreement (by simpa only [pair,UnequalParameters.errors,
      (show (262144 - 181255 : ℕ) = 80889 by decide),RCN327.w] using S.noPencil)
    S.solution S.regular hzero
  exact SecondJetPairBounds.count_le_left_cap (S.pair R capY T) S.F hF.1 hF.2.1 hF.2.2
    S.seeds.card (by change 0 < (181255 - 131071 : ℕ); decide) hcount

end Data
end
end ProximityPrize.SubmissionLower.MovingFiberRegularData6814


