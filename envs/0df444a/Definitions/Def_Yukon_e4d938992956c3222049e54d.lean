-- Prove2me | Definitions.Def_Yukon_e4d938992956c3222049e54d
-- name    : Yukon_e4d938992956c3222049e54d
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T01:02:59.312991+00:00
-- url     : https://prove2.me/theorems/b88b556c-4d4e-4c2c-9d4a-9909dec0320e
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberCarrier6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberCarrier6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberCarrier6814.lean
--
--   yukon-proof-operation:certificate-tail-9f0f8b11bb5765654c38fbf0d777e928f47266990166d32d113282b4239cd919
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiM2NiYWY2ZTczMjIyNTc5YzU1YjZjYjJlODUwOTQxYzk2YzgwNWU0ZGVmYjRjNWU0NTY3NDQxOGI4NDg4NTZhMiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXRhaWwtOWYwZjhiMTFiYjU3NjU2NTRjMzhmYmYwZDc3N2U5MjhmNDcyNjY5OTAxNjZkMzJkMTEzMjgyYjQyMzljZDkxOSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2U0ZDkzODk5Mjk1NmMzMjIyMDQ5ZTU0ZCIsInYiOjJ9]

import Definitions.Def_Yukon_4efd06295acbeb3daeb2e9ed





































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberCarrier6814

open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open LocatorHybridCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def Active (g : Fin 21) (p : FlagDegree) : Prop :=
  3 ≤ p.all ∧ 2 ≤ p.yz ∧ 3 ≤ p.zOnly ∧ MovingFiberCount6814.sourceLimit g < p.all+p.yz+p.zOnly

def ledgerCap (g : Fin 21) (p : FlagDegree) : ℕ :=
  MovingFiberCount6814.roundedCaps g (p.all-3) (p.yz-2) p.zOnly

section Carrier
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberCarrier6814.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberCarrier6814.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I

/-- Build the retained-profile context from the carrier's actual cumulative
weights, restricting neither the source box nor the selected solution set. -/
def ofCarrier (D L s : ℕ) (F : MvPolynomial (Fin 4) K)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hF : Irreducible F) (hrdegree : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w L s)
    (ht : wt residualTotalWeights F ≤ 7501) (hy : wt residualYSWeights F ≤ 142)
    (hr : wt residualSWeights F ≤ 31)
    (h3 : 3 ≤ wt residualSWeights F)
    (hry : wt residualSWeights F+2 ≤ wt residualYSWeights F)
    (hyt : wt residualYSWeights F+2 ≤ wt residualTotalWeights F)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ seeds, 181255 ≤
      (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0)
    (hregular : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0)
    (hno : NoLargeSelectedPencil selected seeds w 80889) :
    MovingFiberRegularData6814.Data nodes u0 u1 where
  D := D
  t := wt residualTotalWeights F
  y := wt residualYSWeights F
  r := wt residualSWeights F
  Dlow := hDlow
  Dchar := hDchar
  tbound := ht
  ybound := hy
  rbound := hr
  rpos := h3
  ry := hry
  yt := hyt
  F := F
  irreducible := hF
  rdegree := hrdegree
  box := by
    intro e he
    have hs := MvPolynomial.le_weightedTotalDegree residualSWeights he
    have ht := MvPolynomial.le_weightedTotalDegree residualTotalWeights he
    simp only [RCN081.weight_fin4,residualSWeights,residualTotalWeights,Fin.isValue,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Nat.mul_zero,Nat.mul_one,
      Nat.zero_add,Nat.add_zero] at hs ht
    change e 1+e 2+e 3 ≤ wt residualTotalWeights F at ht
    exact ⟨by omega,hs,(hbox he).2.2⟩
  support := by
    constructor <;> dsimp only [cellSupport,RCN198.support,cellA,cellB,cellS] <;> omega
  selected := selected
  seeds := seeds
  degree := hdegree
  agreement := hagreement
  solution := hsolution
  regular := hregular
  noPencil := hno

theorem carrier_count_le_ledger (g : Fin 21) (D L s : ℕ) (F : MvPolynomial (Fin 4) K)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hF : Irreducible F) (hrdegree : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w L s)
    (ht : wt residualTotalWeights F ≤ 7501) (hy : wt residualYSWeights F ≤ 142)
    (hr : wt residualSWeights F ≤ 31)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ seeds, 181255 ≤
      (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0)
    (hregular : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0)
    (hno : NoLargeSelectedPencil selected seeds w 80889)
    (hI : Fintype.card I=262144)
    (ha : Active g (originalCumulativeFlag F)) :
    seeds.card ≤ ledgerCap g (originalCumulativeFlag F) := by
  let p := originalCumulativeFlag F
  have ha' : 3 ≤ p.all ∧ 2 ≤ p.yz ∧ 3 ≤ p.zOnly ∧
      MovingFiberCount6814.sourceLimit g < p.all+p.yz+p.zOnly := ha
  have h3 : 3 ≤ wt residualSWeights F := ha'.1
  have hry : wt residualSWeights F+2 ≤ wt residualYSWeights F := by
    have hv : 2 ≤ wt residualYSWeights F-wt residualSWeights F := ha'.2.1
    omega
  have hyt : wt residualYSWeights F+2 ≤ wt residualTotalWeights F := by
    have hz : 3 ≤ wt residualTotalWeights F-wt residualYSWeights F := ha'.2.2.1
    omega
  have htotal : p.all+p.yz+p.zOnly = wt residualTotalWeights F := by
    change wt residualSWeights F+(wt residualYSWeights F-wt residualSWeights F)+
      (wt residualTotalWeights F-wt residualYSWeights F) = wt residualTotalWeights F
    omega
  let S := ofCarrier D L s F hDlow hDchar hF hrdegree hbox ht hy hr h3 hry hyt
    selected seeds hdegree hagreement hsolution hregular hno
  have hown : MovingFiberArithmeticBase6814.Own S := rfl
  have hL : MovingFiberCount6814.sourceLimit g < S.t := by
    change MovingFiberCount6814.sourceLimit g < wt residualTotalWeights F
    rw [← htotal]
    exact ha'.2.2.2
  exact MovingFiberCount6814.count_group S hI hown g hL




end Carrier
end
end ProximityPrize.SubmissionLower.MovingFiberCarrier6814


