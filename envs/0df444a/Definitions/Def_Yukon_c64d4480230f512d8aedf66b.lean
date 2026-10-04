-- Prove2me | Definitions.Def_Yukon_c64d4480230f512d8aedf66b
-- name    : Yukon_c64d4480230f512d8aedf66b
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T14:15:33.464376+00:00
-- url     : https://prove2.me/theorems/34ef6542-3a31-4308-a6b6-87ed589c9959
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberRetainedStage6811.lean
--
--   yukon-proof-operation:foundation-direct-0969db90700e7e682f5a136b9ce115e9faf1b6d65da6db425ddff5e8f6032926
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNmUzMGY4OTA0MTM3ZDgwMDU4NzFlZTRiMjhmNmVlZTgwMzk5M2ZiNGI1N2UyN2IzODU0NjQwNTUyMjExOTY1YiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTA5NjlkYjkwNzAwZTdlNjgyZjVhMTM2YjljZTExNWU5ZmFmMWI2ZDY1ZGE2ZGI0MjVkZGZmNWU4ZjYwMzI5MjYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9jNjRkNDQ4MDIzMGY1MTJkOGFlZGY2NmIiLCJ2IjoyfQ]

import Definitions.Def_Yukon_ca6ef1ca29b9483e7b8d8f20

import Definitions.Def_Yukon_1c9853f4364428ab76f81792

import Definitions.Def_Yukon_74ba13f07dc1a61561ec3e92



















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Concrete retained Stage integration: the original multiplicity-weighted
normal cuts and the new unweighted moving budget use the same source triple.
-/
namespace ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811
open scoped Classical BigOperators
open RCN002 RCN046 RCN057 RCN074 RCN084 RCN085 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTransportC2 LocatorHybridTailProvider
open BoundaryTailProvider CommonLinearChannels6807 MovingFiberThreeSources6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP K p] [CharP (GenericField K) p] {errorCap : ℕ}
local notation "Ω" => GenericField K

def rawFirstFlag (t y r : ℕ) : FlagDegree :=
  RCN198.center (cellA t y) (cellB y r) (cellS r) +
    w • (⟨cellA t y,cellB y r+1,cellS r+2⟩ : FlagDegree)

/-- H-free first-cut flag of the cell: `2(w+1)•flag(H) + 3•unitAll`. -/
def hfreeFirst (t y r : ℕ) : FlagDegree :=
  HFreeFirstSlice6812.hfreeFlag r (y-r) (t-y) unitAllFlag

/-- Direction `j` is charged `(scale/3)·mix(f,X,e_j) + 4(w+1)(scale/3d_j)·mix(f,e_j,V_j)`
(the H-free first cut), plus the unchanged moving term. -/
def numerator {F : MvPolynomial (Fin 4) K} (source : Fin 3 → Source F)
    (scale t y r : ℕ) (flag : FlagDegree) : ℕ :=
  scale/3*flagMixed flag (hfreeFirst t y r) (cellNormal t y r) +
    ∑ j : Fin 3, (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(source j).d))+
      65539*weight (rawFirstFlag t y r) j*(scale/(source j).d))*
      flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag




/-- The three slice directions of the retained stage (`linearZ/U/A` at the common `λ, μ`). -/
def channel {t y r : ℕ}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (cellSupport t y r))
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hflagChar : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hmixedRed : flagMixed flag (cellFirstTail t y r) unitZFlag < p) :
    Fin 3 → MvPolynomial (Fin 3) Ω :=
  let common := ReducedCommonLinear6807.original_common S hproper hflagChar hmixedRed
  ![CommonLinearChannels6807.linearZ,CommonLinearChannels6807.linearU common.lam,
    CommonLinearChannels6807.linearA common.mu common.lam]

/-- The H-free hypothesis for a retained stage: `HFreeChannel` (with `C0 = unitAll`) in
each of its three slice directions, over `AlgebraicClosure (RatFunc Ω)`. -/
def HFreeStage {t y r : ℕ}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (cellSupport t y r)) : Prop :=
  ∀ hproper hflagChar hmixedRed (j : Fin 3),
    HFreeFirstSlice6812.HFreeChannel (E := AlgebraicClosure (RatFunc Ω)) S.F
      (channel S hproper hflagChar hmixedRed j) unitAllFlag






end
end ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811


