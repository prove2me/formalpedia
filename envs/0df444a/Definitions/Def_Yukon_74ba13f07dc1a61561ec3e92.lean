-- Prove2me | Definitions.Def_Yukon_74ba13f07dc1a61561ec3e92
-- name    : Yukon_74ba13f07dc1a61561ec3e92
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T12:26:09.308757+00:00
-- url     : https://prove2.me/theorems/f70d060c-4975-4256-afde-712cf1e7ecb0
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeFirstSlice6812.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeFirstSlice6812.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeFirstSlice6812.lean
--
--   yukon-proof-operation:foundation-direct-a7d1b9494e7ed863e5fb639426d6080224677a6af9bc3a2903cebeb22075961a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNWQxOTFkMDBiOWY5ODhhYzY3MTA1ZDQ3MDhmNWQwZDdhYWE3Yjk4YzcwZTFmZDA4NmFhMWNmNzg4NGNjYTdmOCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWE3ZDFiOTQ5NGU3ZWQ4NjNlNWZiNjM5NDI2ZDYwODAyMjQ2NzdhNmFmOWJjM2EyOTAzY2ViZWIyMjA3NTk2MWEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83NGJhMTNmMDdkYzFhNjE1NjFlYzNlOTIiLCJ2IjoyfQ]

/-
H-free first cut. The only new input is `HFreeSliceBudget`; it replaces the
first-cut local pole bound, and everything else reuses the 6807 chain.
-/
import Definitions.Def_Yukon_0359be1f05b61e82bcf20b8e















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.HFreeFirstSlice6812
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000
local notation "w" => RCN326.w

/-- The H-free first-cut flag: `2(w+1)` copies of the flag `⟨z,v,r-1⟩` of `H = ∂F/∂Y'`
(`boundary_surfaceMap_flags`) and `3` copies of the constant flag `C0`. -/
def hfreeFlag (r v z : ℕ) (C0 : FlagDegree) : FlagDegree :=
  (2*(w+1)) • (⟨z,v,r-1⟩ : FlagDegree) + 3 • C0

section Slice
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

/-- **The H-free per-slice pole budget (hypothesis).**
`C` is a prime of `E[Y,Y',Γ]` (coordinates `0,1,2`) with function field
`L = CoordinateField E C`; `ν` ranges over `Place E L` (normalized valuations of `L`
trivial on `E`); `ev = coefficientMap phi C`; `H = ev (∂F/∂Y')`, `G = ev (polyG F)`.
With `τ = ev (baseNumerator F (w-1)) / H^(2w-1)` (`= Y^(w+1)`), for every finite `W`:
`3·Σ_{ν∈W} pole_ν τ ≤ Σ_{ν∈W} [(w+1)·(4·T_ν + 2·zero_ν H) + 3·flagPole_ν C0]`,
where `pole_ν = RCN187.poleOrder` (`max 0 (log ν ·)`), `T_ν = RCN064.movingPoleTarget`
`= max (2·max(p Y, p Y', p Γ)) (max(p Y, p Γ) + p(G/H))`, and
`zero_ν H = RCN026.zeroOrder = max 0 (ord_ν H)`.
It is the per-place bound `3·pole_ν τ ≤ (w+1)(4T_ν + 2 ord⁺_ν H) + 3c_ν`,
`c_ν ≤ flagPole_ν C0`, summed over `W`. -/
structure HFreeSliceBudget (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (C0 : FlagDegree) : Prop where
  pole_le : ∀ W : Finset (Place E (CoordinateField E C)),
    3 * (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
    ∑ nu ∈ W, (((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) nu +
        2*RCN026.zeroOrder E (CoordinateField E C) nu
          (SecondJetComponentRoots.coefficientMap phi C (polyH K F))) +
      3*flagPole nu.val (coordinate E C) C0)




end Slice

section Stage
variable {K I E T : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance  _root_.ProximityPrize.SubmissionLower.HFreeFirstSlice6812.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.HFreeFirstSlice6812.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "φE" => RingHom.comp (algebraMap (GenericField K) E) (polynomialEmbedding K)




variable [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

/-- The H-free hypothesis for one slice direction `ell`: every prime slice component
`D ∋ F, T-ell` with `H ∉ D` carries an `HFreeSliceBudget`. -/
def HFreeChannel (F : MvPolynomial (Fin 4) K) (ell : MvPolynomial (Fin 3) Ω)
    (C0 : FlagDegree) : Prop :=
  ∀ (D : Ideal PE) [D.IsPrime], SeparableLiteralCoordinate D →
    surfaceMap φE F ∈ D → GenericSlicePoints6807.sliceEquation (E := E) ell ∈ D →
    surfaceMap φE (polyH K F) ∉ D → HFreeSliceBudget φE F D C0




end Stage
end
end ProximityPrize.SubmissionLower.HFreeFirstSlice6812


