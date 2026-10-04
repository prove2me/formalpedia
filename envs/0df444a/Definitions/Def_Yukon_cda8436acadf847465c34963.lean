-- Prove2me | Definitions.Def_Yukon_cda8436acadf847465c34963
-- name    : Yukon_cda8436acadf847465c34963
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T06:19:29.488529+00:00
-- url     : https://prove2.me/theorems/8b6902b0-4821-401e-be1f-0a55ef2e055d
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceWholeCount6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceWholeCount6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceWholeCount6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-497ffd4e6713af10801c28081c588d5628cd0448a048047725536cd88293aba3
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYTY4ZGIxN2MxYTNlZTEwMjQ5OTFkNmM2MTk1MzEwYTE2MzI2YWRkZjM2ZGFlOWRjNmQyOTEwOGM0MTNmNjQ4MyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtNDk3ZmZkNGU2NzEzYWYxMDgwMWMyODA4MWM1ODhkNTYyOGNkMDQ0OGEwNDgwNDc3MjU1MzZjZDg4MjkzYWJhMyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2NkYTg0MzZhY2FkZjg0NzQ2NWMzNDk2MyIsInYiOjJ9]

import Definitions.Def_Yukon_9ee250b49ffcc1fbd0a8d65b


















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The actual retained Z-source and the whole-carrier proper pair feed
one isolated-point count. There is no per-geometric-factor budget charge. -/
namespace ProximityPrize.SubmissionLower.MovingSourceWholeCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN002 RCN046 RCN084 RCN095 RCN135 RCN136 RCN207 RCN234 RCN156 RCN341
open MovingSourceWholeCarrier6814 MovingSourceGeometricBudget6814 MovingSourceCarrierField6814
open MovingSourceRegularRestriction6814 MovingFiberThreeSources6811
open WholeSpaceCube6814 WholeSpaceCubeUniform6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))

def WholePointBound (F : MvPolynomial (Fin 4) K) (S : Source F) (p : FlagDegree)
    (quadratic A : MvPolynomial (Fin 3) Omega) : Prop :=
  ∀ (W : FlagDegree) (cut : MvPolynomial (Fin 3) OmegaT), PolynomialInFlag W cut →
    ∀ points : Finset (Fin 3 → OmegaT),
      (∀ x ∈ points, MvPolynomial.eval x (wholeCarrier F)=0) →
      (∀ x ∈ points, MvPolynomial.eval x (regularEquation F quadratic A)=0) →
      (∀ x ∈ points, MvPolynomial.eval x (regularDenominator F A*S.leading phi)≠0) →
      (∀ x ∈ points, MvPolynomial.aeval x cut=0) →
      (∀ x ∈ points, IsolatedPoint (wholeCarrier F) (regularEquation F quadratic A) cut x) →
      7*points.card≤W.zOnly*flagMixed p unitZFlag ⟨3252,132,51⟩+
        7*(W.yz*25470+W.all*88560)

theorem wholePointBound_of_projection [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (S : Source F) (hd : S.d=7) (hs : S.flag=⟨3252,132,51⟩) (hk : S.k=6)
    (p : FlagDegree) (hp : PolynomialInFlag p (wholeCarrier F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433)
    (U T : ℕ) (hU : 25≤U) (hUmax : U≤30) (hUT : U≤T) (hT : T≤331)
    (quadratic A : MvPolynomial (Fin 3) Omega)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (base : ∀ C : WholeMovingFamily F quadratic A, SeparableLiteralCoordinate C.1)
    (unit : AdaptiveUnitProjectionFamily base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩) :
    WholePointBound F S p quadratic A := by
  intro W cut hcut points hG hM hregular hzero hisolated
  have hne : wholeCarrier F≠0 := by
    intro hz
    exact hF (wholeCarrier_injective (by simpa only [wholeCarrier,map_zero] using hz))
  have hHdiv : surfaceMap phi (RCN313.polyH K F)∣regularDenominator F A := by
    apply dvd_mul_of_dvd_left
    rw [map_mul]
    exact dvd_mul_left _ _
  have h2 : (2 : OmegaT)≠0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
  have hfact : (S.k.factorial : OmegaT)≠0 := by
    rw [hk]
    exact SecondJetOwnShape.factorial_ne 6 (by omega)
  have hb := restricted_source_point_count phi F S (wholeCarrier F) p hne (dvd_refl _) hp
    2130706433 hunit h2 hfact (lift quadratic) (lift A) (initialCoordinate Omega)
    (inFlag_map _ hquadratic) (inFlag_map _ hA) (regularDenominator F A) hHdiv
    base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ unit W cut hcut points hG hM hregular hzero hisolated
  rw [hd,hs] at hb
  have hc := MovingSourcePrimeFamily6814.source_pair_directional_prices U T hU hUmax hUT hT
  exact hb.trans (Nat.add_le_add le_rfl (Nat.mul_le_mul_left 7
    (Nat.add_le_add (Nat.mul_le_mul_left W.yz hc.2.1) (Nat.mul_le_mul_left W.all hc.2.2))))








end
end ProximityPrize.SubmissionLower.MovingSourceWholeCount6814


