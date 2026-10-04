-- Prove2me | Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8
-- name    : Yukon_470e6b3ad95913c90c8c44d8
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T02:57:29.097076+00:00
-- url     : https://prove2.me/theorems/b12a6baf-9a17-428d-978b-b62b85de6c96
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceCarrierField6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceCarrierField6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceCarrierField6814.lean
--
--   yukon-proof-operation:certificate-b56-71a8ef57bf0c1a0617c4cc5b32c847c86e4c90449fb6a52298181fd21874a869
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTA2NTRhZmJkN2I3OTljOTliMDMzNGE5ZTdmNGRmNjFkYWRkMWM2ZWM4NWMxOTM4NTA2NTU5ZWM3Njg0ZWQ5OSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni03MWE4ZWY1N2JmMGMxYTA2MTdjNGNjNWIzMmM4NDdjODZlNGM5MDQ0OWZiNmE1MjI5ODE4MWZkMjE4NzRhODY5IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fNDcwZTZiM2FkOTU5MTNjOTBjOGM0NGQ4IiwidiI6Mn0]

import Definitions.Def_Yukon_32972018b92a668e7c3a547c

















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The faithful field of the original four-variable carrier. Its kernel
is proved to be exactly (F), so the source alternative produces global
helper divisibility, not a root identity at a special closed point. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial SecondJetCoefficients SecondJetClearedHelper
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceCarrierZeros6814 RCN234 RCN156

variable {K : Type} [Field K]

instance carrierSpanPrime (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] :
    (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (Fact.out : Irreducible F).prime

abbrev CarrierRing (F : MvPolynomial (Fin 4) K) :=
  MvPolynomial (Fin 4) K ⧸ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))

abbrev CarrierField (F : MvPolynomial (Fin 4) K) := FractionRing (CarrierRing F)

def carrierMap (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] :
    MvPolynomial (Fin 4) K →+* CarrierField F :=
  (algebraMap (CarrierRing F) (CarrierField F)).comp (Ideal.Quotient.mk _)

theorem carrierMap_zero_iff (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (P : MvPolynomial (Fin 4) K) : carrierMap F P=0 ↔ F∣P := by
  change algebraMap (CarrierRing F) (CarrierField F) (Ideal.Quotient.mk _ P)=0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (CarrierRing F) (CarrierField F)),
    Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]

theorem carrierMap_self (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] :
    carrierMap F F=0 := (carrierMap_zero_iff F F).mpr (dvd_refl F)

instance carrierField_charP (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (p : ℕ) [CharP K p] : CharP (CarrierField F) p :=
  charP_of_injective_ringHom ((carrierMap F).comp MvPolynomial.C).injective p

theorem carrier_H_nonzero (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    [CharP K 2130706433] (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433) :
    carrierMap F (2*RCN313.polyH K F)≠0 := by
  have hh : carrierMap F (RCN313.polyH K F)≠0 := by
    intro hz
    exact RCN267.equation_not_dvd_R_derivative F 2130706433 hpos hsmall
      ((carrierMap_zero_iff F _).mp hz)
  rw [map_mul,map_ofNat]
  apply mul_ne_zero _ hh
  exact (CharP.cast_eq_zero_iff (CarrierField F) 2130706433 2).not.mpr (by decide)

theorem carrier_polynomial_nonzero
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (P : WholeSpaceCube6814.Poly (K := K)) (hP : P≠0) (cap : ℕ)
    (hshape : ∀ e ∈ P.support, e 1+e 2+e 3+e 4≤cap)
    (hF : cap<wt residualTotalWeights F) : (asS P).map (carrierMap F)≠0 := by
  have hh := SecondJetTotalAvoidance.leading_not_dvd P hP F cap hshape hF
  have hl : carrierMap F (asS P).leadingCoeff≠0 := by
    exact fun hz => hh.2 ((carrierMap_zero_iff F _).mp hz)
  exact (SecondJetCoefficientAvoidance.map_degree_preserved (asS P) (carrierMap F) hl).1








end
end ProximityPrize.SubmissionLower.MovingSourceCarrierField6814


