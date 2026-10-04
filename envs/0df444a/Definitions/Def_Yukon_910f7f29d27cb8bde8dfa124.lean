-- Prove2me | Definitions.Def_Yukon_910f7f29d27cb8bde8dfa124
-- name    : Yukon_910f7f29d27cb8bde8dfa124
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T12:10:00.584557+00:00
-- url     : https://prove2.me/theorems/e9c6d9c6-9082-4616-9211-9622079a21de
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.CommonLinearChannels6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.CommonLinearChannels6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/CommonLinearChannels6807.lean
--
--   yukon-proof-operation:foundation-direct-6b1bde0fd7abff82a9542dcb6e818e5739bd2e6f06d2d841fdfe9b7ce0cd033e
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODlhODYwNzQzNzA5ZGIxOTFmNGUzOWVhMTE5YjhmZTZiNjg4NDZkZGJiMmQ5OWQ1MzBmZWQxN2UzNzc2MmY5ZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTZiMWJkZTBmZDdhYmZmODJhOTU0MmRjYjZlODE4ZTU3MzliZDJlNmYwNmQyZDg0MWZkZmU5YjdjZTBjZDAzM2UiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85MTBmN2YyOWQyN2NiOGJkZThkZmExMjQiLCJ2IjoyfQ]

import Definitions.Def_Yukon_9bc6354a39244d128eafc24b

/-
UNCOMPILED. Structural common-linear-coordinate data for the SAME original unit
family. These are equalities of rational functions, not requested cost bounds.
-/














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.CommonLinearChannels6807
open scoped Classical BigOperators
open RCN002 RCN022 RCN030 RCN037 RCN038 RCN040 RCN042 RCN046 RCN093
open RCN095 RCN207 RCN237 RCN264 RCN340 RCN341 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 40000
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
local notation "Poly" => MvPolynomial (Fin 3) Ω

def linearZ : Poly := MvPolynomial.X 2
def linearU (lam : Ω) : Poly := MvPolynomial.X 0 + MvPolynomial.C lam * MvPolynomial.X 2
def linearA (mu lam : Ω) : Poly := MvPolynomial.X 1 +
  MvPolynomial.C mu * MvPolynomial.X 0 + MvPolynomial.C (mu*lam) * MvPolynomial.X 2

public theorem inFlag_X (i : Fin 3) (q : FlagDegree)
    (hi : InFlag q (Finsupp.single i 1)) : PolynomialInFlag q (MvPolynomial.X i : Poly) := by
  intro e he
  have hh : e = Finsupp.single i 1 := by simpa only [MvPolynomial.support_X,Finset.mem_singleton] using he
  subst e
  exact hi
public theorem inFlag_add_poly {q : FlagDegree} {A B : Poly}
    (hA : PolynomialInFlag q A) (hB : PolynomialInFlag q B) : PolynomialInFlag q (A+B) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hA e h
  · exact hB e h
public theorem inFlag_const_mul {q : FlagDegree} {A : Poly}
    (c : Ω) (hA : PolynomialInFlag q A) : PolynomialInFlag q (MvPolynomial.C c * A) := by
  intro e he
  rw [← MvPolynomial.smul_eq_C_mul] at he
  exact hA e (MvPolynomial.support_smul he)

theorem linearZ_in_flag : PolynomialInFlag unitZFlag (linearZ : Poly) := by
  exact inFlag_X 2 unitZFlag (by simp [InFlag,unitZFlag,Finsupp.single_apply])
theorem linearU_in_flag (lam : Ω) : PolynomialInFlag unitYZFlag (linearU lam) := by
  exact inFlag_add_poly
    (inFlag_X 0 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply]))
    (inFlag_const_mul lam (inFlag_X 2 unitYZFlag (by simp [InFlag,unitYZFlag,Finsupp.single_apply])))
theorem linearA_in_flag (mu lam : Ω) : PolynomialInFlag unitAllFlag (linearA mu lam) := by
  exact inFlag_add_poly (inFlag_add_poly
    (inFlag_X 1 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))
    (inFlag_const_mul mu (inFlag_X 0 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply]))))
    (inFlag_const_mul (mu*lam) (inFlag_X 2 unitAllFlag (by simp [InFlag,unitAllFlag,Finsupp.single_apply])))

theorem eval_linearU (P : Ideal Poly) [P.IsPrime] (lam : Ω) :
    coordinateEvaluation Ω P (linearU lam) = affineU Ω P lam := by
  rw [coordinateEvaluation_eq_aeval]
  simp only [linearU,affineU,Algebra.smul_def,map_add,map_mul,
    MvPolynomial.aeval_X,MvPolynomial.aeval_C]
theorem eval_linearA (P : Ideal Poly) [P.IsPrime] (mu lam : Ω) :
    coordinateEvaluation Ω P (linearA mu lam) = affineV Ω P mu (mu*lam) := by
  rw [coordinateEvaluation_eq_aeval]
  simp only [linearA,affineV,Algebra.smul_def,map_add,map_mul,
    MvPolynomial.aeval_X,MvPolynomial.aeval_C]

variable {G T H : MvPolynomial (Fin 3) Ω} {p q : FlagDegree}
  {base : ∀ C : RegularComponent Ω G T H, SeparableLiteralCoordinate C.1}

/-- A generic AdaptiveUnitProjectionFamily alone does NOT imply this structure.
The constructor below is for the original common activeNestedUnitFamily only. -/
structure CommonLinearValues
    (unit : AdaptiveUnitProjectionFamily (Omega := Ω) (G := G) (T := T) (H := H) base p q) where
  lam : Ω
  mu : Ω
  yzValue : ∀ C : RegularComponent Ω G T H,
    coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) = affineU Ω C.1 lam
  allValue : ∀ C : RegularComponent Ω G T H,
    coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) = affineV Ω C.1 mu (mu*lam)

theorem common_z_value (unit : AdaptiveUnitProjectionFamily base p q)
    (C : RegularComponent Ω G T H) :
    coordinateValue Ω (CoordinateField Ω C.1) (unit.zProjection C) =
      coordinateEvaluation Ω C.1 (linearZ : Poly) := unit.zValue C

theorem common_u_value (unit : AdaptiveUnitProjectionFamily base p q)
    (D : CommonLinearValues unit) (C : RegularComponent Ω G T H) :
    coordinateValue Ω (CoordinateField Ω C.1) (unit.yzProjection C) =
      coordinateEvaluation Ω C.1 (linearU D.lam) := by
  rw [eval_linearU]
  exact D.yzValue C

theorem common_a_value (unit : AdaptiveUnitProjectionFamily base p q)
    (D : CommonLinearValues unit) (C : RegularComponent Ω G T H) :
    coordinateValue Ω (CoordinateField Ω C.1) (unit.allProjection C) =
      coordinateEvaluation Ω C.1 (linearA D.mu D.lam) := by
  rw [eval_linearA]
  exact D.allValue C

/-- The common parameters and the projections are the old constructor's actual
ones. In particular no minimization over separately chosen families is made. -/
def of_active_nested
    (base : ∀ C : RegularComponent Ω G T H, SeparableLiteralCoordinate C.1)
    (hactive : ∀ C : RegularComponent Ω G T H,
      KaehlerDifferential.D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 0) ≠ 0 ∨
      KaehlerDifferential.D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 2) ≠ 0)
    (hZ : ∀ C : RegularComponent Ω G T H, LiteralProjectionGate C 2)
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (D : AdaptiveNestedProjectionDataActive (Omega := Ω) (G := G) (T := T) (H := H)
      base hactive hSderiv)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGsupport : G.support ⊆ flagSupport p) (hTsupport : T.support ⊆ flagSupport q) :
    CommonLinearValues (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport) where
  lam := D.lam
  mu := D.mu
  yzValue := by
    intro C
    change coordinateValue Ω (CoordinateField Ω C.1)
      (coordinateOfGate (affineU Ω C.1 D.lam) (D.uGate C)) = _
    exact coordinateOfGate_value _ _
  allValue := by
    intro C
    change (elementEmbedding Ω (CoordinateField Ω C.1)
      (affineV Ω C.1 D.mu (D.mu*D.lam)) (D.allAffineTranscendental C))
        (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X) = _
    exact elementEmbedding_variable Ω (CoordinateField Ω C.1) _ _

/-- Congruent-cut transport preserves the actual common rational functions,
not just their three numeric costs. The old and new component primes are defeq. -/
def of_congruent_cut {T' : Poly} (h : G ∣ T-T')
    {base' : ∀ C : RegularComponent Ω G T' H, SeparableLiteralCoordinate C.1}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (newBase : ∀ C : RegularComponent Ω G T H, SeparableLiteralCoordinate C.1)
    (D : CommonLinearValues U) :
    CommonLinearValues (LocatorHybridTransportC2.unitFamilyOfCongruentCut h U newBase) where
  lam := D.lam
  mu := D.mu
  yzValue C := D.yzValue (RCN066.regularComponentEquiv h C)
  allValue C := D.allValue (RCN066.regularComponentEquiv h C)

end
end ProximityPrize.SubmissionLower.CommonLinearChannels6807


