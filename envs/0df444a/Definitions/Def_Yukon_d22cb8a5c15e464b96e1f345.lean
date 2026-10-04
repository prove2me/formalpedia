-- Prove2me | Definitions.Def_Yukon_d22cb8a5c15e464b96e1f345
-- name    : Yukon_d22cb8a5c15e464b96e1f345
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T19:34:21.417905+00:00
-- url     : https://prove2.me/theorems/76cdcb8a-aade-425d-a2d2-f78303b40d76
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.ContactPencilDirection6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.ContactPencilDirection6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/ContactPencilDirection6814.lean
--
--   yukon-proof-operation:certificate-split-d77a69235bbd01796345e0d4166c1f62e440e136143b43551e294c89fc7f1928
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzJmY2I0ODE5MWQwNDgxNGE2MjMyNDFmZTRhMGQ4N2E1MTI2NDdmNTM1ZGVmNjM4Yzg4NmEzZTA2ZjYzYjY0MiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LWQ3N2E2OTIzNWJiZDAxNzk2MzQ1ZTBkNDE2NmMxZjYyZTQ0MGUxMzYxNDNiNDM1NTFlMjk0Yzg5ZmM3ZjE5MjgiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9kMjJjYjhhNWMxNWU0NjRiOTZlMWYzNDUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_9077872203014fcbbcdda9fb











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.ContactPencilDirection6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MvPolynomial

variable {K : Type*} [CommRing K]
abbrev JetPoly := MvPolynomial (Fin 5) K

/-- The actual second-jet contact substitution, written without composition. -/
def contactMap (x u0 u1 : K) : JetPoly (K := K) →ₐ[K] JetPoly (K := K) :=
  MvPolynomial.aeval ![MvPolynomial.C x+MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4+
      MvPolynomial.X 0*MvPolynomial.X 3-MvPolynomial.X 0^2*MvPolynomial.X 1+
      MvPolynomial.X 0^3*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

def pencilD (v v1 v2 : JetPoly (K := K)) :
    Derivation K (JetPoly (K := K)) (JetPoly (K := K)) :=
  pderiv 4+v • pderiv 2+v1 • pderiv 3+v2 • pderiv 1

def localD (v1 v2 q : JetPoly (K := K)) :
    Derivation K (JetPoly (K := K)) (JetPoly (K := K)) :=
  pderiv 4+v1 • pderiv 3+v2 • pderiv 1+q • pderiv 2

theorem localD_epsilon (v1 v2 q : JetPoly (K := K)) :
    localD v1 v2 q (MvPolynomial.X 0)=0 := by
  simp [localD,pderiv_X]

theorem contact_chain (x u0 u1 : K) (v v1 v2 q : JetPoly (K := K))
    (hcompat : contactMap x u0 u1 v = MvPolynomial.C u1+
      MvPolynomial.X 0*contactMap x u0 u1 v1-
      MvPolynomial.X 0^2*contactMap x u0 u1 v2+MvPolynomial.X 0^3*q)
    (P : JetPoly (K := K)) :
    contactMap x u0 u1 (pencilD v v1 v2 P) =
      localD (contactMap x u0 u1 v1) (contactMap x u0 u1 v2) q
        (contactMap x u0 u1 P) := by
  have hx (j : Fin 5) :
      contactMap x u0 u1 (pencilD v v1 v2 (MvPolynomial.X j)) =
        localD (contactMap x u0 u1 v1) (contactMap x u0 u1 v2) q
          (contactMap x u0 u1 (MvPolynomial.X j)) := by
    fin_cases j <;>
      simp [pencilD,localD,contactMap,pderiv_X] at * <;>
      first | assumption | ring_nf at *; assumption
  induction P using MvPolynomial.induction_on with
  | C c => simp [pencilD,localD,contactMap]
  | add P Q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X P j hp =>
    simp only [Derivation.leibniz,smul_eq_mul,map_add,map_mul,hp,hx]

theorem pencil_preserves_contact (x u0 u1 : K)
    (v v1 v2 q P : JetPoly (K := K)) (m : ℕ)
    (hcompat : contactMap x u0 u1 v = MvPolynomial.C u1+
      MvPolynomial.X 0*contactMap x u0 u1 v1-
      MvPolynomial.X 0^2*contactMap x u0 u1 v2+MvPolynomial.X 0^3*q)
    (hP : MvPolynomial.X 0^m ∣ contactMap x u0 u1 P) :
    MvPolynomial.X 0^m ∣ contactMap x u0 u1 (pencilD v v1 v2 P) := by
  rw [contact_chain x u0 u1 v v1 v2 q hcompat]
  obtain ⟨A,hA⟩ := hP
  refine ⟨localD (contactMap x u0 u1 v1) (contactMap x u0 u1 v2) q A,?_⟩
  rw [hA,Derivation.leibniz,Derivation.leibniz_pow,localD_epsilon]
  simp [smul_eq_mul]

/-- Taylor compatibility has a polynomial correction, with no poles in
epsilon. Hasse order two avoids dividing by two in this statement. -/
theorem backwards_taylor_remainder (P : Polynomial K) :
    Polynomial.X^3 ∣ P-Polynomial.C (P.coeff 0)-Polynomial.X*P.derivative+
      Polynomial.X^2*Polynomial.hasseDeriv 2 P := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro j hj
  interval_cases j <;>
    simp [Polynomial.coeff_derivative,Polynomial.hasseDeriv_coeff,
      Polynomial.coeff_X_pow_mul',Polynomial.coeff_X_mul] <;> ring

theorem hasse_taylor (j : ℕ) (x : K) (P : Polynomial K) :
    Polynomial.hasseDeriv j (Polynomial.taylor x P)=
      Polynomial.taylor x (Polynomial.hasseDeriv j P) := by
  ext n
  rw [Polynomial.hasseDeriv_coeff,Polynomial.taylor_coeff,Polynomial.taylor_coeff]
  have hc := congrArg (fun f : Polynomial K →ₗ[K] Polynomial K => f P)
    (Polynomial.hasseDeriv_comp n j (R := K))
  simp only [LinearMap.comp_apply,LinearMap.smul_apply] at hc
  rw [hc]
  simp [nsmul_eq_mul,Nat.choose_symm_add]

theorem derivative_taylor (x : K) (P : Polynomial K) :
    (Polynomial.taylor x P).derivative=Polynomial.taylor x P.derivative := by
  simpa only [Polynomial.hasseDeriv_one] using hasse_taylor 1 x P

def liftX : Polynomial K →ₐ[K] JetPoly (K := K) :=
  Polynomial.aeval (MvPolynomial.X 0)

theorem contact_liftX (x u0 u1 : K) (P : Polynomial K) :
    contactMap x u0 u1 (liftX P)=liftX (Polynomial.taylor x P) := by
  change ((contactMap x u0 u1).comp (Polynomial.aeval (MvPolynomial.X 0))) P = _
  rw [←Polynomial.aeval_algHom]
  simp only [liftX,Polynomial.taylor_apply,Polynomial.aeval_comp]
  congr 1
  simp [contactMap,add_comm]

theorem exists_pencil_compatibility (x u0 u1 : K) (V : Polynomial K)
    (hvalue : V.eval x=u1) :
    ∃ q : JetPoly (K := K),
      contactMap x u0 u1 (liftX V)=MvPolynomial.C u1+
        MvPolynomial.X 0*contactMap x u0 u1 (liftX V.derivative)-
        MvPolynomial.X 0^2*contactMap x u0 u1 (liftX (Polynomial.hasseDeriv 2 V))+
        MvPolynomial.X 0^3*q := by
  obtain ⟨Q,hQ⟩ := backwards_taylor_remainder (Polynomial.taylor x V)
  rw [Polynomial.taylor_coeff_zero,hvalue,derivative_taylor,hasse_taylor] at hQ
  refine ⟨liftX Q,?_⟩
  have hh := congrArg (fun p : Polynomial K => liftX p) hQ
  simp only [map_add,map_sub,map_mul,map_pow] at hh
  simp only [liftX,Polynomial.aeval_C,Polynomial.aeval_X,MvPolynomial.algebraMap_eq] at hh
  rw [contact_liftX,contact_liftX,contact_liftX]
  dsimp only [liftX]
  linear_combination hh

/-- Unconditional contact preservation for the received interpolation
pencil: the only datum is the actual node value V(x)=u1. -/
theorem received_pencil_preserves_contact (x u0 u1 : K) (V : Polynomial K)
    (hvalue : V.eval x=u1) (P : JetPoly (K := K)) (m : ℕ)
    (hP : MvPolynomial.X 0^m ∣ contactMap x u0 u1 P) :
    MvPolynomial.X 0^m ∣ contactMap x u0 u1
      (pencilD (liftX V) (liftX V.derivative) (liftX (Polynomial.hasseDeriv 2 V)) P) := by
  obtain ⟨q,hq⟩ := exists_pencil_compatibility x u0 u1 V hvalue
  exact pencil_preserves_contact x u0 u1 _ _ _ q P m hq hP

theorem contactMap_eq_actual {F : Type*} [Field F] (x u0 u1 : F) :
    contactMap x u0 u1 =
      (SecondJetDifferentiation.substitute (K := F)).comp
        (SecondJetGlobalSupport.localize x u0 u1) := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j <;>
    simp [contactMap,SecondJetDifferentiation.substitute,SecondJetGlobalSupport.localize] <;> ring



















end
end ProximityPrize.SubmissionLower.ContactPencilDirection6814


