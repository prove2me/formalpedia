-- Prove2me | Definitions.Def_Yukon_91e99a7c9682f8cc19028ba7
-- name    : Yukon_91e99a7c9682f8cc19028ba7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T23:17:00.189983+00:00
-- url     : https://prove2.me/theorems/7c0c0f47-6eff-4750-801f-f64f0f08b611
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceClearing6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceClearing6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceClearing6814.lean
--
--   yukon-proof-operation:certificate-r12-pair-split-ec1e80f7d34f9c4978d83448316077f6c3ccb904f718ef6f1255bc18a24e76db
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjgxMjBkMDMyYzk0MjI4ZDEyNjU0ODg3ZjkzZGYwNjljMmU3NGQ2YzZiNjNkZjcyZmZiMThjZDI0MDE5ODUyOCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMi1wYWlyLXNwbGl0LWVjMWU4MGY3ZDM0ZjljNDk3OGQ4MzQ0ODMxNjA3N2Y2YzNjY2I5MDRmNzE4ZWY2ZjEyNTViYzE4YTI0ZTc2ZGIiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85MWU5OWE3Yzk2ODJmOGNjMTkwMjhiYTciLCJ2IjoyfQ]

import Definitions.Def_Yukon_a98065d48a835a5fe7279317














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The actual denominator-cleared moving cut for a second-jet source.
No assumption of a new degree budget or of post-clearing properness. -/
namespace ProximityPrize.SubmissionLower.MovingSourceClearing6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open MvPolynomial RCN095 RCN136 RCN207
open SecondJetCoefficients SecondJetClearedHelper

section Polynomial
variable {R : Type*} [CommRing R]

/-- Clear P((T-q)/h), with the moving target T still indeterminate. -/
def targetPolynomial (P : Polynomial R) (n : ℕ) (h q : R) : Polynomial R :=
  cleared (P.map Polynomial.C) n (Polynomial.C h) (Polynomial.X-Polynomial.C q)

def inverseSubstitution (h q : R) : Polynomial R →+* Polynomial R :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C h*Polynomial.X+Polynomial.C q)

theorem inverseSubstitution_C (h q a : R) :
    inverseSubstitution h q (Polynomial.C a)=Polynomial.C a := by
  simp [inverseSubstitution]

theorem inverseSubstitution_target (P : Polynomial R) (n : ℕ) (h q : R)
    (hn : P.natDegree ≤ n) :
    inverseSubstitution h q (targetPolynomial P n h q)=(Polynomial.C h)^n*P := by
  have hc : (inverseSubstitution h q).comp Polynomial.C=Polynomial.C := by
    apply RingHom.ext
    intro a
    exact inverseSubstitution_C h q a
  rw [targetPolynomial,map_cleared,Polynomial.map_map,hc]
  simp only [inverseSubstitution_C,map_sub]
  have hx : inverseSubstitution h q Polynomial.X-Polynomial.C q=Polynomial.C h*Polynomial.X := by
    simp [inverseSubstitution]
  rw [hx,cleared_eval (P.map Polynomial.C) n (Polynomial.natDegree_map_le.trans hn)
    (Polynomial.C h) (Polynomial.C h*Polynomial.X) Polynomial.X rfl]
  rw [Polynomial.eval_map,Polynomial.eval₂_C_X]

theorem eval_targetPolynomial {S : Type*} [CommRing S] (f : R →+* S)
    (P : Polynomial R) (n : ℕ) (h q : R) (t : S) :
    Polynomial.eval₂ f t (targetPolynomial P n h q)=
      cleared (P.map f) n (f h) (t-f q) := by
  change (Polynomial.eval₂RingHom f t) (targetPolynomial P n h q)=_
  have hc : (Polynomial.eval₂RingHom f t).comp Polynomial.C=f := by
    apply RingHom.ext
    intro a
    simp
  rw [targetPolynomial,map_cleared,Polynomial.map_map]
  rw [hc]
  simp

end Polynomial

section Surface
variable {K E : Type*} [Field K] [Field E]
local notation "Poly3" => MvPolynomial (Fin 3) E

def coefficients (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K)) :
    Polynomial Poly3 := (asS P).map (surfaceMap phi)

def movingCut (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (s : ℕ) (Q A : Poly3) (target : E) : Poly3 :=
  cleared (coefficients phi P) s (2*A) (MvPolynomial.C target-Q)

theorem coefficient_flag (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (B U T : ℕ) (hBU : B ≤ U) (hUT : U ≤ T)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ T)
    (j : ℕ) : PolynomialInFlag (SecondJetRelaxedFlag.coefficientFlag B U T j)
      ((coefficients phi P).coeff j) := by
  rw [coefficients,Polynomial.coeff_map,←SecondJetSurfaceMap.frozen_mapped_coefficient phi P j]
  exact SecondJetRelaxedFlag.frozen_coefficient_flag
    (MvPolynomial.map (phi.comp Polynomial.C) P) (phi Polynomial.X) B U T hBU hUT
    (SecondJetSurfaceMap.mapped_support_bounds _ P B U T hP) j

theorem twice_linear_flag (A : Poly3) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag unitYZFlag (2*A) := by
  intro e he
  have he' : e ∈ ((2 : E) • A).support := by
    simpa only [MvPolynomial.smul_eq_C_mul,map_ofNat] using he
  exact hA e (MvPolynomial.support_smul he')

theorem movingCut_flag (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (B U T s : ℕ) (hBU : B ≤ U) (hUT : U ≤ T) (hsB : 2*s ≤ B)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ T)
    (Q A : Poly3) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag ⟨T-U,U-B+s,B⟩ (movingCut phi P s Q A target) := by
  change PolynomialInFlag _
    (eliminatedCut s (fun j => (coefficients phi P).coeff j.val) Q (2*A) target)
  apply eliminatedCut_inFlag s _ Q (2*A) target
    (fun j => SecondJetRelaxedFlag.coefficientFlag B U T j.val) _
    (fun j => coefficient_flag phi P B U T hBU hUT hP j.val) hQ (twice_linear_flag A hA)
  intro j
  have hj := j.isLt
  have hsub : B-2*j.val+2*j.val=B := Nat.sub_add_cancel (by omega)
  change (⟨T-U+(s-j.val)*0+j.val*(2*0),
    U-B+j.val+(s-j.val)*1+j.val*(2*0),
    B-2*j.val+(s-j.val)*0+j.val*(2*1)⟩ : FlagDegree)=_
  congr 1 <;> omega

theorem moving_root_relation {L : Type*} [Field L]
    (ev : Poly3 →+* L) (H G Q A : Poly3) (target : E) (sigma : L)
    (hH : ev H≠0) (hN : ev (movingEquation H G Q A target)=0)
    (hsigma : ev (2*H)*sigma=ev G) :
    ev (2*A)*sigma=ev (MvPolynomial.C target-Q) := by
  have hn : ev H*ev (MvPolynomial.C target-Q)=ev A*ev G := by
    simpa only [movingEquation,map_sub,map_mul,sub_eq_zero] using hN
  apply mul_left_cancel₀ hH
  rw [hn]
  simp only [map_mul,map_ofNat] at hsigma ⊢
  calc
    ev H*(2*ev A*sigma) = ev A*(2*ev H*sigma) := by ring
    _ = ev A*ev G := by rw [hsigma]







end Surface






end
end ProximityPrize.SubmissionLower.MovingSourceClearing6814


