-- Prove2me | Definitions.Def_Yukon_ca06e00072579899a61b0098
-- name    : Yukon_ca06e00072579899a61b0098
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T21:22:12.074992+00:00
-- url     : https://prove2.me/theorems/6b6aaeef-23dc-4de3-953c-564d29b437bb
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WholeSpaceCube6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WholeSpaceCube6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WholeSpaceCube6814.lean
--
--   yukon-proof-operation:certificate-split-96d49039a614a18a2beb212e74f4d5a47142fe5aae1971f4c3b35b4b51d49348
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMmY5NTlmNGQ1YjhmMDQzZWQwODg2OTY1OGE3YWZhZTI1MWZmZDE1ZGU4MjdlNTgyNDQ3MzM0YmY4MzAyZGI5MCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTk2ZDQ5MDM5YTYxNGExOGEyYmViMjEyZTc0ZjRkNWE0NzE0MmZlNWFhZTE5NzFmNGMzYjM1YjRiNTFkNDkzNDgiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9jYTA2ZTAwMDcyNTc5ODk5YTYxYjAwOTgiLCJ2IjoyfQ]

import Definitions.Def_Yukon_80838211fc1a21bea5a1af61











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Whole-space exclusion of the recorded simple quadratic's fixed cube.
This uses polynomial degree additivity and dimension, not independently
chosen factors for each source. Variables are X,S,Y,R,gamma.
-/
namespace ProximityPrize.SubmissionLower.WholeSpaceCube6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K]
abbrev Poly := MvPolynomial (Fin 5) K

def weightEmbed (w : Fin 5 → ℕ) : (Fin 5 →₀ ℕ) →+ (Fin 6 →₀ ℕ) where
  toFun d := Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
    Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)+Finsupp.single 4 (d 4)+
    Finsupp.single 5 (Finsupp.weight w d)
  map_zero' := by simp
  map_add' d e := by ext i; fin_cases i <;> simp [Finsupp.add_apply,map_add]

theorem weightEmbed_coord (w : Fin 5 → ℕ) (d : Fin 5 →₀ ℕ) (i : Fin 5) :
    weightEmbed w d i.castSucc = d i := by
  fin_cases i <;> simp [weightEmbed]

theorem weightEmbed_injective (w : Fin 5 → ℕ) : Function.Injective (weightEmbed w) := by
  intro d e h
  ext i
  simpa only [weightEmbed_coord] using congrArg (fun x : Fin 6 →₀ ℕ => x i.castSucc) h

def weightedLift (w : Fin 5 → ℕ) : Poly (K := K) →+* MvPolynomial (Fin 6) K :=
  AddMonoidAlgebra.mapDomainRingHom K (weightEmbed w)

theorem weightedLift_injective (w : Fin 5 → ℕ) : Function.Injective (weightedLift (K := K) w) :=
  AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective w)

theorem weightedLift_degree (w : Fin 5 → ℕ) (P : Poly (K := K)) :
    (weightedLift w P).degreeOf 5 = weightedTotalDegree w P := by
  have hs : (weightedLift w P).support = P.support.image (weightEmbed w) :=
    Finsupp.mapDomain_support_of_injective (weightEmbed_injective w) _
  rw [degreeOf_eq_sup,hs,Finset.sup_image]
  change P.support.sup (fun d => weightEmbed w d 5) = P.support.sup (Finsupp.weight w)
  congr 1
  funext d
  simp [weightEmbed]

theorem weight_mul (w : Fin 5 → ℕ) (P Q : Poly (K := K)) (hP : P≠0) (hQ : Q≠0) :
    weightedTotalDegree w (P*Q) = weightedTotalDegree w P+weightedTotalDegree w Q := by
  have hn (A : Poly (K := K)) (hA : A≠0) : weightedLift w A ≠ 0 := by
    intro hz
    apply hA
    exact weightedLift_injective w (by simpa only [map_zero] using hz)
  rw [←weightedLift_degree,map_mul,degreeOf_mul_eq (hn P hP) (hn Q hQ),
    weightedLift_degree,weightedLift_degree]

theorem weight_pow (w : Fin 5 → ℕ) (P : Poly (K := K)) (hP : P≠0) (n : ℕ) :
    weightedTotalDegree w (P^n) = n*weightedTotalDegree w P := by
  induction n with
  | zero => simp [weightedTotalDegree]
  | succ n ih =>
    rw [pow_succ,weight_mul w _ _ (pow_ne_zero _ hP) hP,ih]
    ring

def codeWeights : Fin 5 → ℕ := ![1,131069,131071,131070,0]
def middleWeights : Fin 5 → ℕ := ![0,1,1,1,0]
def totalWeights : Fin 5 → ℕ := ![0,1,1,1,1]

theorem weight_coords (w : Fin 5 → ℕ) (e : Fin 5 →₀ ℕ) :
    Finsupp.weight w e = e 0*w 0+e 1*w 1+e 2*w 2+e 3*w 3+e 4*w 4 := by
  have he : e = Finsupp.single 0 (e 0)+Finsupp.single 1 (e 1)+
      Finsupp.single 2 (e 2)+Finsupp.single 3 (e 3)+Finsupp.single 4 (e 4) := by
    ext i; fin_cases i <;> simp
  rw [he,map_add,map_add,map_add,map_add]
  simp [Finsupp.weight_single]

theorem factor_code_lower (J : Poly (K := K)) (hJ : J≠0)
    (hmid : weightedTotalDegree middleWeights J=30)
    (hB : ∀ e ∈ J.support, 2*e 1+e 3 ≤ 9) :
    3932121 ≤ weightedTotalDegree codeWeights J := by
  obtain ⟨e,he,hmax⟩ := Finset.exists_mem_eq_sup J.support (support_nonempty.mpr hJ)
    (Finsupp.weight middleWeights)
  have hm : Finsupp.weight middleWeights e=30 := hmax.symm.trans hmid
  have hc : Finsupp.weight codeWeights e ≤ weightedTotalDegree codeWeights J := Finset.le_sup he
  have hb := hB e he
  have hm' : e 1+e 2+e 3=30 := by simpa [weight_coords,middleWeights] using hm
  have hc' : e 0+131069*e 1+131071*e 2+131070*e 3 ≤ weightedTotalDegree codeWeights J := by
    simpa [weight_coords,codeWeights,Nat.mul_comm] using hc
  omega

theorem quotient_bounds (J Q : Poly (K := K)) (hJ : J≠0) (hQ : Q≠0)
    (hmid : weightedTotalDegree middleWeights J=30)
    (hB : ∀ e ∈ J.support, 2*e 1+e 3 ≤ 9)
    (ht : weightedTotalDegree totalWeights J=331)
    (hcode : weightedTotalDegree codeWeights (J^3*Q) < 13050360)
    (htotal : weightedTotalDegree totalWeights (J^3*Q) ≤ 995) :
    weightedTotalDegree codeWeights Q < 1253997 ∧
      weightedTotalDegree totalWeights Q ≤ 2 := by
  have hl := factor_code_lower J hJ hmid hB
  rw [weight_mul _ _ _ (pow_ne_zero _ hJ) hQ,weight_pow _ _ hJ] at hcode htotal
  rw [ht] at htotal
  omega

abbrev QuotientIndex := Fin 1253997 × (Fin 4 → Fin 3)

def quotientExponent (i : QuotientIndex) : Fin 5 →₀ ℕ :=
  Finsupp.cons i.1.val (Finsupp.equivFunOnFinite.symm (fun j => (i.2 j).val))




theorem quotient_support (Q : Poly (K := K))
    (hcode : weightedTotalDegree codeWeights Q < 1253997)
    (htotal : weightedTotalDegree totalWeights Q ≤ 2) :
    ∀ e ∈ Q.support, e ∈ Set.range quotientExponent := by
  intro e he
  have hc := (Finset.le_sup (f := Finsupp.weight codeWeights) he).trans_lt hcode
  have ht := (Finset.le_sup (f := Finsupp.weight totalWeights) he).trans htotal
  simp [weight_coords,codeWeights,totalWeights] at hc ht
  have hx : e 0 < 1253997 := by omega
  have hrest : ∀ i : Fin 4, e i.succ < 3 := by
    intro i
    fin_cases i
    · change e 1 < 3; omega
    · change e 2 < 3; omega
    · change e 3 < 3; omega
    · change e 4 < 3; omega
  refine ⟨(⟨e 0,hx⟩,fun i => ⟨e i.succ,hrest i⟩),?_⟩
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [quotientExponent]

def cubeMultiply (J : Poly (K := K)) : Poly (K := K) →ₗ[K] Poly (K := K) where
  toFun Q := J^3*Q
  map_add' := mul_add _
  map_smul' a Q := by
    simp only [MvPolynomial.smul_eq_C_mul,RingHom.id_apply]
    ac_rfl

def cubeQuotient (V : Submodule K (Poly (K := K))) (J : Poly (K := K))
    (hdiv : ∀ v : V, J^3 ∣ v.val) (v : V) : Poly (K := K) :=
  Classical.choose (hdiv v)

theorem cubeQuotient_spec (V : Submodule K (Poly (K := K))) (J : Poly (K := K))
    (hdiv : ∀ v : V, J^3 ∣ v.val) (v : V) : v.val=J^3*cubeQuotient V J hdiv v :=
  Classical.choose_spec (hdiv v)

def cubeQuotientLinear (V : Submodule K (Poly (K := K))) (J : Poly (K := K))
    (hJ : J≠0) (hdiv : ∀ v : V, J^3 ∣ v.val) : V →ₗ[K] Poly (K := K) where
  toFun := cubeQuotient V J hdiv
  map_add' v u := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hJ)
    rw [mul_add,←cubeQuotient_spec,←cubeQuotient_spec,←cubeQuotient_spec]
    rfl
  map_smul' a v := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hJ)
    rw [←cubeQuotient_spec]
    change a • v.val=J^3*(a • cubeQuotient V J hdiv v)
    rw [cubeQuotient_spec V J hdiv v]
    simp only [MvPolynomial.smul_eq_C_mul]
    ac_rfl

theorem finrank_le_coefficients {W I : Type*} [AddCommGroup W] [Module K W]
    [Fintype I] (e : I → Fin 5 →₀ ℕ) (f : W →ₗ[K] Poly (K := K))
    (hf : Function.Injective f)
    (hs : ∀ v : W, ∀ d ∈ (f v).support, d ∈ Set.range e) :
    Module.finrank K W ≤ Fintype.card I := by
  let A : W →ₗ[K] (I → K) := LinearMap.pi (fun i => (MvPolynomial.lcoeff K (e i)).comp f)
  have hi : Function.Injective A := by
    intro v u h
    apply hf
    ext d
    have hh (i : I) : (f v).coeff (e i)=(f u).coeff (e i) := congrFun h i
    by_cases hv : d ∈ (f v).support
    · obtain ⟨i,rfl⟩ := hs v d hv
      exact hh i
    by_cases hu : d ∈ (f u).support
    · obtain ⟨i,rfl⟩ := hs u d hu
      exact hh i
    rw [MvPolynomial.notMem_support_iff.mp hv,MvPolynomial.notMem_support_iff.mp hu]
  simpa using LinearMap.finrank_le_finrank_of_injective hi












end
end ProximityPrize.SubmissionLower.WholeSpaceCube6814


