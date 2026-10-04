-- Prove2me | Definitions.Def_Yukon_9e6b0bff61d8a97ca7ca80a3
-- name    : Yukon_9e6b0bff61d8a97ca7ca80a3
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T21:44:14.300648+00:00
-- url     : https://prove2.me/theorems/92141760-0bc2-4ff5-910f-269c5c8a5934
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WholeSpaceCubeUniform6814.lean
--
--   yukon-proof-operation:certificate-split-d1f491b803d6d6a994fe90f56448420ce52b42eeafc0023e2747520d8084228a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZTQ0NjhkMWFkYTA0MWU3MzAyOGEzOGUxZTIzNzFiOGExZmJjZmExYzI0ZTJiMzMyZDM5M2YwNzliMDk3ZjgwNCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LWQxZjQ5MWI4MDNkNmQ2YTk5NGZlOTBmNTY0NDg0MjBjZTUyYjQyZWVhZmMwMDIzZTI3NDc1MjBkODA4NDIyOGEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85ZTZiMGJmZjYxZDhhOTdjYTdjYTgwYTMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_ca06e00072579899a61b0098











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! A single enlarged interpolation space excludes the remaining quadratic
fixed cubes uniformly. No enumeration of candidate polynomials is used. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial WholeSpaceCube6814

variable {K : Type*} [Field K]
def slopeWeights : Fin 5 → ℕ := ![0,2,0,1,0]

theorem factor_lower (J : Poly (K := K)) (hJ : J≠0)
    (hm : 25 ≤ weightedTotalDegree middleWeights J)
    (hb : weightedTotalDegree slopeWeights J=9) :
    3276766 ≤ weightedTotalDegree codeWeights J ∧
      25 ≤ weightedTotalDegree totalWeights J := by
  obtain ⟨e,he,hmax⟩ := Finset.exists_mem_eq_sup J.support (support_nonempty.mpr hJ)
    (Finsupp.weight middleWeights)
  have hmid : 25 ≤ Finsupp.weight middleWeights e := by
    change 25 ≤ J.support.sup (Finsupp.weight middleWeights) at hm
    rwa [hmax] at hm
  have hB := (Finset.le_sup (f := Finsupp.weight slopeWeights) he).trans_eq hb
  have hc0 : Finsupp.weight codeWeights e ≤ weightedTotalDegree codeWeights J := Finset.le_sup he
  have ht0 : Finsupp.weight totalWeights e ≤ weightedTotalDegree totalWeights J := Finset.le_sup he
  have hc : e 0+131069*e 1+131071*e 2+131070*e 3 ≤ weightedTotalDegree codeWeights J := by
    simpa [weight_coords,codeWeights,Nat.mul_comm] using hc0
  have ht : e 1+e 2+e 3+e 4 ≤ weightedTotalDegree totalWeights J := by
    simpa [weight_coords,totalWeights] using ht0
  have hm' : 25 ≤ e 1+e 2+e 3 := by simpa [weight_coords,middleWeights] using hmid
  have hb' : 2*e 1+e 3 ≤ 9 := by simpa [weight_coords,slopeWeights,Nat.mul_comm] using hB
  constructor <;> omega

theorem quotient_bounds_uniform (J Q : Poly (K := K)) (hJ : J≠0) (hQ : Q≠0)
    (hm : 25 ≤ weightedTotalDegree middleWeights J)
    (hb : weightedTotalDegree slopeWeights J=9)
    (hcode : weightedTotalDegree codeWeights (J^3*Q) < 13050360)
    (htotal : weightedTotalDegree totalWeights (J^3*Q) ≤ 1700)
    (hmiddle : weightedTotalDegree middleWeights (J^3*Q) ≤ 98)
    (hslope : weightedTotalDegree slopeWeights (J^3*Q) ≤ 31) :
    weightedTotalDegree codeWeights Q < 3220062 ∧
      weightedTotalDegree totalWeights Q ≤ 1625 ∧
      weightedTotalDegree middleWeights Q ≤ 23 ∧
      weightedTotalDegree slopeWeights Q ≤ 4 := by
  have hl := factor_lower J hJ hm hb
  rw [weight_mul _ _ _ (pow_ne_zero _ hJ) hQ,weight_pow _ _ hJ] at hcode htotal hmiddle hslope
  rw [hb] at hslope
  omega

abbrev QuotientIndex :=
  Σ s : Fin 3, Σ r : Fin (5-2*s.val), Σ y : Fin 24,
    Fin (3220062-131071*y.val) × Fin 1626

def quotientExponent (i : QuotientIndex) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![i.2.2.2.1.val,i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

theorem coefficient_count :
    (∑ y : Fin 24, (3220062-131071*y.val)) = 41105892 := by
  norm_num [Fin.sum_univ_succ]

theorem quotient_card : Fintype.card QuotientIndex=601543623528 := by
  simp only [QuotientIndex,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  simp only [←Finset.sum_mul,coefficient_count,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]
  norm_num [Fin.sum_univ_succ]

theorem quotient_support_uniform (Q : Poly (K := K))
    (hb : weightedTotalDegree codeWeights Q < 3220062 ∧
      weightedTotalDegree totalWeights Q ≤ 1625 ∧
      weightedTotalDegree middleWeights Q ≤ 23 ∧
      weightedTotalDegree slopeWeights Q ≤ 4) :
    ∀ e ∈ Q.support, e ∈ Set.range quotientExponent := by
  intro e he
  have hc := (Finset.le_sup (f := Finsupp.weight codeWeights) he).trans_lt hb.1
  have ht := (Finset.le_sup (f := Finsupp.weight totalWeights) he).trans hb.2.1
  have hm := (Finset.le_sup (f := Finsupp.weight middleWeights) he).trans hb.2.2.1
  have hs := (Finset.le_sup (f := Finsupp.weight slopeWeights) he).trans hb.2.2.2
  simp [weight_coords,codeWeights,totalWeights,middleWeights,slopeWeights] at hc ht hm hs
  refine ⟨⟨⟨e 1,by omega⟩,⟨e 3,?_⟩,⟨e 2,by omega⟩,
    ⟨e 0,?_⟩,⟨e 4,by omega⟩⟩,?_⟩
  · change e 3 < 5-2*e 1
    omega
  · change e 0 < 3220062-131071*e 2
    omega
  · ext i
    fin_cases i <;> simp [quotientExponent]

/-- Uniform whole-space avoidance. The hypotheses are source support and
nullity, not a desired counting bound or an assumed coprime source. -/
theorem exists_not_dvd_cube_uniform
    (V : Submodule K (Poly (K := K))) [Module.Finite K V]
    (hdim : 627003341034 ≤ Module.finrank K V)
    (hcode : ∀ P ∈ V, weightedTotalDegree codeWeights P < 13050360)
    (htotal : ∀ P ∈ V, weightedTotalDegree totalWeights P ≤ 1700)
    (hmiddle : ∀ P ∈ V, weightedTotalDegree middleWeights P ≤ 98)
    (hslope : ∀ P ∈ V, weightedTotalDegree slopeWeights P ≤ 31)
    (J : Poly (K := K)) (hJ : J≠0)
    (hm : 25 ≤ weightedTotalDegree middleWeights J)
    (hb : weightedTotalDegree slopeWeights J=9) :
    ∃ P ∈ V, ¬ J^3 ∣ P := by
  classical
  by_contra hno
  have hdiv : ∀ P ∈ V, J^3 ∣ P := by simpa only [not_exists,not_and,not_not] using hno
  let hd : ∀ v : V, J^3 ∣ v.val := fun v => hdiv v.val v.property
  let f := cubeQuotientLinear V J hJ hd
  have hf : Function.Injective f := by
    intro v u he
    apply Subtype.ext
    rw [cubeQuotient_spec V J hd v,cubeQuotient_spec V J hd u]
    exact congrArg (fun Q => J^3*Q) he
  have hs : ∀ v : V, ∀ e ∈ (f v).support, e ∈ Set.range quotientExponent := by
    intro v e he
    have hq : f v ≠ 0 := by intro hz; simpa [hz] using he
    have hv : v.val=J^3*f v := cubeQuotient_spec V J hd v
    have hh := quotient_bounds_uniform J (f v) hJ hq hm hb
      (by rw [←hv]; exact hcode v.val v.property)
      (by rw [←hv]; exact htotal v.val v.property)
      (by rw [←hv]; exact hmiddle v.val v.property)
      (by rw [←hv]; exact hslope v.val v.property)
    exact quotient_support_uniform (f v) hh e he
  have hh := finrank_le_coefficients quotientExponent f hf hs
  rw [quotient_card] at hh
  omega







open RCN095 UniqueCurvatureOwner6814




















end
end ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814


