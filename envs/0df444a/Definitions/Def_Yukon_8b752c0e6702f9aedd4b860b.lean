-- Prove2me | Definitions.Def_Yukon_8b752c0e6702f9aedd4b860b
-- name    : Yukon_8b752c0e6702f9aedd4b860b
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T01:17:02.169341+00:00
-- url     : https://prove2.me/theorems/f5954d1f-f6a4-445a-af6b-d2b99f96bc96
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceVerticalFamily6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceVerticalFamily6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceVerticalFamily6814.lean
--
--   yukon-proof-operation:certificate-tail-424afa2e7bc8ebed13dcec85d416cd5ad6f5bef2bde6d4e8edc482889e82ef5a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZGYzMTc2N2YyODU3MGQwZGY4YTMwYzJjZDQxNzY5NjU3ZjYxNjM4OTVhMzIxYmE2MzdjYjFiNTBjMTIwMDMyZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXRhaWwtNDI0YWZhMmU3YmM4ZWJlZDEzZGNlYzg1ZDQxNmNkNWFkNmY1YmVmMmJkZTZkNGU4ZWRjNDgyODg5ZTgyZWY1YSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzhiNzUyYzBlNjcwMmY5YWVkZDRiODYwYiIsInYiOjJ9]

import Definitions.Def_Yukon_cab3e47590aea7a2fd8756f8













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The vertical arm of the shared plane-family bound. When the irreducible
first equation is constant in the outer variable, the second equation is
nonzero on that fibre. Swap the equations in the existing resultant count;
the cost is exactly outerDegree(Q) * degree(p), with no separability gate. -/
namespace ProximityPrize.SubmissionLower.MovingSourceVerticalFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators

variable {K : Type} [Field K]

theorem irreducible_of_C (p : Polynomial K)
    (hp : Irreducible (Polynomial.C p : Polynomial (Polynomial K))) : Irreducible p := by
  refine ⟨fun hu => hp.not_isUnit (hu.map Polynomial.C), ?_⟩
  intro a b hab
  have hh := hp.isUnit_or_isUnit (by rw [hab, map_mul])
  exact hh.imp Polynomial.isUnit_C.mp Polynomial.isUnit_C.mp

theorem associated_minpoly (p : Polynomial K) (hp : Irreducible p)
    {E : Type} [Field E] [Algebra K E] (y : E) (hy : Polynomial.aeval y p=0) :
    Associated p (minpoly K y) := by
  have hi : IsIntegral K y := IsAlgebraic.isIntegral ⟨p,hp.ne_zero,hy⟩
  exact (minpoly.irreducible hi).associated_of_dvd hp (minpoly.dvd K y hy) |>.symm

theorem specialization_ne_zero (p : Polynomial K) (hp : Irreducible p)
    (Q : Polynomial (Polynomial K)) (hproper : ¬Polynomial.C p ∣ Q)
    {E : Type} [Field E] [Algebra K E] (y : E) (hy : Polynomial.aeval y p=0) :
    Q.map (Polynomial.eval₂RingHom (algebraMap K E) y)≠0 := by
  intro hz
  apply hproper
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro j
  have hj := congrArg (fun A : Polynomial E => A.coeff j) hz
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero,
    Polynomial.coe_eval₂RingHom] at hj
  exact (associated_minpoly p hp y hy).dvd.trans (minpoly.dvd K y hj)

theorem finite_of_vertical_roots
    (p : Polynomial K) (hp : Irreducible p) (Q : Polynomial (Polynomial K))
    (hproper : ¬Polynomial.C p ∣ Q)
    {E : Type} [Field E] [Algebra K E] (y r : E)
    (hy : Polynomial.aeval y p=0)
    (hQ : Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K E) y) r Q=0)
    (hgen : IntermediateField.adjoin K ({y,r} : Set E)=⊤) :
    FiniteDimensional K E := by
  classical
  letI : DecidableEq K := Classical.decEq K
  have hyi : IsIntegral K y := IsAlgebraic.isIntegral ⟨p,hp.ne_zero,hy⟩
  let S : IntermediateField K E := IntermediateField.adjoin K {y}
  let yS : S := ⟨y,IntermediateField.mem_adjoin_simple_self K y⟩
  let g : Polynomial K →+* S := Polynomial.eval₂RingHom (algebraMap K S) yS
  have hcoeff : (algebraMap S E).comp g=
      Polynomial.eval₂RingHom (algebraMap K E) y := by
    apply Polynomial.ringHom_ext
    · intro c
      change algebraMap S E (Polynomial.eval₂ (algebraMap K S) yS (Polynomial.C c))=
        Polynomial.eval₂ (algebraMap K E) y (Polynomial.C c)
      rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
      exact (IsScalarTower.algebraMap_apply K S E c).symm
    · change algebraMap S E (Polynomial.eval₂ (algebraMap K S) yS Polynomial.X)=
        Polynomial.eval₂ (algebraMap K E) y Polynomial.X
      simp only [Polynomial.eval₂_X]
      rfl
  have hQne : Q.map g≠0 := by
    intro hz
    have hh := congrArg (Polynomial.map (algebraMap S E)) hz
    rw [Polynomial.map_map,hcoeff,Polynomial.map_zero] at hh
    exact specialization_ne_zero p hp Q hproper y hy hh
  have hr : Polynomial.aeval r (Q.map g)=0 := by
    change Polynomial.eval₂ (algebraMap S E) r (Q.map g)=0
    rw [Polynomial.eval₂_map,hcoeff]
    exact hQ
  have hri : IsIntegral S r := IsAlgebraic.isIntegral ⟨Q.map g,hQne,hr⟩
  letI : FiniteDimensional K S := IntermediateField.adjoin.finiteDimensional hyi
  letI : Algebra.IsIntegral K S := Algebra.IsIntegral.of_finite K S
  exact RCN024.finiteDimensional_of_integral_generating_pair y r hyi
    (isIntegral_trans r hri) hgen

theorem sum_finrank_vertical
    {I : Type*} [Fintype I] (E : I → Type)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, FiniteDimensional K (E i)]
    (p : Polynomial K) (hp : Irreducible p) (Q : Polynomial (Polynomial K))
    (hproper : ¬Polynomial.C p ∣ Q) (y r : ∀ i, E i)
    (hgen : ∀ i, IntermediateField.adjoin K ({y i,r i} : Set (E i))=⊤)
    (hkernels : Function.Injective (fun i => RCN361.relationIdeal K (E i) (y i) (r i)))
    (hy : ∀ i, Polynomial.aeval (y i) p=0)
    (hQ : ∀ i, RCN361.planeEval K (E i) (y i) (r i) Q=0) :
    (∑ i, Module.finrank K (E i)) ≤ Q.natDegree*p.natDegree := by
  classical
  letI : DecidableEq K := Classical.decEq K
  have hspecial : ∀ f ∈ Finset.univ.image (fun i => minpoly K (y i)),
      Q.map (AdjoinRoot.mk f)≠0 := by
    intro f hf hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
    apply hproper
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro j
    have hj := congrArg (fun A : Polynomial (AdjoinRoot (minpoly K (y i))) => A.coeff j) hz
    simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at hj
    exact (associated_minpoly p hp (y i) (hy i)).dvd.trans (AdjoinRoot.mk_eq_zero.mp hj)
  have hroot : ∀ i, RCN361.planeEval K (E i) (y i) (r i) (Polynomial.C p)=0 := by
    intro i
    rw [RCN365.planeEval_eq_eval₂,Polynomial.eval₂_C]
    exact hy i
  have hres : Polynomial.resultant Q (Polynomial.C p) Q.natDegree 0≠0 := by
    simpa only [Polynomial.resultant_C_right,pow_zero,one_mul] using pow_ne_zero Q.natDegree hp.ne_zero
  have hb := RCN025.sum_finrank_le_resultant_of_relationIdeal_injective
    E Q (Polynomial.C p) Q.natDegree 0 le_rfl (by simp) y r hgen hkernels
    hQ hroot hspecial hres
  simpa only [Polynomial.resultant_C_right,pow_zero,one_mul,Polynomial.natDegree_pow] using hb

/-- All irreducible plane components, including vertical ones. The target is
one resultant degree for the entire family, not one budget per field. -/
theorem finite_sum_finrank_irreducible
    {I : Type*} [Fintype I] (E : I → Type)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    (P Q : Polynomial (Polynomial K)) (hP : Irreducible P) (hproper : ¬P∣Q)
    (y r : ∀ i, E i)
    (hgen : ∀ i, IntermediateField.adjoin K ({y i,r i} : Set (E i))=⊤)
    (hkernels : Function.Injective (fun i => RCN361.relationIdeal K (E i) (y i) (r i)))
    (hProot : ∀ i, RCN361.planeEval K (E i) (y i) (r i) P=0)
    (hQroot : ∀ i, RCN361.planeEval K (E i) (y i) (r i) Q=0) :
    (∀ i, FiniteDimensional K (E i)) ∧
      (∑ i, Module.finrank K (E i)) ≤ (Polynomial.resultant P Q).natDegree := by
  classical
  letI : DecidableEq K := Classical.decEq K
  by_cases hzero : P.natDegree=0
  · have he := Polynomial.eq_C_of_natDegree_eq_zero hzero
    rw [he] at hP hproper hProot ⊢
    have hp := irreducible_of_C (P.coeff 0) hP
    have hy : ∀ i, Polynomial.aeval (y i) (P.coeff 0)=0 := by
      intro i
      have hh := hProot i
      rw [RCN365.planeEval_eq_eval₂,Polynomial.eval₂_C] at hh
      exact hh
    have hfinite : ∀ i, FiniteDimensional K (E i) := fun i =>
      finite_of_vertical_roots (P.coeff 0) hp Q hproper (y i) (r i) (hy i)
        ((RCN365.planeEval_eq_eval₂ _ _ _ _ _).symm.trans (hQroot i)) (hgen i)
    letI : ∀ i, FiniteDimensional K (E i) := hfinite
    refine ⟨hfinite,?_⟩
    have hh := sum_finrank_vertical E (P.coeff 0) hp Q hproper y r hgen hkernels hy hQroot
    simpa only [Polynomial.natDegree_C,Polynomial.resultant_C_left,zero_mul,pow_zero,
      one_mul,Polynomial.natDegree_pow] using hh
  · have hpositive := Nat.pos_of_ne_zero hzero
    have hfinite : ∀ i, FiniteDimensional K (E i) := fun i =>
      RCN024.finite_of_proper_plane_roots P Q hP hpositive hproper (y i) (r i)
        ((RCN365.planeEval_eq_eval₂ _ _ _ _ _).symm.trans (hProot i))
        ((RCN365.planeEval_eq_eval₂ _ _ _ _ _).symm.trans (hQroot i)) (hgen i)
    letI : ∀ i, FiniteDimensional K (E i) := hfinite
    exact ⟨hfinite,RCN124.sum_finrank_le_ordinary_resultant_without_separability
      E P Q hP hpositive hproper y r hgen hkernels hProot hQroot⟩



end
end ProximityPrize.SubmissionLower.MovingSourceVerticalFamily6814


