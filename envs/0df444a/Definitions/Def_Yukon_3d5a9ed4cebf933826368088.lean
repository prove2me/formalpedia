-- Prove2me | Definitions.Def_Yukon_3d5a9ed4cebf933826368088
-- name    : Yukon_3d5a9ed4cebf933826368088
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T22:31:38.233196+00:00
-- url     : https://prove2.me/theorems/661c2a8e-a5b5-408d-9582-9babc7338252
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WholeSpaceSourceKernel6814.lean
--
--   yukon-proof-operation:certificate-split-11822e790ffd1d4869ee2c448b37f5c3a64a3a063e75809bc905846621faf474
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMjQzNTg1MmZmNDFkNTQ0MWMxZGNhNTZlMzBlMmM4YjJhZmFjZWU3ZDRkNWJkYmU4NDkwOWUzMmQxZWVlODY0MCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTExODIyZTc5MGZmZDFkNDg2OWVlMmM0NDhiMzdmNWMzYTY0YTNhMDYzZTc1ODA5YmM5MDU4NDY2MjFmYWY0NzQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8zZDVhOWVkNGNlYmY5MzM4MjYzNjgwODgiLCJ2IjoyfQ]

import Definitions.Def_Yukon_6591a3d1307c7a4371e4d16b













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Actual contact interpolation outside a fixed cube. Keep the large
coefficient index ABSTRACT while proving the kernel argument; instantiate
the checked concrete index only in the final theorem. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
open scoped BigOperators
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpaceSourceCounts6814
open SecondJetSupport SecondJetGlobalSupport
open SecondJetGlobalMap (coefficientLocal untruncate_contact)

variable {K N I : Type*} [Field K] [Fintype N] [Fintype I]

def Bounds (P : WholeSpaceCube6814.Poly (K := K)) : Prop :=
  ∀ e ∈ P.support, 2*e 1+e 3 ≤ 31 ∧ e 1 ≤ 14 ∧
    e 1+e 2+e 3 ≤ 98 ∧ e 1+e 2+e 3+e 4 ≤ 1700 ∧
    e 0+131071*e 2+131070*e 3+131069*e 1 < cutoff (e 1)

theorem weights_of_bounds (P : WholeSpaceCube6814.Poly (K := K)) (hs : Bounds P) :
    weightedTotalDegree codeWeights P < 13050360 ∧
    weightedTotalDegree totalWeights P ≤ 1700 ∧
    weightedTotalDegree middleWeights P ≤ 98 ∧
    weightedTotalDegree slopeWeights P ≤ 31 ∧ P.degreeOf 1 ≤ 14 := by
  have hc : weightedTotalDegree codeWeights P ≤ 13050359 := by
    apply Finset.sup_le
    intro e he
    have hh := (hs e he).2.2.2.2
    have hcut : cutoff (e 1) ≤ 13050360 := Nat.sub_le _ _
    simp [weight_coords,codeWeights]
    omega
  refine ⟨by omega,?_,?_,?_,?_⟩
  · apply Finset.sup_le
    intro e he
    simpa [weight_coords,totalWeights] using (hs e he).2.2.2.1
  · apply Finset.sup_le
    intro e he
    simpa [weight_coords,middleWeights] using (hs e he).2.2.1
  · apply Finset.sup_le
    intro e he
    simpa [weight_coords,slopeWeights,Nat.mul_comm] using (hs e he).1
  · exact MvPolynomial.degreeOf_le_iff.mpr (fun e he => (hs e he).2.1)

/-- Rank-nullity version of the repo's existing global-contact
construction, retaining the entire kernel instead of choosing one vector.
All local-space parameters stay symbolic in this proof. -/
theorem exists_contact_kernel
    (e : I → Fin 5 →₀ ℕ) (he : Function.Injective e)
    (m L B s U w : ℕ) (D : ℕ → ℕ) (hw : 2 ≤ w)
    (hb : ∀ i, 2*e i 1+e i 3 ≤ B) (hs : ∀ i, e i 1 ≤ s)
    (hu : ∀ i, e i 1+e i 2+e i 3 ≤ U)
    (hl : ∀ i, e i 1+e i 2+e i 3+e i 4 ≤ L)
    (hd : ∀ i, e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1 < D (e i 1))
    (nodes : N ↪ K) (u0 u1 : N → K) (bound : ℕ)
    (hcard : bound+Fintype.card N*
      SecondJetRelaxedGlobalMap.rankBound m L B s U
        (fun h => (D h+B-1)/w) ≤ Fintype.card I) :
    ∃ V : Submodule K (WholeSpaceCube6814.Poly (K := K)), Module.Finite K V ∧
      bound ≤ Module.finrank K V ∧
      (∀ P ∈ V, ∀ d ∈ P.support, d ∈ Set.range e) ∧
      (∀ P ∈ V, ∀ n, MvPolynomial.X 0^m ∣ SecondJetDifferentiation.substitute (K := K)
        (localize (nodes n) (u0 n) (u1 n) P)) := by
  classical
  let caps := fun h => (D h+B-1)/w
  let f := SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps
  letI : AddCommGroup f.range := inferInstance
  letI : Module K f.range := f.range.module
  letI : FiniteDimensional K f.range := by
    change FiniteDimensional K
      (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range
    infer_instance
  let ell (n : N) : (I → K) →ₗ[K] SecondJetRelaxedSpace.source (K := K) m L B s U caps :=
    (coefficientLocal e m (nodes n) (u0 n) (u1 n)).codRestrict _
      (SecondJetRelaxedGlobalMap.coefficientLocal_mem e m L B s U w D hw
        (nodes n) (u0 n) (u1 n) hb hs hu hl hd)
  let g : (I → K) →ₗ[K] (N → f.range) :=
    LinearMap.pi (fun n => f.rangeRestrict.comp (ell n))
  have htarget : Module.finrank K (N → f.range) ≤
      Fintype.card N*SecondJetRelaxedGlobalMap.rankBound m L B s U caps := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    exact Nat.mul_le_mul_left _
      (SecondJetRelaxedGlobalMap.local_rank_le_count m L B s U caps)
  have hrange := g.range.finrank_le
  have hsum := g.finrank_range_add_finrank_ker
  have hdimI : Module.finrank K (I → K)=Fintype.card I := by simp
  have hkernel : bound ≤ Module.finrank K g.ker := by
    dsimp only [caps] at htarget
    omega
  let recon : g.ker →ₗ[K] WholeSpaceCube6814.Poly (K := K) :=
    (FiniteMonomials.reconstruct e).comp g.ker.subtype
  have hrecon : Function.Injective recon := by
    intro a b hh
    apply Subtype.ext
    exact FiniteMonomials.reconstruct_injective e he hh
  let V := recon.range
  have hdimV : bound ≤ Module.finrank K V := by
    rw [LinearMap.finrank_range_of_inj hrecon]
    exact hkernel
  refine ⟨V,inferInstance,hdimV,?_,?_⟩
  · rintro P ⟨c,rfl⟩
    exact (FiniteMonomials.mem_range_iff e he _).mp ⟨c.val,rfl⟩
  · rintro P ⟨c,rfl⟩ n
    have hc : g c.val=0 := c.property
    have hz := congrArg Subtype.val (congrFun hc n)
    change SecondJetRank.contactMap (K := K) m
      (coefficientLocal e m (nodes n) (u0 n) (u1 n) c.val)=0 at hz
    have hc' : Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (coefficientLocal e m (nodes n) (u0 n) (u1 n) c.val) :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hz
    have hh := untruncate_contact (SecondJetLocal.contact (K := K)).toRingHom
      Polynomial.X m _ SecondJetLocal.contact_X hc'
    exact SecondJetGlobalDifferentiation.nested_to_flat_contact _ m hh

theorem exists_contact_not_cube_generic
    (e : I → Fin 5 →₀ ℕ) (he : Function.Injective e)
    (hb : ∀ i, 2*e i 1+e i 3 ≤ 31) (hs : ∀ i, e i 1 ≤ 14)
    (hu : ∀ i, e i 1+e i 2+e i 3 ≤ 98)
    (hl : ∀ i, e i 1+e i 2+e i 3+e i 4 ≤ 1700)
    (hd : ∀ i, e i 0+131071*e i 2+131070*e i 3+131069*e i 1 < cutoff (e i 1))
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hcard : 627003341034+Fintype.card N*
      SecondJetRelaxedGlobalMap.rankBound 72 1700 31 14 98
        (fun h => (cutoff h+31-1)/131071) ≤ Fintype.card I)
    (J : WholeSpaceCube6814.Poly (K := K)) (hJ : J≠0)
    (hmid : 25 ≤ weightedTotalDegree middleWeights J)
    (hB : weightedTotalDegree slopeWeights J=9) :
    ∃ P : WholeSpaceCube6814.Poly (K := K), P≠0 ∧ ¬ J^3 ∣ P ∧ Bounds P ∧
      ∀ n, MvPolynomial.X 0^72 ∣ SecondJetDifferentiation.substitute (K := K)
        (localize (nodes n) (u0 n) (u1 n) P) := by
  obtain ⟨V,hfinite,hdim,hsupport,hcontact⟩ := exists_contact_kernel e he
    72 1700 31 14 98 131071 cutoff (by omega) hb hs hu hl hd nodes u0 u1 627003341034 hcard
  letI : Module.Finite K V := hfinite
  have hbounds : ∀ P ∈ V, Bounds P := by
    intro P hP d hd'
    obtain ⟨i,rfl⟩ := hsupport P hP d hd'
    exact ⟨hb i,hs i,hu i,hl i,hd i⟩
  obtain ⟨P,hP,hnot⟩ := exists_not_dvd_cube_uniform V hdim
    (fun P hP => (weights_of_bounds P (hbounds P hP)).1)
    (fun P hP => (weights_of_bounds P (hbounds P hP)).2.1)
    (fun P hP => (weights_of_bounds P (hbounds P hP)).2.2.1)
    (fun P hP => (weights_of_bounds P (hbounds P hP)).2.2.2.1) J hJ hmid hB
  refine ⟨P,?_,hnot,hbounds P hP,hcontact P hP⟩
  intro hz
  exact hnot (by rw [hz]; exact dvd_zero _)

abbrev SourceIndex := SecondJetRelaxedGlobalIndex.Index cutoff 131071 1700 31 14 98




theorem source_derivative_vanish (nodes : N ↪ K) (u0 u1 : N → K)
    (P : WholeSpaceCube6814.Poly (K := K)) (hP : Bounds P)
    (hcontact : ∀ i, MvPolynomial.X 0^72 ∣ SecondJetDifferentiation.substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (d : ℕ) (hd : d ≤ 2) (f : Polynomial K) (hf : f.natDegree ≤ 131071)
    (z : K) (S : Finset N) (hS : 181255 ≤ S.card)
    (hvalues : ∀ i ∈ S, f.eval (nodes i)=u0 i+u1 i*z) :
    SecondJetSpecialize.specialize f z ((pderiv 1)^[d] P)=0 := by
  apply SecondJetRelaxedDifferentiation.derivative_vanish P 72 181255 131071 2 3 d
    (by omega) (by omega) (by omega) hd ?_ nodes u0 u1 hcontact f hf z S hS hvalues
  intro e he
  have hh := (hP e he).2.2.2.2
  dsimp [cutoff] at hh
  norm_num
  omega







end
end ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814


