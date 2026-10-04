-- Prove2me | Definitions.Def_Yukon_55fad66368719f3e76698681
-- name    : Yukon_55fad66368719f3e76698681
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T23:56:54.894705+00:00
-- url     : https://prove2.me/theorems/f9804d9a-706d-4fd5-ab5c-827df1f28123
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceFlatBaseChange6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceFlatBaseChange6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceFlatBaseChange6814.lean
--
--   yukon-proof-operation:certificate-r12-pair-split-febc9940cca00c0bbb82b1734e5961a6211dc22d57dab4c59aa52d9e90ff6a65
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTkxNWZmMDhjMzc3YWU2NTAyZjViZmUwMWM3NWJhMzJhYTRiZmYwMmY1Y2ZhOTNiODUxMTVkMDhiYTNkYjU3OSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMi1wYWlyLXNwbGl0LWZlYmM5OTQwY2NhMDBjMGJiYjgyYjE3MzRlNTk2MWE2MjExZGMyMmQ1N2RhYjRjNTlhYTUyZDllOTBmZjZhNjUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81NWZhZDY2MzY4NzE5ZjNlNzY2OTg2ODEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_f9b1aa1ba67da67faf9565ef











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Transport properness through the injective flat coefficient changes
used by the generic moving-fiber construction. -/
namespace ProximityPrize.SubmissionLower.MovingSourceFlatBaseChange6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open UniqueFactorizationMonoid

section Flat
variable {A B : Type*} [CommRing A] [IsDomain A]
  [UniqueFactorizationMonoid A]
  [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B] [IsNoetherianRing B]
  [Algebra A B] [Module.Flat A B]

theorem map_isRelPrime_of_flat (hinj : Function.Injective (algebraMap A B))
    (P Q : A) (hP : P≠0) (hrel : IsRelPrime P Q) :
    IsRelPrime (algebraMap A B P) (algebraMap A B Q) := by
  classical
  apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
  · rintro ⟨hz,_⟩
    exact hP (hinj (by simpa only [map_zero] using hz))
  intro g hg hgP hgQ
  let I : Ideal B := Ideal.span {g}
  haveI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hg.prime
  let psi : A →+* B ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap A B)
  have hz : psi P=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hgP)
  obtain ⟨factors,hfactors,hprod⟩ := WfDvdMonoid.exists_factors P hP
  have hassoc := Associated.map psi hprod
  rw [hz] at hassoc
  have hp : psi factors.prod=0 := (associated_zero_iff_eq_zero _).mp hassoc
  rw [map_multiset_prod] at hp
  obtain ⟨f,hf,hfzero⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  have hfi : Irreducible f := hfactors f hf
  have hgf : g ∣ algebraMap A B f :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hfzero)
  have he := RCN350.under_prime_factor_eq hinj f hfi.prime g hg.prime hgf
  have hQmem : Q ∈ (Ideal.span ({g} : Set B)).under A := Ideal.mem_span_singleton.mpr hgQ
  rw [he] at hQmem
  exact hfi.not_isUnit (hrel ((Multiset.dvd_prod hf).trans hprod.dvd) (Ideal.mem_span_singleton.mp hQmem))

end Flat

section Coefficients
variable {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat R S]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_map_flat : Module.Flat (MvPolynomial σ R) (MvPolynomial σ S) := by
  exact Module.Flat.of_linearEquiv
    (Algebra.IsPushout.equiv R (MvPolynomial σ R) S (MvPolynomial σ S)).symm.toLinearEquiv

end Coefficients

section Equivalence
variable {A B : Type*} [CommRing A] [CommRing B]

theorem isRelPrime_equiv (e : A ≃+* B) (P Q : A) (h : IsRelPrime P Q) :
    IsRelPrime (e P) (e Q) := by
  intro d hdP hdQ
  have hP := map_dvd e.symm hdP
  have hQ := map_dvd e.symm hdQ
  simp only [RingEquiv.symm_apply_apply] at hP hQ
  have hu := (h hP hQ).map e.toMonoidHom
  change IsUnit (e (e.symm d)) at hu
  simpa only [RingEquiv.apply_symm_apply] using hu

end Equivalence





end
end ProximityPrize.SubmissionLower.MovingSourceFlatBaseChange6814


