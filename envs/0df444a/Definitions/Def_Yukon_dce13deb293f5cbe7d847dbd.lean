-- Prove2me | Definitions.Def_Yukon_dce13deb293f5cbe7d847dbd
-- name    : Yukon_dce13deb293f5cbe7d847dbd
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T01:52:19.618517+00:00
-- url     : https://prove2.me/theorems/baef7538-1cbe-4513-b9e8-6714b9d4518d
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceSharedFamily6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceSharedFamily6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceSharedFamily6814.lean
--
--   yukon-proof-operation:certificate-b56-5edf0c1519067bc59950fe99e5931e130ea75a8444eb8234fd615c8a82a97f32
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMmJjZjkwZWE3MTViOWIyOThiOWQwMGEzMThiZDJiNjIxYmFhMWY3MzFkZmQwNGU1ZmM0NDI1ZjNiMzhmZDVjMCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni01ZWRmMGMxNTE5MDY3YmM1OTk1MGZlOTllNTkzMWUxMzBlYTc1YTg0NDRlYjgyMzRmZDYxNWM4YTgyYTk3ZjMyIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fZGNlMTNkZWIyOTNmNWNiZTdkODQ3ZGJkIiwidiI6Mn0]

import Definitions.Def_Yukon_1bcd4c4ffdf14561f9186504













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! A whole finite curve family is bounded by ONE mixed flag budget of
the actual coprime pair. The first cut may be reducible, repeated, or
independent of the chosen outer variable. -/
namespace ProximityPrize.SubmissionLower.MovingSourceSharedFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN371 RCN011 RCN022 RCN095 RCN093 RCN123 RCN121 RCN084 RCN137
open RCN125 (flagAlgHom flag_irreducible_iff flag_dvd_iff)
open MovingSourceProjectionFamily6814

theorem finite_sum_finrank_coprime_flags
    (K : Type) [Field K] (axis : Axis) (lam mu nu : K) {I : Type} [Fintype I]
    (E : I → Type) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    (e : ∀ i, Original K →ₐ[K] E i)
    (ht : ∀ i, Transcendental K (e i (MvPolynomial.X (axis.order 0))))
    (hgen : ∀ i,
      letI : Algebra (RatFunc K) (E i) :=
        (elementEmbedding K (E i) (e i (MvPolynomial.X (axis.order 0)))
          (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (axis.order 2)),e i (MvPolynomial.X (axis.order 1))} :
          Set (E i))=⊤)
    (hkernels : Function.Injective (fun i => RingHom.ker (e i).toRingHom))
    (B H : Original K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBroot : ∀ i, e i (flagAlgHom lam mu nu B)=0)
    (hHroot : ∀ i, e i (flagAlgHom lam mu nu H)=0)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H) :
    letI : ∀ i, Algebra (RatFunc K) (E i) := fun i =>
      (elementEmbedding K (E i) (e i (MvPolynomial.X (axis.order 0)))
        (ht i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (E i)) ∧
      (∑ i, Module.finrank (RatFunc K) (E i)) ≤ flagMixed p q axis.flag := by
  classical
  letI : ∀ i, Algebra (RatFunc K) (E i) := fun i =>
    (elementEmbedding K (E i) (e i (MvPolynomial.X (axis.order 0)))
      (ht i)).toRingHom.toAlgebra
  have hex : ∀ i, ∃ g : ↥(normalizedFactorSet B), e i (flagAlgHom lam mu nu g.1)=0 := by
    intro i
    obtain ⟨g,hg,hroot⟩ := exists_normalizedFactorSet_zero
      ((e i).toRingHom.comp (flagAlgHom lam mu nu).toRingHom) B hB (hBroot i)
    exact ⟨⟨g,hg⟩,hroot⟩
  choose owner howner using hex
  have hgroup (g : ↥(normalizedFactorSet B)) :
      (∀ i : {i // owner i=g}, FiniteDimensional (RatFunc K) (E i.1)) ∧
        (∑ i : {i // owner i=g}, Module.finrank (RatFunc K) (E i.1)) ≤
          flagMixed (exactFlag g.1) q axis.flag := by
    have hg := normalizedFactorSet_spec B g.1 g.2
    have hproper : ¬g.1∣H := fun hgH => hg.1.not_isUnit (hrel hg.2 hgH)
    have hker : Function.Injective
        (fun i : {i // owner i=g} => RingHom.ker (e i.1).toRingHom) := by
      intro i j hij
      exact Subtype.ext (hkernels hij)
    have hgroot : ∀ i : {i // owner i=g}, e i.1 (flagAlgHom lam mu nu g.1)=0 := by
      intro i
      have hh := howner i.1
      rw [i.2] at hh
      exact hh
    have hb := finite_sum_finrank_projection K axis.order
      (fun i : {i // owner i=g} => E i.1)
      (fun i => e i.1) (fun i => ht i.1) (fun i => hgen i.1) hker
      (flagAlgHom lam mu nu g.1) (flagAlgHom lam mu nu H)
      ((flag_irreducible_iff lam mu nu g.1).mpr hg.1)
      hgroot (fun i => hHroot i.1) (by simpa only [flag_dvd_iff] using hproper)
    exact ⟨hb.1,hb.2.trans (flag_resultant_degree_le axis lam mu nu g.1 H
      (exactFlag g.1) q (polynomialIn_exactFlag g.1) hq hH)⟩
  refine ⟨fun i => (hgroup (owner i)).1 ⟨i,rfl⟩,?_⟩
  calc
    (∑ i, Module.finrank (RatFunc K) (E i))=
        ∑ g : ↥(normalizedFactorSet B),
          ∑ i : {i // owner i=g}, Module.finrank (RatFunc K) (E i.1) :=
      (Fintype.sum_fiberwise owner (fun i => Module.finrank (RatFunc K) (E i))).symm
    _ ≤ ∑ g : ↥(normalizedFactorSet B), flagMixed (exactFlag g.1) q axis.flag :=
      Finset.sum_le_sum (fun g _ => (hgroup g).2)
    _ ≤ flagMixed p q axis.flag := all_factors_mixed_sum_le B hB p q axis.flag hp



end
end ProximityPrize.SubmissionLower.MovingSourceSharedFamily6814


