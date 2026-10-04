-- Prove2me | Definitions.Def_Yukon_1bcd4c4ffdf14561f9186504
-- name    : Yukon_1bcd4c4ffdf14561f9186504
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T01:37:50.407411+00:00
-- url     : https://prove2.me/theorems/5352d34b-7a03-40f9-bfa0-e9a42b9be4eb
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceProjectionFamily6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceProjectionFamily6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceProjectionFamily6814.lean
--
--   yukon-proof-operation:certificate-b56-619607c543d45e40a82031d63de59bf980d5849bfc2b56ea637c1874e5da47e9
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzI0ZjkwNDcxYTUwOGI5YzJlZmYxYTA4NTQxMjYxNjNjOWI3OTVmNDViY2IyYjAwMzRkMzIxMzJjOWE4YzMxMyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni02MTk2MDdjNTQzZDQ1ZTQwYTgyMDMxZDYzZGU1OWJmOTgwZDU4NDliZmMyYjU2ZWE2MzdjMTg3NGU1ZGE0N2U5IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMWJjZDRjNGZmZGYxNDU2MWY5MTg2NTA0IiwidiI6Mn0]

import Definitions.Def_Yukon_8b752c0e6702f9aedd4b860b














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Shared projection degree for an irreducible plane cut, without assuming
that its degree in the chosen outer variable is positive. -/
namespace ProximityPrize.SubmissionLower.MovingSourceProjectionFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN371 RCN011 RCN009 RCN013 RCN008 RCN021 RCN022
open RCN095 RCN125 RCN093 RCN123 RCN121 RCN084 RCN137 RCN071

theorem finite_sum_finrank_projection
    (K : Type) [Field K] (order : Fin 3 ≃ Fin 3) {I : Type} [Fintype I]
    (E : I → Type) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    (e : ∀ i, Original K →ₐ[K] E i)
    (ht : ∀ i, Transcendental K (e i (MvPolynomial.X (order 0))))
    (hgen : ∀ i,
      letI : Algebra (RatFunc K) (E i) :=
        (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
          (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))} : Set (E i))=⊤)
    (hkernels : Function.Injective (fun i => RingHom.ker (e i).toRingHom))
    (G H : Original K) (hG : Irreducible G)
    (hGroot : ∀ i, e i G=0) (hHroot : ∀ i, e i H=0) (hproper : ¬G∣H) :
    letI : ∀ i, Algebra (RatFunc K) (E i) := fun i =>
      (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
        (ht i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (E i)) ∧
      (∑ i, Module.finrank (RatFunc K) (E i)) ≤
        (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree := by
  classical
  letI : ∀ i, Algebra (RatFunc K) (E i) := fun i =>
    (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
      (ht i)).toRingHom.toAlgebra
  by_cases hI : Nonempty I
  · let i₀ : I := Classical.choice hI
    have hirr : Irreducible (planeMap K order G) :=
      planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
        G hG (hGroot i₀) (ht i₀)
    have hproperPlane : ¬planeMap K order G ∣ planeMap K order H := by
      intro hdiv
      exact hproper ((planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
        G H hG (hGroot i₀) (ht i₀)).mp hdiv)
    have hGroots : ∀ i, RCN361.planeEval (RatFunc K) (E i)
        (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
        (planeMap K order G)=0 := by
      intro i
      change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order G)=0
      rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
      exact hGroot i
    have hHroots : ∀ i, RCN361.planeEval (RatFunc K) (E i)
        (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
        (planeMap K order H)=0 := by
      intro i
      change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order H)=0
      rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
      exact hHroot i
    have hrelation : Function.Injective (fun i => RCN361.relationIdeal (RatFunc K) (E i)
        (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))) := by
      intro i j hij
      apply hkernels
      change relationKernel K (E i) order (e i) (ht i)=
        relationKernel K (E j) order (e j) (ht j) at hij
      have hc := congrArg (Ideal.comap (planeMap K order)) hij
      simpa only [relationKernel_contract] using hc
    exact MovingSourceVerticalFamily6814.finite_sum_finrank_irreducible E
      (planeMap K order G) (planeMap K order H) hirr hproperPlane
      (fun i => e i (MvPolynomial.X (order 2)))
      (fun i => e i (MvPolynomial.X (order 1))) hgen hrelation hGroots hHroots
  · letI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    exact ⟨fun i => isEmptyElim i,by simp⟩

/-- Every factor is charged to the original cumulative flags once.
No derivative-active restriction drops the vertical components. -/
theorem all_factors_mixed_sum_le
    {K : Type} [Field K] (B : MvPolynomial (Fin 3) K) (hB : B≠0)
    (p q r : FlagDegree) (hsupport : RCN095.PolynomialInFlag p B) :
    (∑ g : ↥(normalizedFactorSet B), flagMixed (exactFlag g.1) q r) ≤ flagMixed p q r := by
  classical
  have hc := inFlag_weight_caps B p hsupport
  have hw (w : Fin 3 → ℕ) :
      (∑ g : ↥(normalizedFactorSet B), MvPolynomial.weightedTotalDegree w g.1) ≤
        MvPolynomial.weightedTotalDegree w B := by
    rw [Finset.sum_coe_sort]
    exact sum_weightedTotalDegree_le_of_prod_dvd_fin3 w (normalizedFactorSet B) id B hB
      (normalizedFactorSet_product_dvd B hB)
  apply sum_flagMixed_le_of_cumulative
  · simpa only [(exactFlag_cumulative _).1] using (hw flagSWeights).trans hc.1
  · calc
      _=∑ g : ↥(normalizedFactorSet B), MvPolynomial.weightedTotalDegree flagYSWeights g.1 :=
        Finset.sum_congr rfl (fun g _ => (exactFlag_cumulative g.1).2.1)
      _ ≤ _ := (hw flagYSWeights).trans hc.2.1
  · calc
      _=∑ g : ↥(normalizedFactorSet B), MvPolynomial.weightedTotalDegree flagTotalWeights g.1 :=
        Finset.sum_congr rfl (fun g _ => (exactFlag_cumulative g.1).2.2)
      _ ≤ _ := (hw flagTotalWeights).trans hc.2.2

inductive Axis | z | u | v

def Axis.order : Axis → (Fin 3 ≃ Fin 3)
  | .z => zOrder
  | .u => uOrder
  | .v => vOrder

def Axis.flag : Axis → FlagDegree
  | .z => unitZFlag
  | .u => unitYZFlag
  | .v => unitAllFlag

theorem flag_resultant_degree_le
    {K : Type} [Field K] (axis : Axis) (lam mu nu : K)
    (G H : MvPolynomial (Fin 3) K) (p q : FlagDegree)
    (hG : RCN095.PolynomialInFlag p G) (hH : RCN095.PolynomialInFlag q H) (hHne : H≠0) :
    (Polynomial.resultant (planeMap K axis.order (flagAlgHom lam mu nu G))
      (planeMap K axis.order (flagAlgHom lam mu nu H))).natDegree ≤ flagMixed p q axis.flag := by
  have hGs := (support_subset_flagSupport_iff _ _).mpr hG
  have hHs := (support_subset_flagSupport_iff _ _).mpr hH
  cases axis with
  | z => exact RCN112.flagPlaneResultant_z_degree_le p q lam mu nu hGs hHs hHne
  | u => exact RCN112.flagPlaneResultant_u_degree_le p q lam mu nu hGs hHs hHne
  | v => exact RCN112.flagPlaneResultant_v_degree_le p q lam mu nu hGs hHs hHne







end
end ProximityPrize.SubmissionLower.MovingSourceProjectionFamily6814


