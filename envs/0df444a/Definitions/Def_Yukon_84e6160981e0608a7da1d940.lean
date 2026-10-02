-- Prove2me | Definitions.Def_Yukon_84e6160981e0608a7da1d940
-- name    : Yukon_84e6160981e0608a7da1d940
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:03:04.371773+00:00
-- url     : https://prove2.me/theorems/83e95ea2-c09b-43ac-8efb-cc8fa2f2a218
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.GenericSlicePoints6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.GenericSlicePoints6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/GenericSlicePoints6807.lean
--
--   yukon-proof-operation:foundation-direct-c0f0467ca7203661e3d7747a90972037cddd4fcc013a4cbbde373bfdca82d8fd-parser-retry
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOGY5MjA4ZDIxZGI4YWY3MzUxMWY4MDkxMTE0M2NhNjQ2NTc4MmQ4NmM5NDgwNDEzMWZlYWVjNTYwYjE4ZjVhOSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWMwZjA0NjdjYTcyMDM2NjFlM2Q3NzQ3YTkwOTcyMDM3Y2RkZDRmY2MwMTNhNGNiYmRlMzczYmZkY2E4MmQ4ZmQtcGFyc2VyLXJldHJ5IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fODRlNjE2MDk4MWUwNjA4YTdkYTFkOTQwIiwidiI6Mn0]

/-
UNCOMPILED. Concrete generic-fiber point construction from the pinned APIs.
The nonlinear elimination theorem RCN202.embedding_point_certificate is used
at k=0, H=U=1, G=0. Its equation becomes t-ell and its cut becomes A.
In particular IsolatedPoint is a conclusion here, not an assumed cut budget.
-/
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09







































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.GenericSlicePoints6807
open scoped Classical BigOperators
open RCN002 RCN072 RCN264 RCN207 RCN208 RCN134 RCN084
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 300000

variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
local notation "Poly" => MvPolynomial (Fin 3) K
local notation "PE" => MvPolynomial (Fin 3) E

theorem filteredCut_zero {R : Type*} [CommRing R] (A H G : R) :
    filteredCut 0 (fun _ : Fin 1 => A) H G = A := by
  simp [filteredCut, Fin.sum_univ_succ]

def sliceEquation (ell : Poly) : PE :=
  MvPolynomial.C (algebraMap (RatFunc K) E (RCN202.rationalVariable K)) -
    scalarPolynomialMap K E ell

/-- Drop only the auxiliary regularity gate; the underlying prime is unchanged.
This is what permits the old k=0 theorem to use H=1 while preserving the original
H*c exclusion separately in the resulting point certificate. -/
abbrev gateOneComponent (F A R : Poly) (C : RegularComponent K F A R) :
    RegularComponent K F (filteredCut 0 (fun _ : Fin 1 => A) 1 0) 1 :=
  ⟨C.1, by
    classical
    apply (mem_regularComponents K).mpr
    constructor
    · simpa only [filteredCut_zero] using regularComponent_mem K F A R C
    · intro h
      have hz : coordinateEvaluation K C.1 (1 : Poly) = 0 := by
        apply RingHom.mem_ker.mp
        change (1 : Poly) ∈ RingHom.ker (coordinateEvaluation K C.1).toRingHom
        rwa [coordinateEvaluation_ker K C.1]
      exact one_ne_zero (by simpa only [map_one] using hz)⟩

omit [IsAlgClosed E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] in
theorem scalar_eval_embedding (P : Ideal Poly) [P.IsPrime]
    (f : CoordinateField K P →ₐ[K] E) (A : Poly) :
    MvPolynomial.eval (embeddingPoint P f) (scalarPolynomialMap K E A) =
      f (coordinateEvaluation K P A) := by
  have h := AlgHom.congr_fun (embeddingPoint_aeval P f) A
  change MvPolynomial.eval (embeddingPoint P f)
    (MvPolynomial.map (algebraMap K E) A) = _
  rw [MvPolynomial.eval_map]
  exact h

omit [IsAlgClosed E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] in
theorem scalar_eval_ne_zero (P : Ideal Poly) [P.IsPrime]
    (f : CoordinateField K P →ₐ[K] E) (A : Poly) (hA : A ∉ P) :
    MvPolynomial.eval (embeddingPoint P f) (scalarPolynomialMap K E A) ≠ 0 := by
  rw [scalar_eval_embedding]
  intro h
  apply hA
  rw [← coordinateEvaluation_ker K P]
  exact (map_eq_zero_iff f f.injective).mp h

theorem embedding_point_certificate
    (F A R ell : Poly) (C : RegularComponent K F A R)
    [Algebra (RatFunc K) (CoordinateField K C.1)]
    [IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
    [FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
    (hj : algebraMap (RatFunc K) (CoordinateField K C.1)
      (RCN202.rationalVariable K) = coordinateEvaluation K C.1 ell)
    (f : CoordinateField K C.1 →ₐ[RatFunc K] E) :
    let mu := scalarPolynomialMap K E
    let v := embeddingPoint C.1 (f.restrictScalars K)
    MvPolynomial.eval v (mu F) = 0 ∧
      MvPolynomial.eval v (sliceEquation (E := E) ell) = 0 ∧
      MvPolynomial.aeval v (mu A) = 0 ∧
      MvPolynomial.eval v (mu R) ≠ 0 ∧
      IsolatedPoint (mu F) (sliceEquation (E := E) ell) (mu A) v := by
  let C0 := gateOneComponent F A R C
  have hj0 : algebraMap (RatFunc K) (CoordinateField K C0.1)
      (RCN202.rationalVariable K) = movingValue C0.1 1 0 ell 1 := by
    simpa only [movingValue, map_one, map_zero, mul_zero, zero_div, add_zero]
      using hj
  have h1 : (1 : Poly) ∉ C0.1 := regularComponent_H_not_mem K _ _ _ C0
  have hcert := RCN202.embedding_point_certificate F 1 0 ell 1 0
    (fun _ : Fin 1 => A) C0 hj0 h1 f
  have hc :
      MvPolynomial.eval (embeddingPoint C.1 (f.restrictScalars K))
        (scalarPolynomialMap K E F) = 0 ∧
      MvPolynomial.eval (embeddingPoint C.1 (f.restrictScalars K))
        (sliceEquation (E := E) ell) = 0 ∧
      MvPolynomial.aeval (embeddingPoint C.1 (f.restrictScalars K))
        (scalarPolynomialMap K E A) = 0 ∧
      MvPolynomial.eval (embeddingPoint C.1 (f.restrictScalars K)) (1 : PE) ≠ 0 ∧
      IsolatedPoint (scalarPolynomialMap K E F) (sliceEquation (E := E) ell)
        (scalarPolynomialMap K E A) (embeddingPoint C.1 (f.restrictScalars K)) := by
    simpa only [map_one, map_zero,
      movingEquation, eliminatedCut, filteredCut_zero, one_mul, mul_zero,
      sub_zero, sliceEquation] using hcert
  exact ⟨hc.1, hc.2.1, hc.2.2.1,
    scalar_eval_ne_zero C.1 (f.restrictScalars K) R
      (regularComponent_H_not_mem K F A R C), hc.2.2.2.2⟩

section WeightedEmbeddings
variable {I : Type} [Fintype I]
  (P : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (P i).IsPrime]
  [∀ i, Algebra (RatFunc K) (CoordinateField K (P i))]
  [∀ i, IsScalarTower K (RatFunc K) (CoordinateField K (P i))]
  [∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i))]
  [∀ i, Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))]

/-- The left side is weighted embeddings, not merely a number of points.
Separability is indispensable for AlgHom.card = finrank. -/
theorem weighted_embedding_sum (weight : I → ℕ) :
    (∑ z : (Σ i, CoordinateField K (P i) →ₐ[RatFunc K] E), weight z.1) =
      ∑ i, weight i * Module.finrank (RatFunc K) (CoordinateField K (P i)) := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, AlgHom.card, mul_comm]

end WeightedEmbeddings
end
end ProximityPrize.SubmissionLower.GenericSlicePoints6807


