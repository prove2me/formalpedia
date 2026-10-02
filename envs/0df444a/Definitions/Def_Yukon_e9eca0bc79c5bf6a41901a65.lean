-- Prove2me | Definitions.Def_Yukon_e9eca0bc79c5bf6a41901a65
-- name    : Yukon_e9eca0bc79c5bf6a41901a65
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:41:54.979121+00:00
-- url     : https://prove2.me/theorems/bddeac5e-d0fe-4bd9-b62d-fcdfd5e945a8
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.ActualSliceMultiplicity6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.ActualSliceMultiplicity6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/ActualSliceMultiplicity6807.lean
--
--   yukon-proof-operation:foundation-direct-c4cef4c927fecccad6305d4cd53e748d1000271e37a9092728cbd1954e07d490
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOWQ1M2JlZTNjZjY4MjkyYzMzOTRhZTUxYjE2NGFmNGFiY2VjN2M1NTIwZGQ0NjQwZGRjNThhMWVmYzBjMzFkNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWM0Y2VmNGM5MjdmZWNjY2FkNjMwNWQ0Y2Q1M2U3NDhkMTAwMDI3MWUzN2E5MDkyNzI4Y2JkMTk1NGUwN2Q0OTAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9lOWVjYTBiYzc5YzViZjZhNDE5MDFhNjUiLCJ2IjoyfQ]

/-
UNCOMPILED. Concrete original multiplicity transfer into a prime slice quotient.
Unlike the former generic-ring adapter, factor=0 and contraction are derived
from the actual Stage originalData, an embedding point, and its slice prime.
The underlying prime D may be singular; no multiplicity equality is assumed.
-/
import Definitions.Def_Yukon_84e6160981e0608a7da1d940

import Definitions.Def_Yukon_02a5cf55f4aedeb35d6b4dd1










































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.ActualSliceMultiplicity6807
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095
open RCN134 RCN135 RCN136 RCN208 RCN217 RCN244 RCN248 RCN313
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
variable {K I E : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance  _root_.ProximityPrize.SubmissionLower.ActualSliceMultiplicity6807.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.ActualSliceMultiplicity6807.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "PK4" => MvPolynomial (Fin 4) K

def originalToSlice (D : Ideal PE) : PK4 →+* CoordinateRing E D :=
  (Ideal.Quotient.mk D).comp ((scalarPolynomialMap Ω E).comp
    (surfaceMap (polynomialEmbedding K)))

def slicePoint (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (emb : CoordinateField Ω C.1 →ₐ[Ω] E)
    (D : Ideal PE)
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint C.1 emb) : PE →ₐ[E] E).toRingHom) :
    PointOn E D := ⟨embeddingPoint C.1 emb, hD⟩

theorem originalToSlice_point_value
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (emb : CoordinateField Ω C.1 →ₐ[Ω] E)
    (D : Ideal PE) [D.IsPrime]
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint C.1 emb) : PE →ₐ[E] E).toRingHom)
    (F : PK4) :
    pointHom E D (slicePoint S C emb D hD) (originalToSlice (K := K) D F) =
      emb (coordinateEvaluation Ω C.1 (surfaceMap (polynomialEmbedding K) F)) := by
  change MvPolynomial.eval (embeddingPoint C.1 emb)
    (scalarPolynomialMap Ω E (surfaceMap (polynomialEmbedding K) F)) = _
  exact GenericSlicePoints6807.scalar_eval_embedding C.1 emb _

theorem slice_point_kernel_contracts
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (emb : CoordinateField Ω C.1 →ₐ[Ω] E)
    (D : Ideal PE) [D.IsPrime]
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint C.1 emb) : PE →ₐ[E] E).toRingHom) :
    Ideal.comap (originalToSlice (K := K) D)
      (RingHom.ker (pointHom E D (slicePoint S C emb D hD)).toRingHom) =
        componentPrime S C := by
  ext F
  change pointHom E D (slicePoint S C emb D hD) (originalToSlice D F) = 0 ↔
    surfaceMap (polynomialEmbedding K) F ∈ C.1
  rw [originalToSlice_point_value S C emb D hD,
    map_eq_zero_iff emb emb.injective]
  change surfaceMap (polynomialEmbedding K) F ∈
    RingHom.ker (coordinateEvaluation Ω C.1).toRingHom ↔ _
  rw [coordinateEvaluation_ker Ω C.1]

theorem original_factor_zero
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (D : Ideal PE) [D.IsPrime]
    (hcarrier : scalarPolynomialMap Ω E S.G ∈ D) :
    originalToSlice (K := K) D (originalData S C).factor = 0 := by
  change Ideal.Quotient.mk D
    (scalarPolynomialMap Ω E
      (surfaceMap (polynomialEmbedding K) (originalData S C).factor)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact D.mem_of_dvd (map_dvd (scalarPolynomialMap Ω E)
    (originalData S C).factor_dvd) hcarrier

def firstTailInSlice
    (S : Stage K I Gamma x p flag errorCap stageSupport) (D : Ideal PE) :
    CoordinateRing E D :=
  Ideal.Quotient.mk D (scalarPolynomialMap Ω E
    (globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1)))

def firstTailScalarInSlice (D : Ideal PE) : CoordinateRing E D :=
  Ideal.Quotient.mk D (scalarPolynomialMap Ω E
    (MvPolynomial.C ((-(polynomialEmbedding K) Polynomial.X)^(RCN326.w+1))))

theorem firstTailInSlice_factorization
    (S : Stage K I Gamma x p flag errorCap stageSupport) (D : Ideal PE) :
    firstTailInSlice S D = originalToSlice (K := K) D
      (numerator K S.F (RCN326.w+1)) * firstTailScalarInSlice (K := K) D := by
  simp only [firstTailInSlice, firstTailScalarInSlice, originalToSlice,
    globalTailCut_eq, map_mul, RingHom.comp_apply]

/-- Full old multiplicity in the actual slice quotient and point ideal. -/
theorem actual_first_tail_mem_point_power
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (C : FirstTailComponent S) (emb : CoordinateField Ω C.1 →ₐ[Ω] E)
    (D : Ideal PE) [D.IsPrime]
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint C.1 emb) : PE →ₐ[E] E).toRingHom)
    (hcarrier : scalarPolynomialMap Ω E S.G ∈ D) :
    firstTailInSlice S D ∈
      (RingHom.ker (pointHom E D (slicePoint S C emb D hD)).toRingHom) ^
        localMultiplicity S (canonicalLocalDVRFamily S hproper) C := by
  let phi := pointHom E D (slicePoint S C emb D hD)
  let J := RingHom.ker phi.toRingHom
  letI : J.IsMaximal := RCN017.pointKernel_isMaximal phi
  have hf := original_factor_zero S C D hcarrier
  have hc := slice_point_kernel_contracts S C emb D hD
  have h := proper_global_tail_mem_projected_primary S hproper C
    (originalToSlice (K := K) D) 0 (firstTailInSlice S D)
    (firstTailScalarInSlice (K := K) D) J
    (by rw [hf]; exact Ideal.zero_mem _)
    (J.zero_mem) hc (firstTailInSlice_factorization S D)
  simpa [J] using h

/-- Nonzero at the chosen point, not globally invertible in the affine ring. -/
theorem original_H_point_ne_zero
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (emb : CoordinateField Ω C.1 →ₐ[Ω] E)
    (D : Ideal PE) [D.IsPrime]
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint C.1 emb) : PE →ₐ[E] E).toRingHom) :
    pointHom E D (slicePoint S C emb D hD)
      (originalToSlice (K := K) D (polyH K S.F)) ≠ 0 := by
  rw [originalToSlice_point_value S C emb D hD]
  intro hz
  have he := (map_eq_zero_iff emb emb.injective).mp hz
  apply RCN312.firstTailComponent_regularity_not_mem S C
  rw [← coordinateEvaluation_ker Ω C.1]
  exact he


/-- Scalar extension commutes with freezing the original X-coordinate. -/
theorem scalar_surfaceMap (F : PK4) :
    scalarPolynomialMap Ω E (surfaceMap (polynomialEmbedding K) F) =
      surfaceMap ((algebraMap Ω E).comp (polynomialEmbedding K)) F := by
  simp only [RCN208.scalarPolynomialMap, RCN136.surfaceMap,
    RingHom.comp_apply, MvPolynomial.map_map]

theorem firstTailScalar_point_value
    (D : Ideal PE) [D.IsPrime] (point : PointOn E D) :
    pointHom E D point (firstTailScalarInSlice (K := K) D) =
      algebraMap Ω E ((-(polynomialEmbedding K) Polynomial.X)^(RCN326.w+1)) := by
  simp only [firstTailScalarInSlice, pointHom_mk,
    RCN208.scalarPolynomialMap, MvPolynomial.map_C, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]

theorem firstTailScalar_point_ne_zero
    (D : Ideal PE) [D.IsPrime] (point : PointOn E D) :
    pointHom E D point (firstTailScalarInSlice (K := K) D) ≠ 0 := by
  rw [firstTailScalar_point_value]
  exact (map_ne_zero (algebraMap Ω E)).mpr (tail_scalar_ne_zero (polynomialEmbedding K)
    (polynomialEmbedding_injective K) (RCN326.w+1))

/-- The normalization is derived from the frozen numerator_H_cube identity. -/
theorem firstTailInSlice_normal_form
    (S : Stage K I Gamma x p flag errorCap stageSupport) (D : Ideal PE) :
    firstTailInSlice S D = firstTailScalarInSlice (K := K) D *
      (originalToSlice (K := K) D (polyH K S.F))^3 *
        originalToSlice (K := K) D (baseNumerator S.F (RCN326.w-1)) := by
  rw [firstTailInSlice_factorization,
    show RCN326.w+1 = (RCN326.w-1)+2 by decide,
    numerator_eq_H_cube, map_mul, map_pow]
  ring

/-- Coordinate evaluation of an original polynomial is the fraction-field
image of its concrete quotient-ring representative. -/
theorem originalToSlice_fraction_value (D : Ideal PE) [D.IsPrime] (F : PK4) :
    algebraMap (CoordinateRing E D) (CoordinateField E D)
      (originalToSlice (K := K) D F) =
      coordinateEvaluation E D
        (surfaceMap ((algebraMap Ω E).comp (polynomialEmbedding K)) F) := by
  change coordinateEvaluation E D
    (scalarPolynomialMap Ω E (surfaceMap (polynomialEmbedding K) F)) = _
  rw [scalar_surfaceMap]

/-- Membership of the first tail in a prime slice is equivalent to vanishing
of its quotient representative; isolation provides the negated membership. -/
theorem firstTailInSlice_ne_zero
    (S : Stage K I Gamma x p flag errorCap stageSupport) (D : Ideal PE)
    (hproper : scalarPolynomialMap Ω E
      (globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1)) ∉ D) :
    firstTailInSlice S D ≠ 0 := by
  intro hz
  exact hproper (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- Keep the exponent w+3 explicitly, before cancelling in the function field. -/
theorem normalized_first_tail_identity {A L : Type*}
    [CommRing A] [Field L] (ev : A →+* L)
    (tail base H kappa : A) (w : ℕ)
    (hrel : tail = kappa * H^3 * base)
    (hH : ev H ≠ 0) (hk : ev kappa ≠ 0) :
    ev tail / ev (kappa * H^(w+3)) = ev base / (ev H)^w := by
  rw [hrel]
  simp only [map_mul, map_pow]
  rw [pow_add]
  field_simp
  <;> ring

end
end ProximityPrize.SubmissionLower.ActualSliceMultiplicity6807


