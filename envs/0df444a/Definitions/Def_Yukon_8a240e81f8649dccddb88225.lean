-- Prove2me | Definitions.Def_Yukon_8a240e81f8649dccddb88225
-- name    : Yukon_8a240e81f8649dccddb88225
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T04:47:29.844131+00:00
-- url     : https://prove2.me/theorems/16c0ff42-c433-469f-bb9a-4f615fd07b9e
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeSlice6812.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeSlice6812.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeSlice6812.lean
--
--   yukon-proof-operation:foundation-direct-f0bc05dc7d46072ef5576df1fadd5a6a0cde3d6651923679e71b350adbc24a96
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMDMwMjk3NzUxMDlhNDljOGU2ZWVmNjA1NDNhMWNkN2E3NzU1YjJiNWQxMTllZjg2MTFhY2U2ZmIxY2ZjODNiOSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWYwYmMwNWRjN2Q0NjA3MmVmNTU3NmRmMWZhZGQ1YTZhMGNkZTNkNjY1MTkyMzY3OWU3MWIzNTBhZGJjMjRhOTYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84YTI0MGU4MWY4NjQ5ZGNjZGRiODgyMjUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09

import Definitions.Def_Yukon_44eee9f2bbb5bf38cd30ce5d











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
# H-free bridge, piece 2a: slice descent

A slice component `D` (a prime of `E[Y,Y',Γ]` containing the surface and the slice equation
`ℓ - t`, with a coordinate transcendental over `E`) contracts to exactly `(G)` in
`Ω[Y,Y',Γ]` for the irreducible surface factor `G ∈ D`, and to exactly `(F₀)` in
`K[X,Y,Y',γ]` for an irreducible factor `F₀ ∣ F`.  So `L0 = Frac(K[X,Y,Y',γ]/(F₀))` embeds in
the slice function field `CoordinateField E D`.
-/

namespace ProximityPrize.SubmissionLower.HFree6812

open MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341

section Contraction

theorem coordEval_eq_zero_iff {E : Type} [Field E] (D : Ideal (MvPolynomial (Fin 3) E))
    [D.IsPrime] (x : MvPolynomial (Fin 3) E) : coordinateEvaluation E D x = 0 ↔ x ∈ D := by
  have h := coordinateEvaluation_ker E D
  constructor
  · intro hx
    rw [← h]
    exact hx
  · intro hx
    rw [← h] at hx
    exact hx

variable {Ω E : Type} [Field Ω] [Field E]
  [Algebra Ω E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E]

/-- The generic slice value `t`. -/
noncomputable abbrev sliceValue (Ω E : Type) [Field Ω] [Field E] [Algebra (RatFunc Ω) E] : E :=
  algebraMap (RatFunc Ω) E (rationalVariable Ω)

theorem sliceValue_transcendental : Transcendental Ω (sliceValue Ω E) := by
  have h : rationalVariable Ω = RatFunc.X := RatFunc.algebraMap_X
  rw [sliceValue, h, transcendental_algebraMap_iff (algebraMap (RatFunc Ω) E).injective]
  exact RatFunc.transcendental_X

omit [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E] in
/-- A slice component contains the image of an irreducible factor of any polynomial it
contains. -/
theorem exists_irreducible_mem (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (A : MvPolynomial (Fin 3) Ω) (hA : A ≠ 0) (hAD : scalarPolynomialMap Ω E A ∈ D) :
    ∃ G, Irreducible G ∧ G ∣ A ∧ scalarPolynomialMap Ω E G ∈ D := by
  classical
  revert hA hAD
  induction A using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ u hu =>
    intro _ hAD
    exact absurd (Ideal.eq_top_of_isUnit_mem D hAD (hu.map _)) Ideal.IsPrime.ne_top'
  | h₃ a q ha hq ih =>
    intro hA hAD
    rw [map_mul] at hAD
    rcases Ideal.IsPrime.mem_or_mem inferInstance hAD with h | h
    · exact ⟨q, hq.irreducible, dvd_mul_right q a, h⟩
    · obtain ⟨G, hG, hGa, hGD⟩ := ih ha h
      exact ⟨G, hG, hGa.mul_left q, hGD⟩

/-- **Slice contraction.** -/
theorem slice_comap_eq (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep : SeparableLiteralCoordinate D) (G : MvPolynomial (Fin 3) Ω) (hG : Irreducible G)
    (hGD : scalarPolynomialMap Ω E G ∈ D) (c : Fin 3 → Ω) (i : Fin 3) (hci : c i = 1)
    (hslice : MvPolynomial.C (sliceValue Ω E) -
      scalarPolynomialMap Ω E (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D) :
    D.comap (scalarPolynomialMap Ω E) = Ideal.span {G} := by
  classical
  have hev : ∀ A : MvPolynomial (Fin 3) Ω,
      aeval (coordinate E D) A = coordinateEvaluation E D (scalarPolynomialMap Ω E A) := by
    intro A
    rw [coordinateEvaluation_eq_aeval, scalarPolynomialMap, aeval_map_algebraMap]
  have hzero : ∀ A : MvPolynomial (Fin 3) E, A ∈ D → coordinateEvaluation E D A = 0 :=
    fun A hA => (coordEval_eq_zero_iff D A).2 hA
  apply le_antisymm
  · intro P hP
    rw [Ideal.mem_span_singleton]
    by_contra hGP
    have hℓ : ∑ m, algebraMap Ω (CoordinateField E D) (c m) * coordinate E D m =
        algebraMap E (CoordinateField E D) (sliceValue Ω E) := by
      have h1 := hzero _ hslice
      rw [map_sub, sub_eq_zero] at h1
      rw [← hev] at h1
      have h2 : coordinateEvaluation E D (MvPolynomial.C (sliceValue Ω E)) =
          algebraMap E (CoordinateField E D) (sliceValue Ω E) :=
        (coordinateEvaluation E D).commutes _
      rw [h2] at h1
      rw [h1]
      simp only [map_sum, map_mul, aeval_C, aeval_X]
    have halg := coordinates_algebraic_of_not_dvd G P hG hGP (coordinate E D)
      (by rw [hev]; exact hzero _ hGD) (by rw [hev]; exact hzero _ hP) i c hci
      (sliceValue Ω E) sliceValue_transcendental hℓ
    exact sep.transcendental (halg sep.index)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hGD

end Contraction

section Descent

variable {K : Type} [Field K] {E : Type} [Field E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

/-- The coefficient map of the certificate, `K[X,Y,Y',γ] → CoordinateField E D`. -/
noncomputable def sliceMap (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] :
    MvPolynomial (Fin 4) K →+* CoordinateField E D :=
  (coordinateEvaluation E D).toRingHom.comp
    (surfaceMap ((algebraMap (GenericField K) E).comp (polynomialEmbedding K)))

omit [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem surfaceMap_generic_eq (A : MvPolynomial (Fin 4) K) :
    surfaceMap ((algebraMap (GenericField K) E).comp (polynomialEmbedding K)) A =
      scalarPolynomialMap (GenericField K) E (surfaceMap (polynomialEmbedding K) A) := by
  simp only [surfaceMap, scalarPolynomialMap, RingHom.comp_apply, MvPolynomial.map_map]

/-- **Slice descent**: the kernel of the slice map is generated by an irreducible factor. -/
theorem slice_descent (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep : SeparableLiteralCoordinate D) (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hFD : surfaceMap ((algebraMap (GenericField K) E).comp (polynomialEmbedding K)) F ∈ D)
    (c : Fin 3 → GenericField K) (i : Fin 3) (hci : c i = 1)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D) :
    ∃ F₀ : MvPolynomial (Fin 4) K, Irreducible F₀ ∧ F₀ ∣ F ∧
      RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀} := by
  classical
  set φ := polynomialEmbedding K
  have hA : surfaceMap φ F ≠ 0 := surfaceMap_ne_zero φ (polynomialEmbedding_injective K) F hF
  have hAD : scalarPolynomialMap (GenericField K) E (surfaceMap φ F) ∈ D := by
    rw [← surfaceMap_generic_eq]; exact hFD
  obtain ⟨G, hG, -, hGD⟩ := exists_irreducible_mem D (surfaceMap φ F) hA hAD
  have hcomap := slice_comap_eq D sep G hG hGD c i hci hslice
  have hker : RingHom.ker (sliceMap (K := K) D) = originalPrime (Ideal.span {G}) := by
    ext A
    rw [RingHom.mem_ker, mem_originalPrime_iff, ← hcomap, Ideal.mem_comap,
      ← surfaceMap_generic_eq]
    exact coordEval_eq_zero_iff D _
  haveI hGprime : (Ideal.span {G}).IsPrime :=
    (Ideal.span_singleton_prime hG.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hG)
  have hGheight : (Ideal.span {G}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hG.ne_zero) hG.not_isUnit
  set Q := RingHom.ker (sliceMap (K := K) D)
  haveI hQprime : Q.IsPrime := RingHom.ker_isPrime _
  have hQheight : Q.height ≤ 1 := by
    rw [hker, ← hGheight]
    exact originalPrime_height_le _
  have hFQ : F ∈ Q := (coordEval_eq_zero_iff D _).2 hFD
  have hQbot : Q ≠ ⊥ := by
    intro h; rw [h] at hFQ; exact hF ((Submodule.mem_bot _).mp hFQ)
  obtain ⟨F₀, hF₀Q, hF₀⟩ := hQprime.exists_mem_prime_of_ne_bot hQbot
  haveI hF₀prime : (Ideal.span {F₀}).IsPrime := (Ideal.span_singleton_prime hF₀.ne_zero).mpr hF₀
  have hF₀height : (Ideal.span {F₀}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hF₀.ne_zero) hF₀.not_unit
  have hle : Ideal.span {F₀} ≤ Q := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hF₀Q
  have heq : Ideal.span {F₀} = Q := by
    by_contra hne
    have hlt := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hF₀height] at hlt
    have h2 : (2 : ℕ∞) ≤ 1 := hlt.trans hQheight
    exact absurd h2 (by decide)
  refine ⟨F₀, hF₀.irreducible, ?_, heq.symm⟩
  rw [← Ideal.mem_span_singleton, heq]
  exact hFQ

end Descent

section SliceField

open RCN313 RCN055 RCN077 RCN188

variable {K : Type} [Field K] (F F₀ : MvPolynomial (Fin 4) K) [hF₀ : Fact (Irreducible F₀)]

/-- `K[X,Y,Y',γ]/(F₀)`. -/
abbrev SliceRing := MvPolynomial (Fin 4) K ⧸ Ideal.span {F₀}

instance sliceRing_isPrime : (Ideal.span {F₀}).IsPrime :=
  (Ideal.span_singleton_prime hF₀.out.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hF₀.out)

instance  _root_.ProximityPrize.SubmissionLower.HFree6812.instIsDomainSliceRing : IsDomain (SliceRing F₀) := Ideal.Quotient.isDomain _

/-- `L0 = Frac(K[X,Y,Y',γ]/(F₀))`, the field on which the H-free derivation acts. -/
abbrev SliceField := FractionRing (SliceRing F₀)

/-- `K[X,Y,Y',γ] → L0`. -/
noncomputable def sliceProj : MvPolynomial (Fin 4) K →+* SliceField F₀ :=
  (algebraMap (SliceRing F₀) (SliceField F₀)).comp (Ideal.Quotient.mk _)

omit hF₀ in
theorem sliceProj_eq_zero_iff (A : MvPolynomial (Fin 4) K) : sliceProj F₀ A = 0 ↔ F₀ ∣ A := by
  rw [sliceProj, RingHom.comp_apply,
    map_eq_zero_iff _ (IsFractionRing.injective (SliceRing F₀) (SliceField F₀)),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

omit hF₀ in
/-- `baseDerivation F` preserves `(F₀)` when `F₀ ∣ F`. -/
theorem baseDerivation_stable (hdvd : F₀ ∣ F) :
    ∀ P ∈ Ideal.span {F₀}, baseDerivation F P ∈ Ideal.span {F₀} := by
  obtain ⟨F₁, rfl⟩ := hdvd
  have h0 : baseDerivation (F₀ * F₁) F₀ ∈ Ideal.span {F₀} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨MvPolynomial.pderiv 2 F₁ * (MvPolynomial.pderiv 0 F₀ +
        MvPolynomial.X 2 * MvPolynomial.pderiv 1 F₀) -
      (MvPolynomial.pderiv 0 F₁ + MvPolynomial.X 2 * MvPolynomial.pderiv 1 F₁) *
        MvPolynomial.pderiv 2 F₀, ?_⟩
    rw [baseDerivation_apply, polyH, polyG]
    simp only [Derivation.leibniz, smul_eq_mul]
    ring
  intro P hP
  obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton.mp hP
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  exact (Ideal.span {F₀}).add_mem
    ((Ideal.span {F₀}).mul_mem_right _ (Ideal.mem_span_singleton_self F₀))
    ((Ideal.span {F₀}).mul_mem_left _ h0)

/-- The cleared derivation `H · D` on `L0`. -/
noncomputable def clearedSliceDerivation (hdvd : F₀ ∣ F) :
    Derivation K (SliceField F₀) (SliceField F₀) :=
  localizationDerivation (nonZeroDivisors (SliceRing F₀))
    (quotientDerivation (baseDerivation F) (Ideal.span {F₀}) (baseDerivation_stable F F₀ hdvd))

/-- The H-free derivation `D = ∂_X + Y' ∂_Y + σ ∂_{Y'}` on `L0`, `σ = G/H`. -/
noncomputable def sliceDerivation (hdvd : F₀ ∣ F) :
    Derivation K (SliceField F₀) (SliceField F₀) :=
  (sliceProj F₀ (polyH K F))⁻¹ • clearedSliceDerivation F F₀ hdvd

theorem sliceDerivation_proj (hdvd : F₀ ∣ F) (P : MvPolynomial (Fin 4) K) :
    sliceDerivation F F₀ hdvd (sliceProj F₀ P) =
      sliceProj F₀ (baseDerivation F P) / sliceProj F₀ (polyH K F) := by
  rw [sliceDerivation, Derivation.smul_apply, smul_eq_mul, div_eq_inv_mul]
  congr 1
  simp only [clearedSliceDerivation, sliceProj, RingHom.comp_apply]
  rw [localizationDerivation_algebraMap, quotientDerivation_mk]

/-- `D` in coordinates: `D P = (∂_X P + Y' ∂_Y P) + ∂_{Y'} P · σ`. -/
theorem sliceDerivation_proj_eq (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0)
    (P : MvPolynomial (Fin 4) K) :
    sliceDerivation F F₀ hdvd (sliceProj F₀ P) =
      sliceProj F₀ (MvPolynomial.pderiv 0 P + MvPolynomial.X 2 * MvPolynomial.pderiv 1 P) +
        sliceProj F₀ (MvPolynomial.pderiv 2 P) *
          (sliceProj F₀ (polyG K F) / sliceProj F₀ (polyH K F)) := by
  rw [sliceDerivation_proj, baseDerivation_apply]
  simp only [map_add, map_mul]
  field_simp

/-- The H-free first cut: `D^m (Y') = baseNumerator (m-1) / H^(2m-1)`. -/
theorem sliceDerivation_iterate (hdvd : F₀ ∣ F) (hH : sliceProj F₀ (polyH K F) ≠ 0) (n : ℕ) :
    (⇑(sliceDerivation F F₀ hdvd))^[n + 1] (sliceProj F₀ (MvPolynomial.X 2)) =
      sliceProj F₀ (baseNumerator F n) / sliceProj F₀ (polyH K F) ^ (2 * n + 1) := by
  induction n with
  | zero =>
    rw [Function.iterate_one, sliceDerivation_proj, baseDerivation_R]
    simp [baseNumerator]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz_div, Derivation.leibniz_pow,
      sliceDerivation_proj, sliceDerivation_proj]
    simp only [baseNumerator, smul_eq_mul, nsmul_eq_mul, map_sub, map_mul, map_natCast,
      Nat.add_sub_cancel]
    field_simp
    ring

end SliceField

section Embedding

variable {K : Type} [Field K] {E : Type} [Field E]
  [Algebra (GenericField K) E] (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
  (F₀ : MvPolynomial (Fin 4) K) [hF₀ : Fact (Irreducible F₀)]

/-- The embedding `ψ : L0 → CoordinateField E D` when `ker (sliceMap D) = (F₀)`. -/
noncomputable def sliceEmbedding (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀}) :
    SliceField F₀ →+* CoordinateField E D :=
  IsFractionRing.lift (A := SliceRing F₀)
    (g := Ideal.Quotient.lift (Ideal.span {F₀}) (sliceMap (K := K) D) (fun a ha => by
      rw [← hker] at ha; exact ha))
    ((Ideal.injective_lift_iff _).mpr hker)

theorem sliceEmbedding_proj (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})
    (A : MvPolynomial (Fin 4) K) :
    sliceEmbedding D F₀ hker (sliceProj F₀ A) = sliceMap (K := K) D A := by
  rw [sliceEmbedding, sliceProj, RingHom.comp_apply, IsFractionRing.lift_algebraMap,
    Ideal.Quotient.lift_mk]

end Embedding

end ProximityPrize.SubmissionLower.HFree6812


