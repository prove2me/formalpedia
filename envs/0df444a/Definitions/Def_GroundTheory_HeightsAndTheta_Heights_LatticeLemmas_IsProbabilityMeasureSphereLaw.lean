-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:43.479372+00:00
-- url     : https://prove2.me/theorems/26b6b561-bd97-486f-9672-f9e3e9cfbb01
-- title:
--   Is Probability Measure Sphere Law
-- statement:
--   Definitions and structural lemmas for Is Probability Measure Sphere Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt
noncomputable section
section GaussNorms
def normAbv (L : Type*) [NormedField L] : AbsoluteValue L ℝ where
  toFun := norm
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' _ := norm_eq_zero
  add_le' := norm_add_le
variable {L : Type*} [Field L]
def affineSubst {ι κ : Type*} [Fintype κ] (B : Matrix ι κ L) (a : ι → L) (g : MvPolynomial ι L) :
    MvPolynomial κ L :=
  bind₁ (fun i ↦ ∑ j, C (B i j) * X j + C (a i)) g
end GaussNorms
def GaussNormBasic.Statement : Prop :=
  ∀ (L : Type) [NormedField L] [IsUltrametricDist L] [CompleteSpace L],

    (∀ (ι : Type) (g g' : MvPolynomial ι L),
      gaussNormOf (normAbv L) (g + g') ≤
          max (gaussNormOf (normAbv L) g) (gaussNormOf (normAbv L) g') ∧
        gaussNormOf (normAbv L) (g * g') ≤ gaussNormOf (normAbv L) g * gaussNormOf (normAbv L) g') ∧

    (∀ (ι κ : Type) [Fintype κ] (B : Matrix ι κ L) (a : ι → L), (∀ i j, ‖B i j‖ ≤ 1) →
      (∀ i, ‖a i‖ ≤ 1) → ∀ g : MvPolynomial ι L,
        gaussNormOf (normAbv L) (affineSubst B a g) ≤ gaussNormOf (normAbv L) g) ∧

    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι L) (a : ι → L), (∀ i j, ‖B i j‖ ≤ 1) →
      (∀ i, ‖a i‖ ≤ 1) → IsUnit B.det → (∀ i j, ‖B⁻¹ i j‖ ≤ 1) → ∀ g : MvPolynomial ι L,
        gaussNormOf (normAbv L) (affineSubst B a g) = gaussNormOf (normAbv L) g) ∧

    (∀ (ι κ : Type) [Fintype ι] [Fintype κ] (P : Matrix ι κ L), (∀ i k, ‖P i k‖ ≤ 1) →
      (∀ y : ι → L, (∀ i, ‖y i‖ ≤ 1) → ∃ x : κ → L, (∀ k, ‖x k‖ ≤ 1) ∧ P.mulVec x = y) →
      ∀ g : MvPolynomial ι L, gaussNormOf (normAbv L) (affineSubst P 0 g) = gaussNormOf (normAbv L) g)
def SchwartzZippelPerVariable.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] (q d : ℕ) (S : Finset R)
    (G : MvPolynomial (Fin q) R), G ≠ 0 → (∀ i, G.degreeOf i ≤ d) →
      ((Fintype.piFinset fun _ : Fin q ↦ S).filter fun c ↦ eval c G = 0).card ≤
        q * d * S.card ^ (q - 1)
def RootsOfUnityValuation.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → ∀ ζ : 𝓞 E, IsPrimitiveRoot ζ l →
    ∀ c c' : 𝓞 E, c ^ l = 1 → c' ^ l = 1 → c ≠ c' →
      (∃ u : (Algebra.adjoin ℤ {ζ})ˣ, c - c' = ((u : Algebra.adjoin ℤ {ζ}) : 𝓞 E) * (1 - ζ)) ∧
      (∃ u : (Algebra.adjoin ℤ {ζ})ˣ, (1 - ζ) ^ (l - 1) = ((u : Algebra.adjoin ℤ {ζ}) : 𝓞 E) * l) ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
        ((l : 𝓞 E) ∉ v.asIdeal →
          NumberField.HeightOneSpectrum.adicAbv E v ((c - c' : 𝓞 E) : E) = 1 ∧
          Set.InjOn (Ideal.Quotient.mk v.asIdeal) {x : 𝓞 E | x ^ l = 1} ∧
          l + 1 ≤ Nat.card (𝓞 E ⧸ v.asIdeal)) ∧
        ((l : 𝓞 E) ∈ v.asIdeal →
          NumberField.HeightOneSpectrum.adicAbv E v ((c - c' : 𝓞 E) : E) ^ (l - 1) =
            NumberField.HeightOneSpectrum.adicAbv E v (l : E) ∧
          l ≤ Nat.card (𝓞 E ⧸ v.asIdeal))
section Sphere
variable {n : ℕ}
def sphereBall (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j ↦ u (i, j)) < 1}
def sphereNormalize (h : HermNorm n) (k : ℕ) (u : Fin k × Fin n → ℂ) : Fin k × Fin n → ℂ :=
  fun ij ↦ ((h.norm fun j ↦ u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij
def SphereIntegrable (h : HermNorm n) (k : ℕ) (g : (Fin k × Fin n → ℂ) → ℝ) : Prop :=
  IntegrableOn (fun u ↦ g (sphereNormalize h k u)) (sphereBall h k)
def sphereLaw (N : ℕ) : Measure (Fin N → ℂ) :=
  (volume[|sphereBall (HermNorm.std N) 1]).map
    fun u j ↦ sphereNormalize (HermNorm.std N) 1 u (0, j)
def coordAlong (p z : Fin n → ℂ) : ℂ := ∑ j, z j * star (p j)
def orthoDir (p z : Fin n → ℂ) : Fin n → ℂ :=
  ((HermNorm.std n).norm (z - coordAlong p z • p) : ℂ)⁻¹ • (z - coordAlong p z • p)
def phaseLaw : Measure ℝ := volume[|Set.Ioc (-Real.pi) Real.pi]
end Sphere
def SphereProjectionLaw.Statement : Prop :=
  ∀ (N : ℕ) (p : Fin N → ℂ), ∑ j, ‖p j‖ ^ 2 = 1 →
    (N = 1 → ∀ᵐ z ∂sphereLaw N, ‖coordAlong p z‖ = 1) ∧
    (2 ≤ N →
      (∀ᵐ z ∂sphereLaw N,
        z = coordAlong p z • p + ((√(1 - ‖coordAlong p z‖ ^ 2) : ℝ) : ℂ) • orthoDir p z ∧
        coordAlong p (orthoDir p z) = 0 ∧ (HermNorm.std N).norm (orthoDir p z) = 1) ∧
      (sphereLaw N).map (fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))) =
        phaseLaw.prod ((sphereLaw N).map fun z ↦ (‖coordAlong p z‖, orthoDir p z)) ∧
      (sphereLaw N).map (fun z ↦ ‖coordAlong p z‖ ^ 2) =
        volume.withDensity fun x ↦
          ENNReal.ofReal (Set.indicator (Set.Icc 0 1) (fun x ↦ (N - 1 : ℝ) * (1 - x) ^ (N - 2)) x))
def PointwiseLelong.Statement : Prop :=
  ∀ (N d : ℕ) (Q : MvPolynomial (Fin N) ℂ), Q ≠ 0 → Q.IsHomogeneous d →
    (∀ p : Fin N → ℂ, ∑ j, ‖p j‖ ^ 2 = 1 → eval p Q ≠ 0 →
      SphereIntegrable (HermNorm.std N) 1 (fun u ↦ Real.log ‖eval (fun j ↦ u (0, j)) Q‖) ∧
      Real.log ‖eval p Q‖ - d * (harmonic (N - 1) : ℝ) / 2 ≤
        sphereMean (HermNorm.std N) 1 (fun u ↦ Real.log ‖eval (fun j ↦ u (0, j)) Q‖)) ∧
    (1 ≤ N →
      Real.log (⨆ z : {z : Fin N → ℂ // ∑ j, ‖z j‖ ^ 2 = 1}, ‖eval (z : Fin N → ℂ) Q‖) -
          d * (harmonic (N - 1) : ℝ) / 2 ≤
        sphereMean (HermNorm.std N) 1 (fun u ↦ Real.log ‖eval (fun j ↦ u (0, j)) Q‖))
def pairingForm {N : ℕ} (p : Fin N → ℂ) : MvPolynomial (Fin N) ℂ := ∑ j, C (star (p j)) * X j
def PointwiseLelongSharp.Statement : Prop :=
  ∀ (N d : ℕ) (p : Fin N → ℂ), ∑ j, ‖p j‖ ^ 2 = 1 →
    sphereMean (HermNorm.std N) 1 (fun u ↦ Real.log ‖eval (fun j ↦ u (0, j)) (pairingForm p ^ d)‖) =
      Real.log ‖eval p (pairingForm p ^ d)‖ - d * (harmonic (N - 1) : ℝ) / 2
section HeightsOfPoints
def intToField (F K : Type*) [Field F] [Field K] [Algebra F K] : 𝓞 F →+* K :=
  (algebraMap F K).comp (algebraMap (𝓞 F) F)
variable {F : Type*} [Field F] [NumberField F] {W : Type*} [AddCommGroup W] [Module (𝓞 F) W]
abbrev DualVec (F : Type*) [Field F] (W : Type*) [AddCommGroup W] [Module (𝓞 F) W]
    (K : Type*) [Field K] [Algebra F K] : Type _ :=
  W →ₛₗ[intToField F K] K
variable {K : Type*} [Field K] [NumberField K] [Algebra F K]
def dualNormAt (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (yv : DualVec F W K) : ℝ :=
  ⨆ x : W, NumberField.HeightOneSpectrum.adicAbv K v (yv x)
def archFunctional (τ : K →+* ℂ) (yv : DualVec F W K) :
    Fibre (τ.comp (algebraMap F K)) W →ₗ[𝓞 F] ComplexAt (τ.comp (algebraMap F K)) :=
  TensorProduct.lift
    (LinearMap.mk₂ (𝓞 F) (fun (z : ComplexAt (τ.comp (algebraMap F K))) (x : W) ↦
        z * ofComplex _ (τ (yv x)))
      (fun z₁ z₂ x ↦ add_mul _ _ _)
      (fun a z x ↦ smul_mul_assoc _ _ _)
      (fun z x₁ x₂ ↦ by rw [map_add, map_add, map_add, mul_add])
      (fun a z x ↦ by
        rw [map_smulₛₗ, smul_eq_mul, map_mul, map_mul, smul_def]
        simp only [intToField, RingHom.comp_apply]
        ring_nf))
variable [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]
def archDualNorm (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) : ℝ :=
  ⨆ ξ : {ξ : FibreSpace h (τ.comp (algebraMap F K)) // ‖ξ‖ ≤ 1},
    ‖(ofComplex _).symm (archFunctional τ yv ((FibreSpace.equiv h _).symm ξ))‖
def heightWith (h : HermitianMetric F W) (yv : DualVec F W K) (w : W) : ℝ :=
  -((Module.finrank ℚ K : ℝ)⁻¹ *
    ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv w) / dualNormAt v yv)) +
      ∑ τ : K →+* ℂ, Real.log (‖τ (yv w)‖ / archDualNorm h τ yv)))
def pointHeight (h : HermitianMetric F W) (yv : DualVec F W K) : ℝ :=
  heightWith h yv (Classical.epsilon fun w : W ↦ yv w ≠ 0)
def fibreGen (h : HermitianMetric F W) (σ : F →+* ℂ) {n : ℕ} (w : Fin n → W) (x : Fin n → ℂ) :
    FibreSpace h σ :=
  ∑ k, x k • fibreVec h σ (w k)
def fibrePoly (h : HermitianMetric F W) (σ : F →+* ℂ) {n : ℕ} (w : Fin n → W)
    (P : MvPolynomial (Fin n) ℂ) (ξ : FibreSpace h σ) : ℂ :=
  eval (Function.invFun (fibreGen h σ w) ξ) P
def fibreSphereMean (h : HermitianMetric F W) (σ : F →+* ℂ) (g : FibreSpace h σ → ℝ) : ℝ :=
  sphereMean (HermNorm.std (Module.finrank ℂ (FibreSpace h σ))) 1 fun u ↦
    g ((stdOrthonormalBasis ℂ (FibreSpace h σ)).repr.symm (WithLp.toLp 2 fun j ↦ u (0, j)))
def fibreMahler (h : HermitianMetric F W) (σ : F →+* ℂ) {n : ℕ} (w : Fin n → W)
    (P : MvPolynomial (Fin n) ℂ) : ℝ :=
  fibreSphereMean h σ fun ξ ↦ Real.log ‖fibrePoly h σ w P ξ‖
end HeightsOfPoints
def HeightOfPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (W : Type) [AddCommGroup W] [Module (𝓞 F) W]
    [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W] (h : HermitianMetric F W) (n : ℕ)
    (w : Fin n → W), Submodule.span (𝓞 F) (Set.range w) = ⊤ →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] (yv : DualVec F W K), yv ≠ 0 →
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        dualNormAt v yv = ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) ∧
        dualNormAt v yv = gaussNorm v (∑ k, C (yv (w k)) * X k)) ∧
      ∀ x : W, yv x ≠ 0 →
        heightWith h yv x = (Module.finrank ℚ K : ℝ)⁻¹ *
          ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (dualNormAt v yv)) +
            ∑ τ : K →+* ℂ, Real.log (archDualNorm h τ yv))
def HeightOfCycle.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (W : Type) [AddCommGroup W] [Module (𝓞 F) W]
    [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W] (h : HermitianMetric F W) (n : ℕ)
    (w : Fin n → W), Submodule.span (𝓞 F) (Set.range w) = ⊤ →
    ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K] [NumberField K]
      [Algebra F K] [Algebra E K] [IsScalarTower F E K] (m : ℕ) (yv : Fin m → DualVec F W K),
      (∀ q, yv q ≠ 0) → ∀ c : K, c ≠ 0 → ∀ P : MvPolynomial (Fin n) E,
      P.map (algebraMap E K) = C c * ∏ q, ∑ k, C (yv q (w k)) * X k →
        ∑ q, pointHeight h (yv q) = (Module.finrank ℚ E : ℝ)⁻¹ *
          ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Real.log (gaussNorm v P)) +
            ∑ σ : E →+* ℂ, (fibreMahler h (σ.comp (algebraMap F E)) w (P.map σ) +
              m * (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2))
section Inhabitants
example : IsUltrametricDist ℚ_[2] ∧ CompleteSpace ℚ_[2] := ⟨inferInstance, inferInstance⟩
theorem HermNorm.std_norm_eq {n : ℕ} (v : Fin n → ℂ) :
    (HermNorm.std n).norm v = √(∑ i, ‖v i‖ ^ 2) := by
  simp [HermNorm.norm, HermNorm.std]
theorem isOpen_sphereBall_std (N : ℕ) : IsOpen (sphereBall (HermNorm.std N) 1) := by
  have : sphereBall (HermNorm.std N) 1 = ⋂ i : Fin 1, {u | (HermNorm.std N).norm (fun j ↦ u (i, j)) < 1} := by
    ext u; simp [sphereBall]
  rw [this]
  refine isOpen_iInter_of_finite fun i ↦ isOpen_lt ?_ continuous_const
  simp only [HermNorm.std_norm_eq]
  fun_prop
theorem sphereBall_std_subset (N : ℕ) : sphereBall (HermNorm.std N) 1 ⊆ Metric.closedBall 0 1 := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro ij
  have h := hu ij.1
  rw [HermNorm.std_norm_eq] at h
  have hle : ‖u ij‖ ≤ √(∑ j, ‖u (ij.1, j)‖ ^ 2) := by
    rw [Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ by positivity)]
    have := Finset.single_le_sum (f := fun j ↦ ‖u (ij.1, j)‖ ^ 2) (fun _ _ ↦ by positivity)
      (Finset.mem_univ ij.2)
    simpa using this
  linarith
instance isProbabilityMeasure_sphereLaw (N : ℕ) : IsProbabilityMeasure (sphereLaw N) := by
  have h0 : volume (sphereBall (HermNorm.std N) 1) ≠ 0 := by
    refine ((isOpen_sphereBall_std N).measure_pos volume ⟨0, ?_⟩).ne'
    simp [sphereBall, HermNorm.std_norm_eq]
  have htop : volume (sphereBall (HermNorm.std N) 1) ≠ ⊤ :=
    ((measure_mono (sphereBall_std_subset N)).trans_lt
      (isCompact_closedBall 0 1).measure_lt_top).ne
  have := cond_isProbabilityMeasure_of_finite h0 htop
  unfold sphereLaw
  refine Measure.isProbabilityMeasure_map (Measurable.aemeasurable ?_)
  unfold sphereNormalize
  simp only [HermNorm.std_norm_eq]
  fun_prop
def ratPointVec : DualVec ℚ (Fin 2 → 𝓞 ℚ) ℚ where
  toFun x := (x 0 : ℚ) + 2 * (x 1 : ℚ)
  map_add' x y := by simp only [Pi.add_apply, map_add]; ring
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, intToField, RingHom.comp_apply,
      map_mul, Algebra.algebraMap_self, RingHom.id_apply]
    ring
end Inhabitants
end
end GroundTheory.Heights₂.Heights


