-- Prove2me | Definitions.Def_OAIQWPP000
-- name    : OAIQWPP000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:07:27.871034+00:00
-- url     : https://prove2.me/theorems/7555a55e-ffbf-4cb7-ab29-c9dc4a524c32
-- title:
--   OpenAI Petty projection-volume split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of Petty's projection-volume conjecture in dimensions $n \ge 4$ (`OAI.PettyProjection.petty_projection_volume`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Geometry/ProjectionBodies` (OpenAI, *Petty's projection-volume conjecture in dimensions at least four*, OpenAI Math Release, September 24, 2026, result family 088, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Examples are the normalized spherical measure `Spherical.sigma` and mean `Spherical.mean`, the spherical $L^2$ space `Spherical.H` with the projection `Spherical.Q`, the harmonic subspaces `Spherical.harmonicSpace`, the support function `support`, `volumeRoot`, `normalizedVolume`, `supportFunctional`, `measurePair`, `cosineSeminorm`, the structure `RelativeGauge` and `RelativeGauge.IsMinimizer`. The bundle also contains the lemmas those definitions use in their bodies (for example `Spherical.seminorm_continuous`, which appears inside statements, and the proof fields of structures), and OpenAI's `@[simp]` lemmas about these definitions.
--
--   The definitions of the published statement (`Space`, `IsConvexBody`, `unitBall`, `kappa`, `perpendicular`, `shadowVolume`, `projectionBody`, `projectionRatio`, `pettyConstant`, `IsEllipsoid`) are not repeated: the bundle imports them from the published bundle `Def_PettyProjectionVolume`. It imports no other bundle.
--
--   Three compatibility lemmas that newer Lean versions provide under these names (`ite_eq_left`, `ite_eq_right`, `dite_eq_right`, which are `if_pos`, `if_neg` and `dif_neg`) are declared at the top, in the namespace `OAI.PettyProjection`.
--
--   Two of the bundle's lemmas carry line-level edits of the port for this Mathlib. In `unifIntegrable_of_sq_bound`, this Mathlib's `unifIntegrable_of` quantifies over a real $\varepsilon > 0$, so the proof drops its case split on $\varepsilon = \infty$ and uses $\varepsilon$ in place of `ε.toReal`. It also drops the measurability argument of `eLpNorm_one_eq_lintegral_enorm`, which takes none here. In `tendsto_integral_of_sq_bound`, `tendsto_integral_of_L1'` takes an extra measurability argument, which the port supplies.
--
--   Modules: `SphericalCore.lean`, `Support.lean`, `SphericalGap.lean`, `NormCurvature.lean`, `ScalarBounds.lean`, `ScalarCalculus.lean`, `NormEstimates.lean`, `CosineCalculus.lean`, `WulffVariation.lean`, `ShadowSlices.lean`, `SliceTransport.lean`, `BrunnMinkowski.lean`, `Homothety.lean`, `SupportMeasures.lean`, `SignCalculus.lean`, `CosineSpectrum.lean`, `SignSpectrum.lean`, `NormRigidity.lean`, `SeminormBounds.lean`, `RelativeGauges.lean`, `VariationalMinimizers.lean`, `VariationalRepresentation.lean`, `FixedPointCalculus.lean`, `GaussianMeasures.lean`, `RankContinuity.lean`, `PositionMatrices.lean`, `AffinePosition.lean`, `BilinearEquality.lean`, `Normalization.lean`, `AffineCovariance.lean`.
--
--   The theorems that the definitions do not need are proved in the ten solutions of this split. Five prove classical results, published as standalone statements: the absence of a $C^1$ retraction of the ball onto its sphere (OpenAI's ingredient for Brouwer's theorem), the Brunn–Minkowski inequality (concavity form in $\mathbb R^n$ and additive form in any finite-dimensional inner product space), its equality case, and Minkowski's first inequality. Brouwer's fixed-point theorem itself is not republished: OpenAI's `fixedPoint_compact_convex` is a one-line application of the published standalone statement `AGT.brouwer_fixed_point`. Four prove the intermediate statements `OAI.PettyProjection.RelativeGauge.exists_symmetric_position`, `OAI.PettyProjection.Spherical.norm_estimate`, `OAI.PettyProjection.Spherical.norm_sign_form` and `OAI.PettyProjection.measure_bilinear`. The last proves `OAI.PettyProjection.petty_projection_volume` from them. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Petty's projection-volume conjecture in dimensions at least four, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 088; Apache License 2.0); definitions carved from lean/OAI/Geometry/ProjectionBodies at commit adc7f12

import Mathlib
import Definitions.Def_PettyProjectionVolume

section
-- module Solutions.OAIQW_PettyProjection.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
namespace OAI.PettyProjection
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434
end OAI.PettyProjection
end

section
-- module Solutions.OAIQW_PettyProjection.SphericalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise

namespace PettyProjection.Spherical

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := sphere (0 : Space n) 1

def surface (n : ℕ) : Measure (Sphere n) :=
  (volume : Measure (Space n)).toSphere

def sigma (n : ℕ) : Measure (Sphere n) :=
  (surface n univ)⁻¹ • surface n

instance surface_finite (n : ℕ) : IsFiniteMeasure (surface n) := by
  unfold surface
  infer_instance

lemma surface_ne_zero (n : ℕ) [NeZero n] : surface n ≠ 0 := by
  exact Measure.toSphere_ne_zero _

instance sigma_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (sigma n) := by
  constructor
  rw [sigma, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (Measure.measure_univ_ne_zero.mpr (surface_ne_zero n)) (measure_ne_top _ _)

instance surface_open_pos (n : ℕ) : (surface n).IsOpenPosMeasure := by
  unfold surface
  infer_instance

instance sigma_open_pos (n : ℕ) : (sigma n).IsOpenPosMeasure := by
  exact Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

/-- Spherical means in the probability normalization. -/
def mean {n : ℕ} (f : Sphere n → ℝ) : ℝ := ∫ u, f u ∂sigma n

instance sphere_compact (n : ℕ) : CompactSpace (Sphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Space n) 1)

lemma norm_coe {n : ℕ} (u : Sphere n) : ‖(u : Space n)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using u.property

/-- Continuous functions are put into the actual spherical L² space. -/
abbrev H (n : ℕ) := Lp ℝ 2 (sigma n)

def toH (n : ℕ) [NeZero n] : C(Sphere n, ℝ) →L[ℝ] H n :=
  ContinuousMap.toLp 2 (sigma n) ℝ

/-- Restrictions of ambient coordinate quadratics. Their span contains the
constants on the unit sphere and all degree-two spherical harmonics. -/
def coordinateProduct (n : ℕ) (i j : Fin n) : C(Sphere n, ℝ) where
  toFun u := (u : Space n) i * (u : Space n) j
  continuous_toFun := by fun_prop

def lowSpace (n : ℕ) [NeZero n] : Submodule ℝ (H n) :=
  Submodule.span ℝ (Set.range fun ij : Fin n × Fin n =>
    toH n (coordinateProduct n ij.1 ij.2))

instance lowSpace_finite (n : ℕ) [NeZero n] : FiniteDimensional ℝ (lowSpace n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- The complement of the constants and the quadratics. For even input this
is exactly the even tail of degree at least four. -/
def Q (n : ℕ) [NeZero n] : H n →L[ℝ] H n :=
  (lowSpace n)ᗮ.starProjection

/-- Orthogonal changes of variables on the actual unit sphere. -/
def sphereMap {n : ℕ} (U : Space n ≃ₗᵢ[ℝ] Space n) : Sphere n ≃ₜ Sphere n where
  toFun u := ⟨U u, by simpa only [mem_sphere, dist_zero_right, U.norm_map] using norm_coe u⟩
  invFun u := ⟨U.symm u, by simpa only [mem_sphere, dist_zero_right, U.symm.norm_map] using norm_coe u⟩
  left_inv u := by ext; simp
  right_inv u := by ext; simp
  continuous_toFun := (U.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (U.symm.continuous.comp continuous_subtype_val).subtype_mk _

lemma cone_preimage {n : ℕ} (U : Space n ≃ₗᵢ[ℝ] Space n) (s : Set (Sphere n)) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereMap U ⁻¹' s)) =
      U ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨r, hr, U u, ⟨sphereMap U u, hu, rfl⟩, by simp⟩
  · rintro ⟨r, hr, y, ⟨v, hv, rfl⟩, heq⟩
    refine ⟨r, hr, U.symm v, ⟨(sphereMap U).symm v, ?_, rfl⟩, ?_⟩
    · simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hv
    · have hh := congrArg U.symm heq
      simpa only [map_smul, U.symm_apply_apply] using hh

lemma surface_preserving {n : ℕ} (U : Space n ≃ₗᵢ[ℝ] Space n) :
    MeasurePreserving (sphereMap U) (surface n) (surface n) := by
  refine ⟨(sphereMap U).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereMap U).measurable hs, surface,
    Measure.toSphere_apply' _ ((sphereMap U).measurable hs),
    Measure.toSphere_apply' _ hs, cone_preimage]
  rw [U.measurePreserving.measure_preimage_emb U.toHomeomorph.measurableEmbedding]

lemma sigma_preserving {n : ℕ} (U : Space n ≃ₗᵢ[ℝ] Space n) :
    MeasurePreserving (sphereMap U) (sigma n) (sigma n) :=
  (surface_preserving U).smul_measure _

lemma mean_rotation {n : ℕ} (U : Space n ≃ₗᵢ[ℝ] Space n) (f : Sphere n → ℝ) :
    mean (fun u => f (sphereMap U u)) = mean f :=
  (sigma_preserving U).integral_comp (sphereMap U).measurableEmbedding f

local instance instCompleteSpaceContinuousLinearMapRealIdSpace (n : ℕ) : CompleteSpace (Space n →L[ℝ] Space n) :=
  FiniteDimensional.complete ℝ _

local instance instNormedAlgebraRatContinuousLinearMapRealIdSpace (n : ℕ) : NormedAlgebra ℚ (Space n →L[ℝ] Space n) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- Exponentiating an actual skew-adjoint operator produces rotations. -/
def rotation {n : ℕ} (T : Space n →L[ℝ] Space n) (hT : star T = -T) (t : ℝ) :
    Space n ≃ₗᵢ[ℝ] Space n :=
  Unitary.linearIsometryEquiv ⟨NormedSpace.exp (t • T),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
      rw [skewAdjoint.mem_iff, star_smul, star_trivial, hT, smul_neg])⟩

lemma continuous_integrable {n : ℕ} [NeZero n] {f : Sphere n → ℝ}
    (hf : Continuous f) : Integrable f (sigma n) := by
  simpa only [integrableOn_univ] using
    hf.continuousOn.integrableOn_compact (μ := sigma n) isCompact_univ

/-- Derivative along an infinitesimal linear rotation. -/
def rotDeriv {n : ℕ} (T : Space n →L[ℝ] Space n) (f : Space n → ℝ) : Space n → ℝ :=
  fun x => fderiv ℝ f x (T x)

lemma continuous_rotDeriv {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (rotDeriv T f) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply T.continuous

lemma contDiff_rotDeriv {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (rotDeriv T f) :=
  (hf.fderiv_right (by norm_num)).clm_apply T.contDiff

/-- The standard skew generator in the i,j plane. -/
def generator (n : ℕ) (i j : Fin n) : Space n →L[ℝ] Space n :=
  InnerProductSpace.rankOne ℝ (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) -
    InnerProductSpace.rankOne ℝ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- The Dirichlet form, expressed without local coordinates by rotations. -/
def energy {n : ℕ} (f g : Space n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
    mean (fun u : Sphere n => rotDeriv (generator n i j) f u *
      rotDeriv (generator n i j) g u)

/-- The spherical Laplacian expressed by its rotation generators. -/
def casimir {n : ℕ} (f : Space n → ℝ) : Space n → ℝ := fun x =>
  (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
    rotDeriv (generator n i j) (rotDeriv (generator n i j) f) x

/-- Ambient evaluation of a polynomial, using the Euclidean coordinates. -/
def polynomialFunction {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Space n → ℝ :=
  fun x => MvPolynomial.eval (fun i => x i) p

lemma polynomialFunction_contDiff {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ⊤ (polynomialFunction p) := by
  unfold polynomialFunction
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contDiff_const : ContDiff ℝ ⊤ (fun _ : Space n => c))
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp =>
    have hi : ContDiff ℝ ⊤ (fun x : Space n => x i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul hi

/-- Polynomial rotation differentiation, a derivation preserving degree. -/
def polynomialRotation {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.X i * MvPolynomial.pderiv j p - MvPolynomial.X j * MvPolynomial.pderiv i p

open MvPolynomial

/-- Radius squared as an ambient polynomial. -/
def radiusPolynomial (n : ℕ) : MvPolynomial (Fin n) ℝ := ∑ i : Fin n, X i ^ 2

def eulerPolynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, X i * pderiv i p

def laplacePolynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, pderiv i (pderiv i p)

/-- The spherical Laplace eigenvalues. -/
def eigenvalue (n d : ℕ) : ℝ := (d : ℝ) * ((d : ℝ) + n - 2)

lemma laplacePolynomial_add {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    laplacePolynomial (p + q) = laplacePolynomial p + laplacePolynomial q := by
  simp [laplacePolynomial, Finset.sum_add_distrib]

lemma laplacePolynomial_C_mul {n : ℕ} (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    laplacePolynomial (C c * p) = C c * laplacePolynomial p := by
  simp [laplacePolynomial, Finset.mul_sum]

/-- The nonzero radial coefficient in the finite Fischer decomposition. -/
def radialCoefficient (n l j : ℕ) : ℝ := 2 * (j + 1 : ℕ) * (2 * l + 2 * (j + 1 : ℕ) + n - 2)

lemma laplacePolynomial_smul {n : ℕ} (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    laplacePolynomial (c • p) = c • laplacePolynomial p := by
  simpa only [← C_mul'] using laplacePolynomial_C_mul c p

/-- Algebraic span of radius powers times homogeneous harmonics of fixed total degree. -/
def fischerSpan (n d : ℕ) : Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  Submodule.span ℝ {q | ∃ j l p, 2 * j + l = d ∧ p.IsHomogeneous l ∧
    laplacePolynomial p = 0 ∧ q = radiusPolynomial n ^ j * p}

/-- Actual polynomial restrictions, as continuous functions on the sphere. -/
def polynomialRestriction (n : ℕ) : MvPolynomial (Fin n) ℝ →ₐ[ℝ] C(Sphere n, ℝ) where
  toFun p := ⟨fun u => polynomialFunction p u,
    (polynomialFunction_contDiff p).continuous.comp continuous_subtype_val⟩
  map_zero' := by
    ext u
    change MvPolynomial.eval (fun i => (u : Space n) i) 0 = 0
    exact map_zero _
  map_one' := by
    ext u
    change MvPolynomial.eval (fun i => (u : Space n) i) 1 = 1
    exact map_one _
  map_add' p q := by ext u; exact MvPolynomial.eval_add
  map_mul' p q := by ext u; exact MvPolynomial.eval_mul
  commutes' c := by ext u; exact MvPolynomial.eval_C _

def polynomialL2 (n : ℕ) [NeZero n] : MvPolynomial (Fin n) ℝ →ₗ[ℝ] H n :=
  (toH n).toLinearMap.comp (polynomialRestriction n).toLinearMap

def laplaceLinear (n : ℕ) : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun := laplacePolynomial
  map_add' := laplacePolynomial_add
  map_smul' := laplacePolynomial_smul

def harmonicPolynomials (n d : ℕ) : Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  homogeneousSubmodule (Fin n) ℝ d ⊓ (laplaceLinear n).ker

instance harmonicPolynomials_finite (n d : ℕ) : FiniteDimensional ℝ (harmonicPolynomials n d) := by
  have : FiniteDimensional ℝ (homogeneousSubmodule (Fin n) ℝ d) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin n) ℝ d)
  exact Submodule.finiteDimensional_of_le (show harmonicPolynomials n d ≤
    homogeneousSubmodule (Fin n) ℝ d from inf_le_left)

/-- The genuine homogeneous harmonic subspaces of spherical L². -/
def harmonicSpace (n d : ℕ) [NeZero n] : Submodule ℝ (H n) :=
  (harmonicPolynomials n d).map (polynomialL2 n)

instance harmonicSpace_finite (n d : ℕ) [NeZero n] : FiniteDimensional ℝ (harmonicSpace n d) := by
  apply Module.Finite.of_fg
  exact ((Submodule.fg_iff_finiteDimensional (harmonicPolynomials n d)).mpr inferInstance).map _

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection

/-- The actual support function of a compact body, not a surrogate gauge. -/
def support {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  sSup ((fun x => ⟪u,x⟫) '' K)

lemma support_attained {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (u : Space n) : ∃ x ∈ K, support K u = ⟪u,x⟫ :=
  hK.exists_sSup_image_eq hKn (by fun_prop)

lemma inner_le_support {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {x : Space n} (hx : x ∈ K) (u : Space n) : ⟪u,x⟫ ≤ support K u := by
  exact le_csSup (hK.bddAbove_image (by fun_prop)) (mem_image_of_mem _ hx)

lemma support_le_iff {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {u : Space n} {a : ℝ} : support K u ≤ a ↔ ∀ x ∈ K, ⟪u,x⟫ ≤ a := by
  constructor
  · intro h x hx; exact (inner_le_support hK hx u).trans h
  · intro h
    obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]; exact h x hx

lemma support_continuous {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) :
    Continuous (support K) :=
  hK.continuous_sSup (by fun_prop)

lemma support_smul {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) (u : Space n) : support K (r • u) = r*support K u := by
  apply le_antisymm
  · apply (support_le_iff hK hKn).mpr
    intro x hx
    rw [real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (inner_le_support hK hx u) hr
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]
    simpa only [real_inner_smul_left] using inner_le_support hK hx (r • u)

lemma support_nonneg {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (h0 : 0 ∈ K)
    (u : Space n) : 0 ≤ support K u := by
  simpa only [inner_zero_right] using inner_le_support hK h0 u

lemma mem_iff_inner_le_support {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hKn : K.Nonempty) {x : Space n} :
    x ∈ K ↔ ∀ u : Space n, ⟪u,x⟫ ≤ support K u := by
  constructor
  · intro hx u; exact inner_le_support hK hx u
  · intro hx
    by_contra hn
    obtain ⟨f,a,hfa,hax⟩ := geometric_hahn_banach_closed_point hc hK.isClosed hn
    let u := (InnerProductSpace.toDual ℝ (Space n)).symm f
    have hu (y : Space n) : ⟪u,y⟫ = f y := by
      change (InnerProductSpace.toDual ℝ (Space n)) u y = f y
      rw [LinearIsometryEquiv.apply_symm_apply]
    obtain ⟨y,hy,he⟩ := support_attained hK hKn u
    have h := hx u
    rw [he,hu,hu] at h
    exact (not_lt_of_ge h) ((hfa y hy).trans hax)

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SphericalGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology MvPolynomial
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

def restrictContinuous {n : ℕ} (f : Space n → ℝ) (hf : Continuous f) : C(Sphere n, ℝ) :=
  ⟨fun u => f u, hf.comp continuous_subtype_val⟩

/-- A chosen true polynomial representative of a harmonic L² vector. -/
def harmonicRepresentative {n d : ℕ} [NeZero n] (v : harmonicSpace n d) : MvPolynomial (Fin n) ℝ :=
  Classical.choose v.property

/-- The mean-subtracted variance in the probability normalization. -/
def variance {n : ℕ} (f : Sphere n → ℝ) : ℝ := mean (fun u => f u ^ 2) - (mean f) ^ 2

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Pointwise Convolution
namespace PettyProjection.Spherical

lemma seminorm_continuous (n : ℕ) (g : Seminorm ℝ (Space n)) : Continuous g :=
  continuousOn_univ.mp (g.convexOn.continuousOn isOpen_univ)

def normSmooth {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    Space n → ℝ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (g : Space n → ℝ)

lemma normSmooth_contDiff {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    ContDiff ℝ 2 (normSmooth g φ) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed (seminorm_continuous n g).locallyIntegrable

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma sphere_ae_of_radial {n : ℕ} {P : Space n → Prop}
    (hP : ∀ᵐ x ∂(volume : Measure (Space n)), P x)
    (hr : ∀ (u : Sphere n) (r : ℝ), 0 < r → P (r • (u : Space n)) → P u) :
    ∀ᵐ (u : Sphere n) ∂sigma n, P (u : Space n) := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n) - 1)
  have hν : ν ≠ 0 := by
    intro h
    have he := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ (Space n) - 1)
      (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))
    change ν _ = _ at he
    rw [h] at he
    have hp : 0 < (1 : ℝ) ^ (Module.finrank ℝ (Space n) - 1 + 1) /
        ((Module.finrank ℝ (Space n) - 1 : ℕ) + 1) := by positivity
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) he.symm
  let : NeZero ν := ⟨hν⟩
  have hs : ∀ᵐ (x : ({0}ᶜ : Set (Space n))) ∂(volume : Measure (Space n)).comap
      (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n), P (x : Space n) :=
    (ae_restrict_iff_subtype (measurableSet_singleton (0 : Space n)).compl).mp
      (ae_restrict_of_ae hP)
  have hm := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  have hi := hm.symm (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv
  have hh := hi.quasiMeasurePreserving.ae hs
  have hh' : ∀ᵐ z ∂(surface n).prod ν, P (z.2.1 • (z.1 : Space n)) := by
    change ∀ᵐ z ∂(surface n).prod ν, P (((homeomorphUnitSphereProd (Space n)).symm z : ({0}ᶜ : Set (Space n))) : Space n) at hh
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hh
  apply Measure.ae_smul_measure (μ := surface n) _ ((surface n univ)⁻¹)
  filter_upwards [Measure.ae_ae_of_ae_prod hh'] with u hu
  obtain ⟨r, hr'⟩ := hu.exists
  exact hr u r r.property hr'

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.NormCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe)

/-- Intersection of the actual supporting constraints, with no evenness or
convexity condition on the constraint function. -/
def wulff {n : ℕ} (s : Sphere n → ℝ) : Set (Space n) :=
  {x | ∀ u : Sphere n, ⟪(u : Space n),x⟫ ≤ s u}

lemma wulff_support {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hKn : K.Nonempty) :
    wulff (fun u : Sphere n => support K u) = K := by
  ext x
  rw [mem_iff_inner_le_support hK hc hKn]
  constructor
  · intro h u
    by_cases hu : u = 0
    · subst u
      obtain ⟨y,hy,he⟩ := support_attained hK hKn 0
      simpa only [inner_zero_left] using he.ge
    · let v : Sphere n := ⟨‖u‖⁻¹ • u, by
        rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]⟩
      have he : u = ‖u‖ • (v : Space n) := by dsimp [v]; rw [smul_inv_smul₀ (norm_ne_zero_iff.mpr hu)]
      rw [he,real_inner_smul_left,support_smul hK hKn (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (h v) (norm_nonneg _)
  · intro h u; exact h u

/-- Compact coefficient set of the maximum formula. -/
def wulffCoefficients {n : ℕ} (s : Sphere n → ℝ) : Set (Space n) :=
  range (fun u : Sphere n => (s u)⁻¹ • (u : Space n))

def wulffMax {n : ℕ} (s : Sphere n → ℝ) (x : Space n) : ℝ :=
  support (wulffCoefficients s) x

lemma wulffCoefficients_compact {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsCompact (wulffCoefficients s) :=
  isCompact_range ((s.continuous.inv₀ (fun u => (hs u).ne')).smul continuous_subtype_val)

lemma wulffCoefficients_nonempty {n : ℕ} [NeZero n] (s : Sphere n → ℝ) :
    (wulffCoefficients s).Nonempty := by
  obtain ⟨u,hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : Space n))).mpr (by norm_num : (0:ℝ) ≤ 1)
  exact ⟨_,⟨⟨u,hu⟩,rfl⟩⟩

lemma wulffMax_attained {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) : ∃ u : Sphere n, wulffMax s x = ⟪x,(u : Space n)⟫ / s u := by
  obtain ⟨y,⟨u,rfl⟩,he⟩ := support_attained (wulffCoefficients_compact s hs)
    (wulffCoefficients_nonempty s) x
  exact ⟨u,by simpa only [wulffMax,real_inner_smul_right,div_eq_inv_mul] using he⟩

lemma le_wulffMax {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) (u : Sphere n) : ⟪x,(u : Space n)⟫ / s u ≤ wulffMax s x := by
  simpa only [wulffMax,real_inner_smul_right,div_eq_inv_mul] using
    inner_le_support (wulffCoefficients_compact s hs) (mem_range_self u) x

lemma wulffMax_pos {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    {x : Space n} (hx : x ≠ 0) : 0 < wulffMax s x := by
  let u : Sphere n := ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
  have he : ⟪x,(u : Space n)⟫ = ‖x‖ := by
    dsimp only [u]
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  apply lt_of_lt_of_le _ (le_wulffMax s hs x u)
  rw [he]
  exact div_pos (norm_pos_iff.mpr hx) (hs u)

lemma wulffMax_zero {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    wulffMax s (0 : Space n) = 0 := by
  obtain ⟨u,he⟩ := wulffMax_attained s hs 0
  simpa only [inner_zero_left,zero_div] using he

lemma mem_smul_wulff {n : ℕ} {s : Sphere n → ℝ} {a : ℝ} (ha : 0 < a) {x : Space n} :
    x ∈ a • wulff s ↔ ∀ u : Sphere n, ⟪x,(u : Space n)⟫ ≤ a*s u := by
  rw [mem_smul_set_iff_inv_smul_mem₀ ha.ne']
  change (∀ u : Sphere n, ⟪(u : Space n),a⁻¹ • x⟫ ≤ s u) ↔ _
  simp_rw [real_inner_smul_right,real_inner_comm (y := x),← div_eq_inv_mul,div_le_iff₀ ha]
  simp only [mul_comm]

lemma gauge_wulff_eq_max {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) : gauge (wulff s) x = wulffMax s x := by
  by_cases hx : x = 0
  · subst x; rw [gauge_zero,wulffMax_zero s hs]
  have hp := wulffMax_pos s hs hx
  have hmem : x ∈ wulffMax s x • wulff s := by
    apply (mem_smul_wulff hp).mpr
    intro u
    have h := (div_le_iff₀ (hs u)).mp (le_wulffMax s hs x u)
    simpa only [mul_comm] using h
  apply le_antisymm (gauge_le_of_mem hp.le hmem)
  rw [gauge_def]
  refine le_csInf (s := {r : ℝ | r ∈ Ioi 0 ∧ x ∈ r • wulff s})
    ⟨wulffMax s x,hp,hmem⟩ ?_
  rintro a ⟨ha,hax⟩
  obtain ⟨u,he⟩ := wulffMax_attained s hs x
  rw [he]
  exact (div_le_iff₀ (hs u)).mpr ((mem_smul_wulff ha).mp hax u)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Pointwise Convolution
namespace PettyProjection.Spherical

def shrinkingBump (n j : ℕ) : ContDiffBump (0 : Space n) where
  rIn := (1 / ((j : ℝ) + 1)) / 2
  rOut := 1 / ((j : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((j : ℝ) + 1) := by positivity
    linarith

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.ScalarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PettyProjection.Scalar

def exponent (n : ℕ) : ℕ := if n = 4 then 1 else 2

def coefficient (n : ℕ) : ℝ :=
  if n = 4 then 121 / 35 else
    ((n : ℝ)^2 + 5 * n + 7) / (((n : ℝ) + 1) * ((n : ℝ) + 3))

def beta (n : ℕ) : ℝ := if n = 4 then 1 / 2 else 2 / 3

def weight (n : ℕ) : ℝ :=
  if n = 4 then 3 / 14 else if n = 5 ∨ n = 6 then 1 / 3 else 1 / 2

def e (n : ℕ) (z : ℝ) : ℝ := ((z⁻¹)^n - 1) / n

def M (n : ℕ) (z : ℝ) : ℝ := z ^ exponent n - 1 + exponent n * e n z

def W (n : ℕ) (z : ℝ) : ℝ := z ^ exponent n - z ^ (exponent n - 1) + e n z

def G (n : ℕ) (z : ℝ) : ℝ := if 1 < z then beta n * M n z else 0

def D (n : ℕ) (z : ℝ) : ℝ := z ^ exponent n - 1 - G n z

/-- Closed form of the integral of M'(a)^2 over [1,z], or zero below 1. -/
def I (n : ℕ) (z : ℝ) : ℝ :=
  if 1 < z then
    (exponent n : ℝ)^2 *
      ((z ^ (2 * exponent n - 1) - 1) / (2 * exponent n - 1 : ℕ) -
        2 * (1 - (z⁻¹) ^ (n + 1 - exponent n)) / (n + 1 - exponent n : ℕ) +
        (1 - (z⁻¹) ^ (2 * n + 1)) / (2 * n + 1 : ℕ))
  else 0

def L (n : ℕ) (z : ℝ) : ℝ :=
  coefficient n *
    ((((n : ℝ) - 1) * beta n ^ 2 * z * I n z - 2 * n * G n z ^ 2) /
        (weight n * (2 * n + 8)) + D n z ^ 2 / (1 - weight n))

def P4 (z : ℝ) : ℝ := 462 * z^10 - 983 * z^9 + 93 * z^8 + 3399 * z^5 - 3378 * z^4 + 407

def U4 (x : ℝ) : ℝ := 17052 * x^4 - 6711 * x^2 - 1446 * x + 1728

def P5 (z : ℝ) : ℝ := 151525 * z^14 - 273570 * z^12 - 680800 * z^11 + 938157 * z^10 + 225720 * z^7 - 462264 * z^5 + 101232

def U5 (x : ℝ) : ℝ := 86314305 * x^4 - 5802775 * x^2 - 1505900 * x + 623700

def P6 (z : ℝ) : ℝ := 48399 * z^16 - 75894 * z^14 - 218004 * z^13 + 285961 * z^12 + 56940 * z^8 - 127478 * z^6 + 30076

def U6 (x : ℝ) : ℝ := 51269452 * x^4 - 132249 * x^2 + 452790

def P7 (z : ℝ) : ℝ := 3185 * z^18 + 77910 * z^16 - 185472 * z^15 + 101385 * z^14 + 40040 * z^9 - 43080 * z^7 + 6032

def P8 (z : ℝ) : ℝ := 5032 * z^20 + 106896 * z^18 - 245128 * z^17 + 131937 * z^16 + 45288 * z^10 - 52683 * z^8 + 8658

def P9 (z : ℝ) : ℝ := 17955 * z^22 + 344826 * z^20 - 771336 * z^19 + 409763 * z^18 + 124488 * z^11 - 153472 * z^9 + 27776

open Finset

/-- Taylor remainder of the n-th power after its quadratic term. -/
def tail (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (n+1), if 3 ≤ j then (n.choose j : ℝ)*x^j else 0

def largeC (r : ℝ) := (r^2+5*r+7)/((r+1)*(r+3))
def H (r : ℝ) := 18*(r+4)/largeC r

def A4 (r : ℝ) := (2*r-8)/3
def A2 (r : ℝ) := H r-12*r-32-64/r
def A1 (r : ℝ) := -H r+16*(r-1)/3+32-16*(r-1)/(2*r+1)
def A0 (r : ℝ) := -H r/r+6*r+40+64/r-128/r^2
def B2 (r : ℝ) := 16+64/r
def B0 (r : ℝ) := H r/r-48-64/r+256/r^2
def T0 (r : ℝ) := 16*(r-1)/(2*r+1)-128/r^2

def q0 (r : ℝ) := A4 r+A2 r+A1 r+A0 r
def q1 (r : ℝ) := 4*A4 r+2*A2 r+A1 r
def q2 (r : ℝ) := 6*A4 r+A2 r
def q3 (r : ℝ) := 4*A4 r
def q4 (r : ℝ) := A4 r
def r0 (r : ℝ) := B2 r+B0 r
def r1 (r : ℝ) := 2*B2 r
def r2 (r : ℝ) := B2 r

def V0 (r : ℝ) := 34*r^5-95*r^4-1666*r^3-5701*r^2-8052*r-2688
def V1 (r : ℝ) := 2*r^5+9*r^4-162*r^3-845*r^2-1220*r-448
def V2 (r : ℝ) := 5*r^3+8*r^2-41*r-56
def R0 (r : ℝ) := 7*r^4+8*r^3-187*r^2-748*r-896

end PettyProjection.Scalar
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.ScalarCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology
namespace PettyProjection.Scalar

lemma hasDerivAt_inverse_pow (n : ℕ) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun x : ℝ => (x⁻¹) ^ n) (-(n : ℝ) * (z⁻¹) ^ (n + 1)) z := by
  have h := hasDerivAt_zpow (-(n : ℤ)) z (Or.inl hz)
  have he : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
  simpa only [he, zpow_neg, zpow_natCast, inv_pow, Int.cast_neg, Int.cast_natCast] using h

lemma hasDerivAt_e {n : ℕ} (hn : n ≠ 0) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (e n) (-(z⁻¹) ^ (n + 1)) z := by
  have h := ((hasDerivAt_inverse_pow n hz).sub_const 1).div_const (n : ℝ)
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  convert! h using 1
  field_simp

lemma hasDerivAt_M {n : ℕ} (hn : n ≠ 0) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (M n) ((exponent n : ℝ) * (z ^ (exponent n - 1) - (z⁻¹) ^ (n + 1))) z := by
  have h := ((hasDerivAt_pow (exponent n) z).sub_const 1).add
    ((hasDerivAt_e hn hz).const_mul (exponent n : ℝ))
  convert! h using 1
  ring

lemma M_one (n : ℕ) : M n 1 = 0 := by simp [M, e]

lemma paste_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ∀ x, 1 ≤ x → HasDerivAt f (f' x) x) (hf1 : f 1 = 0) (hf'1 : f' 1 = 0)
    (x : ℝ) :
    HasDerivAt (fun z => if 1 < z then f z else 0) (if 1 < x then f' x else 0) x := by
  rcases lt_trichotomy x 1 with hx | rfl | hx
  · have he : (fun z => if 1 < z then f z else 0) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds hx] with z hz
      simp only [ite_eq_right (not_lt.mpr hz.le)]
    simpa only [ite_eq_right (not_lt.mpr hx.le)] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
  · have hl : HasDerivWithinAt (fun z => if 1 < z then f z else 0) 0 (Iic 1) 1 := by
      apply (hasDerivAt_const 1 (0 : ℝ)).hasDerivWithinAt.congr
      · intro z hz
        simp only [ite_eq_right (not_lt.mpr (show z ≤ 1 from hz))]
      · simp
    have hr : HasDerivWithinAt (fun z => if 1 < z then f z else 0) 0 (Ici 1) 1 := by
      have h := (hf 1 le_rfl).hasDerivWithinAt (s := Ici 1)
      rw [hf'1] at h
      apply h.congr
      · intro z hz
        rcases lt_or_eq_of_le (show 1 ≤ z from hz) with hz | rfl
        · simp only [ite_eq_left hz]
        · simp [hf1]
      · simp [hf1]
    have h := hl.union hr
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at h
    simpa using h
  · have he : (fun z => if 1 < z then f z else 0) =ᶠ[𝓝 x] f := by
      filter_upwards [eventually_gt_nhds hx] with z hz
      simp only [ite_eq_left hz]
    simpa only [ite_eq_left hx] using (hf x hx.le).congr_of_eventuallyEq he

lemma paste_contDiff_one {f f' : ℝ → ℝ}
    (hf : ∀ x, 1 ≤ x → HasDerivAt f (f' x) x) (hf1 : f 1 = 0) (hf'1 : f' 1 = 0)
    (hcont : ContinuousOn f' (Ici 1)) :
    ContDiff ℝ 1 (fun z => if 1 < z then f z else 0) := by
  have hd := paste_hasDerivAt hf hf1 hf'1
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun x => (hd x).differentiableAt
  · have he : deriv (fun z => if 1 < z then f z else 0) =
        (fun z => if z ≤ 1 then 0 else f' z) := by
      funext z
      rw [(hd z).deriv]
      simp only [← not_le, ite_not]
    rw [he]
    exact continuous_if_le continuous_id continuous_const continuousOn_const hcont
      (fun x hx => by change x = 1 at hx; subst x; exact hf'1.symm)

end PettyProjection.Scalar
end

noncomputable section
open Set Filter Topology
namespace PettyProjection.Scalar

def Mprime (n : ℕ) (z : ℝ) : ℝ :=
  (exponent n : ℝ) * (z ^ (exponent n - 1) - (z⁻¹) ^ (n + 1))

def Iformula (n : ℕ) (z : ℝ) : ℝ :=
  (exponent n : ℝ)^2 *
    ((z ^ (2 * exponent n - 1) - 1) / (2 * exponent n - 1 : ℕ) -
      2 * (1 - (z⁻¹) ^ (n + 1 - exponent n)) / (n + 1 - exponent n : ℕ) +
      (1 - (z⁻¹) ^ (2 * n + 1)) / (2 * n + 1 : ℕ))

lemma Mprime_one (n : ℕ) : Mprime n 1 = 0 := by simp [Mprime]

lemma continuousOn_Mprime (n : ℕ) : ContinuousOn (Mprime n) (Ici 1) := by
  apply continuousOn_const.mul
  apply (continuousOn_id.pow _).sub
  exact (continuousOn_id.inv₀ (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx))).pow _

lemma contDiff_G {n : ℕ} (hn : 4 ≤ n) : ContDiff ℝ 1 (G n) := by
  apply paste_contDiff_one (f' := fun z => beta n * Mprime n z)
  · intro x hx
    exact (hasDerivAt_M (by omega) (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))).const_mul _
  · simp [M_one]
  · simp [Mprime_one]
  · exact continuousOn_const.mul (continuousOn_Mprime n)

end PettyProjection.Scalar
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.NormEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

lemma continuous_D {n : ℕ} (hn : 4 ≤ n) : Continuous (D n) :=
  ((continuous_id.pow _).sub continuous_const).sub (contDiff_G hn).continuous

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.CosineCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology Function
namespace PettyProjection.Spherical

/-- Positive part to a natural power; the endpoint is fixed to zero. -/
def posPower (r : ℕ) (x : ℝ) : ℝ := if 0 < x then x^r else 0

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

/-- Genuine tangential gradient on the unit sphere, expressed ambiently. -/
def sphereGradient {n : ℕ} (f : Space n → ℝ) (x : Space n) : Space n :=
  ∇ f x - (fderiv ℝ f x x) • x

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.WulffVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uU

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma kappa_pos (n : ℕ) : 0 < kappa n := by
  unfold kappa unitBall
  exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 (by norm_num)).ne'
    (measure_closedBall_lt_top.ne)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma measurable_gradient {n : ℕ} (f : Space n → ℝ) : Measurable (gradient f) := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma support_smul_set {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (u : Space n) : support (t • K) u = t*support K u := by
  have hn : (t • K).Nonempty := by obtain ⟨x,hx⟩ := hKn; exact ⟨t • x,smul_mem_smul_set hx⟩
  apply le_antisymm
  · apply (support_le_iff (hK.smul t) hn).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (inner_le_support hK hx u) ht
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]
    simpa only [real_inner_smul_right] using
      inner_le_support (hK.smul t) (smul_mem_smul_set hx) u

lemma support_pos_of_nhds {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (h0 : K ∈ 𝓝 (0 : Space n)) (u : Sphere n) : 0 < support K u := by
  obtain ⟨r,hr,hrK⟩ := Metric.mem_nhds_iff.mp h0
  have hx : (r/2) • (u : Space n) ∈ K := by
    apply hrK
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),norm_coe,mul_one]
    linarith
  have h := inner_le_support hK hx (u : Space n)
  rw [real_inner_smul_right,real_inner_self_eq_norm_sq,norm_coe,one_pow,mul_one] at h
  linarith

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.ShadowSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma perpendicular_inner {n : ℕ} (u : Space n) (z : perpendicular u) : ⟪u,(z : Space n)⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.property

/-- Orthogonal coordinates with the last coordinate in a specified unit direction. -/
def shadowCoordLinear {n : ℕ} (u : Sphere n) :
    WithLp 2 (perpendicular (u : Space n) × ℝ) →ₗ[ℝ] Space n where
  toFun z := (WithLp.ofLp z).1+(WithLp.ofLp z).2 • (u : Space n)
  map_add' z w := by
    simp only [WithLp.ofLp_add,Prod.fst_add,Prod.snd_add,Submodule.coe_add,add_smul]
    abel
  map_smul' a z := by
    simp only [WithLp.ofLp_smul,Prod.smul_fst,Prod.smul_snd,Submodule.coe_smul_of_tower,
      smul_eq_mul,smul_add,smul_smul,RingHom.id_apply]

lemma shadowCoordLinear_inner {n : ℕ} (u : Sphere n)
    (z w : WithLp 2 (perpendicular (u : Space n) × ℝ)) :
    ⟪shadowCoordLinear u z,shadowCoordLinear u w⟫ = ⟪z,w⟫ := by
  change ⟪((WithLp.ofLp z).1 : Space n)+(WithLp.ofLp z).2 • (u : Space n),
    ((WithLp.ofLp w).1 : Space n)+(WithLp.ofLp w).2 • (u : Space n)⟫ = _
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq,norm_coe,one_pow,mul_one,
    perpendicular_inner,Submodule.mem_orthogonal_singleton_iff_inner_left.mp (WithLp.ofLp z).1.property]
  simp only [mul_zero,add_zero,zero_add,WithLp.prod_inner_apply,Submodule.coe_inner,Real.inner_apply]
  ring

lemma shadowCoordLinear_surjective {n : ℕ} (u : Sphere n) : Surjective (shadowCoordLinear u) := by
  intro x
  have hz : x-⟪(u : Space n),x⟫ • (u : Space n) ∈ perpendicular (u : Space n) := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,norm_coe,one_pow,mul_one,sub_self]
  refine ⟨WithLp.toLp 2 (⟨_,hz⟩,⟪(u : Space n),x⟫),?_⟩
  change x-_+_ = x
  exact sub_add_cancel _ _

def shadowCoords {n : ℕ} (u : Sphere n) :
    WithLp 2 (perpendicular (u : Space n) × ℝ) ≃ₗᵢ[ℝ] Space n :=
  LinearIsometryEquiv.ofSurjective
    (LinearMap.isometryOfInner (shadowCoordLinear u) (shadowCoordLinear_inner u))
    (shadowCoordLinear_surjective u)

/-- The coordinate change preserves the actual standard Euclidean measures. -/
def shadowMeasurableEquiv {n : ℕ} (u : Sphere n) :
    (perpendicular (u : Space n) × ℝ) ≃ᵐ Space n :=
  (MeasurableEquiv.toLp 2 _).trans (shadowCoords u).toMeasurableEquiv

lemma shadowMeasurableEquiv_measurePreserving {n : ℕ} (u : Sphere n) :
    MeasurePreserving (shadowMeasurableEquiv u) :=
  (WithLp.volume_preserving_toLp _ _).trans (shadowCoords u).measurePreserving

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

def unitSegment {n : ℕ} (y : Space n) : Set (Space n) :=
  (fun a : ℝ => a • y) '' Icc (-1) 1

def shadowContinuousEquiv {n : ℕ} (u : Sphere n) :
    (perpendicular (u : Space n) × ℝ) ≃L[ℝ] Space n :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (perpendicular (u : Space n)) ℝ).symm.trans
    (shadowCoords u).toContinuousLinearEquiv

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SliceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

def horizontalSlice (K : Set (E × ℝ)) (s : ℝ) : Set E := (fun y => (y,s)) ⁻¹' K

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

def sliceDensity (K : Set (E × ℝ)) (s : ℝ) : ℝ := volume.real (horizontalSlice K s)

end
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The dimension-induction predicate, used only with a proved lower-dimensional
case. It is not an extra hypothesis on the projection-volume main theorem. -/
def BrunnMinkowskiRoot (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] (m : ℕ) : Prop :=
  ∀ K M : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
    IsCompact M → Convex ℝ M → (interior M).Nonempty →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      a*(volume.real K)^((m:ℝ)⁻¹)+b*(volume.real M)^((m:ℝ)⁻¹) ≤
        (volume.real (a • K+b • M))^((m:ℝ)⁻¹)

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma volumeReal_pos_of_body {K : Set E} (hK : IsCompact K) (hi : (interior K).Nonempty) :
    0 < volume.real K :=
  ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (isOpen_interior.measure_pos volume hi)
    (measure_mono interior_subset))) hK.measure_ne_top

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

/-- Standard coordinate splitting, with explicit measure evidence. -/
def finSplitLinear (n : ℕ) : (Fin (n+1) → ℝ) ≃ₗ[ℝ] ((Fin n → ℝ) × ℝ) where
  toEquiv := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).toEquiv.trans
    (Equiv.prodComm _ _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finSplit (n : ℕ) : (Fin (n+1) → ℝ) ≃L[ℝ] ((Fin n → ℝ) × ℝ) :=
  (finSplitLinear n).toContinuousLinearEquiv

def finOneLinear : (Fin 1 → ℝ) ≃ₗ[ℝ] ℝ := LinearEquiv.funUnique (Fin 1) ℝ ℝ

def finOne : (Fin 1 → ℝ) ≃L[ℝ] ℝ := finOneLinear.toContinuousLinearEquiv

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.Homothety
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Pointwise RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe)

/-- The unnormalized Euclidean first moment. It is the barycenter for unit
volume bodies, the only place where it is used below. -/
def firstMoment {n : ℕ} (K : Set (Space n)) : Space n := ∫ x in K, x

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

def volumeRoot {n : ℕ} (K : Set (Space n)) : ℝ := (volume.real K)^((n:ℝ)⁻¹)

lemma volumeRoot_pos {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) : 0 < volumeRoot K :=
  Real.rpow_pos_of_pos (volumeReal_pos_of_body hK hi) _

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SupportMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma gauge_pos_sphere {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (u : Sphere n) : 0 < gauge K (u : Space n) := by
  let s : C(Sphere n,ℝ) := ⟨fun u => support K u,(support_continuous hK).comp continuous_subtype_val⟩
  have hs : ∀ u,0 < s u := support_pos_of_nhds hK h0
  have hw : wulff s = K := wulff_support hK hc ⟨0,mem_of_mem_nhds h0⟩
  rw [← hw,gauge_wulff_eq_max s hs]
  exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)

def gaugeDensity {n : ℕ} (K : Set (Space n)) (u : Sphere n) : ENNReal :=
  ENNReal.ofReal ((gauge K (u : Space n))⁻¹^n)

def gaugeProjectionMeasure {n : ℕ} (K : Set (Space n)) : Measure (Space n) :=
  Measure.map (fun u : Sphere n => ∇ (gauge K) (u : Space n))
    ((sigma n).withDensity (gaugeDensity K))

lemma gaugeMeasure_finite {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    IsFiniteMeasure (gaugeProjectionMeasure K) := by
  have hp := gauge_pos_sphere hK hc h0
  have hcont : Continuous (fun u : Sphere n => (gauge K (u : Space n))⁻¹^n) :=
    (((continuous_gauge hc h0).comp continuous_subtype_val).inv₀ (fun u => (hp u).ne')).pow n
  have hi := hcont.integrable_of_hasCompactSupport (μ := sigma n) (HasCompactSupport.of_compactSpace _)
  have hf : ∫⁻ u, gaugeDensity K u ∂sigma n ≠ ⊤ := by
    unfold gaugeDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun u => (pow_nonneg (inv_nonneg.mpr (hp u).le) n)))]
    exact ENNReal.ofReal_ne_top
  have := isFiniteMeasure_withDensity hf
  exact Measure.isFiniteMeasure_map _ _

lemma gaugeMeasure_bounded {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂gaugeProjectionMeasure K, ‖x‖ ≤ B := by
  obtain ⟨C,hC⟩ := hc.lipschitz_gauge h0
  refine ⟨C,C.coe_nonneg,?_⟩
  have hm : Measurable (fun u : Sphere n => ∇ (gauge K) (u : Space n)) :=
    (measurable_gradient _).comp measurable_subtype_coe
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_le measurable_norm measurable_const)).mpr
  apply Eventually.of_forall
  intro u
  have he : ‖∇ (gauge K) (u : Space n)‖=‖fderiv ℝ (gauge K) (u : Space n)‖ :=
    (InnerProductSpace.toDual ℝ (Space n)).symm.norm_map _
  rw [he]
  exact norm_fderiv_le_of_lipschitz ℝ hC

lemma boundedMeasure_integrable_continuous {n : ℕ} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hb : ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂μ, ‖x‖ ≤ B) {f : Space n → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  obtain ⟨B,_,hB⟩ := hb
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Space n) B).exists_bound_of_continuousOn hf.continuousOn
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [hB] with x hx
  exact hC x (by simpa only [mem_closedBall,dist_zero_right] using hx)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

def supportFunctional {n : ℕ} (μ : Measure (Space n)) (K : Set (Space n)) : ℝ :=
  ∫ x,support K x ∂μ

def normalizedVolume {n : ℕ} (K : Set (Space n)) : ℝ :=
  volumeRoot K/(kappa n)^((n:ℝ)⁻¹)

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SignCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology
namespace PettyProjection.Spherical

def softAbs (ε t : ℝ) : ℝ := Real.sqrt (t^2+ε)
def softSign (ε t : ℝ) : ℝ := t/softAbs ε t
def softSlope (ε t : ℝ) : ℝ := ε/(softAbs ε t)^3

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

def signedPair {n : ℕ} (F G : Sphere n → Space n) : ℝ :=
  ∫ z : Sphere n × Sphere n, Real.sign ⟪(z.1 : Space n),(z.2 : Space n)⟫ *
    ⟪F z.1,G z.2⟫ ∂(sigma n).prod (sigma n)

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.CosineSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

/-- Positive-hemisphere power kernel, including the constant zeroth power. -/
def higherKernel {n : ℕ} (r : ℕ) (u : Sphere n) (f : Sphere n → ℝ) : ℝ :=
  mean (fun x => (max ⟪(u : Space n),(x : Space n)⟫ 0)^r*f x)

end PettyProjection.Spherical
end

noncomputable section
open Filter Topology
namespace PettyProjection.Spherical

/-- Normalized multiplier of the positive-power kernel on degree `2*j`. -/
def higherFactor (n j : ℕ) (s : ℝ) : ℝ :=
  ∏ a ∈ Finset.range j, (s-2*a)/(s+n+2*a)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

def pole (n : ℕ) [NeZero n] : Sphere n :=
  ⟨EuclideanSpace.single (0 : Fin n) 1, by simp⟩

/-- The true normalized cosine kernel's constant, not an assumed multiplier. -/
def cosineConstant (n : ℕ) [NeZero n] : ℝ :=
  2*higherKernel 1 (pole n) (fun _ => 1)

/-- The actual cosine integral, with its constant fixed geometrically. -/
def cosine {n : ℕ} [NeZero n] (f : Sphere n → ℝ) (u : Sphere n) : ℝ :=
  mean (fun x : Sphere n => |⟪(u : Space n),(x : Space n)⟫| *f x)/cosineConstant n

lemma cosine_continuous {n : ℕ} [NeZero n] {f : Sphere n → ℝ} (hf : Continuous f) :
    Continuous (cosine f) := by
  apply Continuous.div_const
  have h := continuous_parametric_integral_of_continuous (μ := sigma n)
    (f := fun u x : Sphere n => |⟪(u : Space n),(x : Space n)⟫| *f x)
    (by fun_prop) isCompact_univ
  simpa only [Measure.restrict_univ, mean] using h

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

def cosineMap {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) : C(Sphere n, ℝ) :=
  ⟨cosine f, cosine_continuous f.continuous⟩

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SignSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

def signFactor (n j : ℕ) (a : ℝ) : ℝ :=
  higherFactor n j 1*(1+a*eigenvalue n (2*j))

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma casimir_continuous {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (casimir f) := by
  unfold casimir
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_rotDeriv _ (contDiff_rotDeriv _ hf))

def casimirMap {n : ℕ} (f : Space n → ℝ) (hf : ContDiff ℝ 2 f) : C(Sphere n, ℝ) :=
  restrictContinuous (casimir f) (casimir_continuous hf)

def signOperator {n : ℕ} [NeZero n] (a : ℝ) (f : Space n → ℝ) (hf : ContDiff ℝ 2 f) :
    C(Sphere n, ℝ) := cosineMap (restrictContinuous f hf.continuous - a • casimirMap f hf)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

def radialField {n : ℕ} (f : Space n → ℝ) (u : Sphere n) : Space n := f u • (u : Space n)
def tangentField {n : ℕ} (f : Space n → ℝ) (u : Sphere n) : Space n := sphereGradient f u

def signField {n : ℕ} (k : ℝ) (f : Space n → ℝ) (u : Sphere n) : Space n :=
  radialField f u + k⁻¹ • tangentField f u

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.NormRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

def gaugeMoment {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ) : ℝ :=
  mean (fun u : Sphere n => g u^k)

def gaugeTail {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n)) (k : ℕ) : ℝ :=
  ‖Q n (toH n (restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k)))‖

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

def gaugeField {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ) (u : Sphere n) : Space n :=
  g u^(k-1) • ∇ (g : Space n → ℝ) u

def absolutePair {n : ℕ} (F G : Sphere n → Space n) : ℝ :=
  ∫ z : Sphere n × Sphere n, |⟪F z.1,G z.2⟫| ∂(sigma n).prod (sigma n)

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SeminormBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uι

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma seminorm_le_max_norm {n : ℕ} (g : Seminorm ℝ (Space n)) {R : ℝ}
    (hmax : ∀ u : Sphere n, g u ≤ R) (x : Space n) : g x ≤ R*‖x‖ := by
  by_cases hx : x=0
  · simp [hx]
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let u : Sphere n := ⟨‖x‖⁻¹ • x, by simp [norm_smul,hx0]⟩
  have hu := hmax u
  have hgu : g x=‖x‖*g u := by
    change g x=‖x‖*g (‖x‖⁻¹ • x)
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    field_simp
  rw [hgu]
  nlinarith [norm_nonneg x]

/-- Exact coordinate minorant used for logarithmic coercivity and continuous
extension to singular matrix ranks. -/
lemma seminorm_coordinate_minorant {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n))
    (hg : g ≠ 0) : ∃ (R : ℝ) (e : Sphere n), 0 < R ∧
      (∀ u : Sphere n, g u ≤ R) ∧
      (∀ x : Space n, R*|⟪x,(e:Space n)⟫| ≤ g x) := by
  have hne : (sphere (0 : Space n) 1).Nonempty := by
    obtain ⟨x,hx⟩ := exists_norm_eq (Space n) (by norm_num : (0:ℝ)≤1)
    exact ⟨x,by simpa [mem_sphere,dist_zero_right]⟩
  obtain ⟨v,hv,hm⟩ := (isCompact_sphere (0 : Space n) 1).exists_isMaxOn hne
    (seminorm_continuous n g).continuousOn
  have hv1 : ‖v‖=1 := by simpa [mem_sphere,dist_zero_right] using hv
  let R := g v
  have hR : 0≤R := apply_nonneg g v
  have hmax (u : Sphere n) : g u ≤ R := hm u.property
  have hbound := seminorm_le_max_norm g hmax
  have hRp : 0<R := by
    by_contra h
    have hz : R=0 := le_antisymm (le_of_not_gt h) hR
    apply hg
    ext x
    exact le_antisymm (by simpa [hz] using hbound x) (apply_nonneg g x)
  let S := Submodule.span ℝ {v}
  let f : Module.Dual ℝ S := R • ((innerSL ℝ v).toLinearMap.comp S.subtype)
  have hf (y : S) : |f y| ≤ g (y:Space n) := by
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp y.property
    change |R*⟪v,(y:Space n)⟫| ≤ g (y:Space n)
    rw [← ha,inner_smul_right,real_inner_self_eq_norm_sq,hv1,map_smul_eq_mul]
    simp only [one_pow,mul_one,Real.norm_eq_abs,abs_mul,abs_of_nonneg hR]
    dsimp only [R]
    rw [mul_comm]
  obtain ⟨φ,hφ,hφbound⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm_real
    S f (seminorm_continuous n g) (fun y => (le_abs_self _).trans (hf y))
  have hφv : φ v=R := by
    have h := hφ ⟨v,Submodule.mem_span_singleton_self v⟩
    simpa [f,real_inner_self_eq_norm_sq,hv1] using h
  have hφnorm : ‖φ‖=R := by
    apply le_antisymm
    · exact φ.opNorm_le_bound hR (fun x => by simpa only [Real.norm_eq_abs] using (hφbound x).trans (hbound x))
    · have h := φ.le_opNorm v
      rw [hφv,hv1,Real.norm_of_nonneg hR,mul_one] at h
      exact h
  let w := (InnerProductSpace.toDual ℝ (Space n)).symm φ
  have hw : ‖w‖=R := by simpa only [w,LinearIsometryEquiv.norm_map] using hφnorm
  let e : Sphere n := ⟨R⁻¹ • w,by
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR),hw]
    exact inv_mul_cancel₀ hRp.ne'⟩
  refine ⟨R,e,hRp,hmax,fun x => ?_⟩
  change R*|⟪x,R⁻¹ • w⟫| ≤ g x
  rw [inner_smul_right,abs_mul,abs_of_pos (inv_pos.mpr hRp),← mul_assoc,
    mul_inv_cancel₀ hRp.ne',one_mul,real_inner_comm]
  simpa only [w,InnerProductSpace.toDual_symm_apply] using hφbound x

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma intervalIntegrable_abs_rpow {p a b : ℝ} (hp : -1<p) :
    IntervalIntegrable (fun t : ℝ => |t|^p) volume a b := by
  apply intervalIntegrable_of_even (fun t => by rw [abs_neg])
  intro x hx
  apply (intervalIntegral.intervalIntegrable_rpow' hp).congr
  intro t ht
  rw [uIoc_of_le hx.le] at ht
  dsimp only
  rw [abs_of_nonneg ht.1.le]

lemma inner_rpow_integrable_ball {n : ℕ} (e : Sphere n) {p : ℝ} (hp : -1<p) :
    IntegrableOn (fun x : Space n => |⟪(e:Space n),x⟫|^p) (ball 0 1) := by
  let B := ball (0 : perpendicular (e:Space n)) 1
  let : IsFiniteMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isBounded_ball : Bornology.IsBounded B).measure_lt_top⟩
  have hI : Integrable (fun z : perpendicular (e:Space n) × ℝ => |z.2|^p)
      ((volume.restrict B).prod (volume.restrict (Icc (-1:ℝ) 1))) := by
    have h := (integrableOn_Icc_iff_integrableOn_Ioc (f := fun t : ℝ => |t|^p)).mpr
      (intervalIntegrable_abs_rpow (a := -1) (b := 1) hp).1
    exact h.comp_snd _
  rw [Measure.prod_restrict,← Measure.volume_eq_prod] at hI
  have hsub : (shadowMeasurableEquiv e) ⁻¹' ball (0:Space n) 1 ⊆ B ×ˢ Icc (-1:ℝ) 1 := by
    rintro ⟨z,t⟩ h
    have hnorm : ‖shadowCoords e (WithLp.toLp 2 (z,t))‖<1 := by
      simpa [shadowMeasurableEquiv] using h
    rw [(shadowCoords e).norm_map] at hnorm
    have hz := WithLp.norm_fst_le (p := (2:ℝ≥0∞)) _ (WithLp.toLp 2 (z,t))
    have ht := WithLp.norm_snd_le (p := (2:ℝ≥0∞)) _ (WithLp.toLp 2 (z,t))
    refine ⟨?_,?_⟩
    · simpa only [B,mem_ball,dist_zero_right,WithLp.toLp_fst] using hz.trans_lt hnorm
    · have habs : |t|<1 := by exact ht.trans_lt hnorm
      exact ⟨(neg_lt_of_abs_lt habs).le,(lt_of_abs_lt habs).le⟩
  change IntegrableOn (fun z : perpendicular (e:Space n) × ℝ => |z.2|^p) (B ×ˢ Icc (-1:ℝ) 1) at hI
  have hI' := hI.mono_set hsub
  have heq : (fun z : perpendicular (e:Space n) × ℝ => |⟪(e:Space n),shadowMeasurableEquiv e z⟫|^p)=
      (fun z => |z.2|^p) := by
    funext z
    change |⟪(e:Space n),(z.1:Space n)+z.2 • (e:Space n)⟫|^p=_
    rw [inner_add_right,perpendicular_inner,inner_smul_right,real_inner_self_eq_norm_sq,norm_coe]
    simp
  exact ((shadowMeasurableEquiv_measurePreserving e).integrableOn_comp_preimage
    (shadowMeasurableEquiv e).measurableEmbedding).mp (by simpa only [comp_def,heq] using hI')

lemma sphere_integrable_of_homogeneous {n : ℕ} [NeZero n] {f : Space n → ℝ} {p : ℝ}
    (hf : IntegrableOn f (ball 0 1))
    (hh : ∀ (r : ℝ),0<r → ∀ x,f (r • x)=r^p*f x) :
    Integrable (fun u : Sphere n => f u) (sigma n) := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n)-1)
  let I : Set (Ioi (0:ℝ)) := Iio ⟨1,by norm_num⟩
  have hνI : ν I ≠ 0 := by
    have h := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ (Space n)-1)
      (⟨1,by norm_num⟩ : Ioi (0:ℝ))
    change ν I=_ at h
    rw [h]
    apply (ENNReal.ofReal_pos.mpr _).ne'
    positivity
  let F : Space n → ℝ := (ball (0:Space n) 1).indicator f
  have hF : Integrable F := hf.integrable_indicator measurableSet_ball
  have hs := (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0:Space n)).compl).mp
    (hF.integrableOn (s := ({0}ᶜ : Set (Space n))))
  have hm := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  have hprod := (hm.symm (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv).integrable_comp_emb
    (homeomorphUnitSphereProd (Space n)).symm.measurableEmbedding |>.mpr hs
  have hAE : ∀ᵐ r ∂ν, Integrable (fun u : Sphere n => F (r.1 • (u:Space n))) (surface n) := by
    have h := hprod.prod_left_ae
    change ∀ᵐ r ∂ν, Integrable (fun u => F ↑((homeomorphUnitSphereProd (Space n)).symm (u,r))) (surface n) at h
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using h
  obtain ⟨r,hr,hir⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hνI (ae_restrict_of_ae hAE)
  have hr1 : (r:ℝ)<1 := hr
  have hp : r.1^p ≠ 0 := (Real.rpow_pos_of_pos r.property p).ne'
  have hfun : (fun u : Sphere n => F (r.1 • (u:Space n)))=(fun u : Sphere n => r.1^p*f u) := by
    funext u
    have hu : r.1 • (u:Space n) ∈ ball (0:Space n) 1 := by
      simpa only [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg r.property.le,norm_coe,mul_one] using hr1
    dsimp only [F]
    rw [indicator_of_mem hu,hh r r.property]
  rw [hfun] at hir
  have hi := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hp) (fun u : Sphere n => f u)).mp hir
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr (Measure.measure_univ_ne_zero.mpr (surface_ne_zero n)))

lemma inner_rpow_integrable_sphere {n : ℕ} [NeZero n] (e : Sphere n) {p : ℝ} (hp : -1<p) :
    Integrable (fun u : Sphere n => |⟪(e:Space n),(u:Space n)⟫|^p) (sigma n) := by
  apply sphere_integrable_of_homogeneous (p := p) (inner_rpow_integrable_ball e hp)
  intro r hr x
  rw [inner_smul_right,abs_mul,abs_of_pos hr,Real.mul_rpow hr.le (abs_nonneg _)]

lemma log_sq_le_negative_rpow {t : ℝ} (ht : 0<t) (h1 : t≤1) :
    (Real.log t)^2 ≤ 16*t^(-(1/2:ℝ)) := by
  have hl : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos ht.le h1)
  have h := Real.log_le_rpow_div (inv_nonneg.mpr ht.le) (by norm_num : (0:ℝ)<1/4)
  rw [Real.log_inv] at h
  have hsq := sq_le_sq₀ hl (by positivity : 0 ≤ (t⁻¹)^(1/4:ℝ)/(1/4:ℝ)) |>.mpr h
  have hp : ((t⁻¹)^(1/4:ℝ))^2=t^(-(1/2:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (inv_nonneg.mpr ht.le),Real.inv_rpow ht.le]
    norm_num
    rw [Real.rpow_neg ht.le]
  rw [div_pow,neg_sq, hp] at hsq
  norm_num at hsq
  nlinarith

lemma log_inner_sq_integrable {n : ℕ} [NeZero n] (e : Sphere n) :
    Integrable (fun u : Sphere n => (Real.log |⟪(e:Space n),(u:Space n)⟫|)^2) (sigma n) := by
  apply ((inner_rpow_integrable_sphere e (by norm_num : (-1:ℝ)< -(1/2:ℝ))).const_mul 16).mono'
    ((measurable_const.inner measurable_subtype_coe).abs.log.pow_const 2).aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  by_cases h : |⟪(e:Space n),(u:Space n)⟫|=0
  · simp only [h,Real.log_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    positivity
  · apply log_sq_le_negative_rpow (lt_of_le_of_ne (abs_nonneg _) (Ne.symm h))
    simpa only [norm_coe,mul_one] using (abs_real_inner_le_norm (e:Space n) (u:Space n))

lemma log_inner_integrable {n : ℕ} [NeZero n] (e : Sphere n) :
    Integrable (fun u : Sphere n => Real.log |⟪(e:Space n),(u:Space n)⟫|) (sigma n) := by
  apply ((log_inner_sq_integrable e).add (integrable_const (1:ℝ))).mono'
    ((measurable_const.inner measurable_subtype_coe).abs.log.aestronglyMeasurable)
  filter_upwards with u
  rw [Real.norm_eq_abs]
  let x := Real.log |⟪(e:Space n),(u:Space n)⟫|
  change |x| ≤ x^2+1
  nlinarith [sq_nonneg (|x|-1),sq_abs x]

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma inner_ne_zero_ae_sphere {n : ℕ} (e : Sphere n) :
    ∀ᵐ (u : Sphere n) ∂sigma n, ⟪(e:Space n),(u:Space n)⟫ ≠ 0 := by
  apply sphere_ae_of_radial (P := fun x : Space n => ⟪(e:Space n),x⟫ ≠ 0)
  · have hR : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      simpa only [ae_iff,not_not,Set.ofPred_eq_eq_singleton] using (measure_singleton (0:ℝ))
    have hp : ∀ᵐ z : perpendicular (e:Space n) × ℝ ∂volume, z.2 ≠ 0 := by
      rw [Measure.volume_eq_prod]
      exact (Measure.ae_prod_iff_ae_ae (by measurability)).mpr (Eventually.of_forall (fun _ => hR))
    have he : ∀ᵐ x : Space n ∂volume, ((shadowMeasurableEquiv e).symm x).2 ≠ 0 :=
      ((shadowMeasurableEquiv_measurePreserving e).symm (shadowMeasurableEquiv e)).quasiMeasurePreserving.ae hp
    filter_upwards [he] with x hx
    have hy := (shadowMeasurableEquiv e).apply_symm_apply x
    have hid (z : perpendicular (e:Space n) × ℝ) :
        ⟪(e:Space n),shadowMeasurableEquiv e z⟫=z.2 := by
      change ⟪(e:Space n),(z.1:Space n)+z.2 • (e:Space n)⟫=z.2
      rw [inner_add_right,perpendicular_inner,inner_smul_right,real_inner_self_eq_norm_sq,norm_coe]
      simp
    rwa [← hid,hy] at hx
  · intro u r _ h
    rw [inner_smul_right,mul_ne_zero_iff] at h
    exact h.2

lemma mean_inner_independent {n : ℕ} (f : ℝ → ℝ) (e v : Sphere n) :
    mean (fun u : Sphere n => f ⟪(e:Space n),(u:Space n)⟫) =
      mean (fun u : Sphere n => f ⟪(v:Space n),(u:Space n)⟫) := by
  let U := (ℝ ∙ ((e:Space n)-(v:Space n)))ᗮ.reflection
  have hev : U e=v := Submodule.reflection_sub ((norm_coe e).trans (norm_coe v).symm)
  have h := mean_rotation U (fun u : Sphere n => f ⟪U (e:Space n),(u:Space n)⟫)
  change mean (fun u : Sphere n => f ⟪U (e:Space n),U (u:Space n)⟫)=_ at h
  simp only [U.inner_map_map] at h
  simpa only [hev] using h

lemma seminorm_pos_ae_sphere {n : ℕ} [NeZero n] {g : Seminorm ℝ (Space n)} (hg : g ≠ 0) :
    ∀ᵐ (u : Sphere n) ∂sigma n, 0 < g u := by
  obtain ⟨R,e,hR,_,hb⟩ := seminorm_coordinate_minorant g hg
  filter_upwards [inner_ne_zero_ae_sphere e] with u hu
  exact (mul_pos hR (abs_pos.mpr (by simpa only [real_inner_comm] using hu))).trans_le (hb u)

lemma log_sq_coercive_bound {a R t : ℝ} (ha : 0<a) (ha1 : a≤1) (hR : 0<R)
    (htl : R*a≤t) (htu : t≤R) :
    (Real.log t)^2 ≤ 2*(Real.log R)^2+2*(Real.log a)^2 := by
  have ht := (mul_pos hR ha).trans_le htl
  have hl0 := Real.log_le_log (mul_pos hR ha) htl
  rw [Real.log_mul hR.ne' ha.ne'] at hl0
  have hl1 := Real.log_le_log ht htu
  have ha0 : Real.log a≤0 := Real.log_nonpos ha.le ha1
  have habs : |Real.log t|≤|Real.log R|+|Real.log a| := by
    rw [abs_le]
    constructor
    · rw [abs_of_nonpos ha0]
      linarith [neg_abs_le (Real.log R)]
    · linarith [le_abs_self (Real.log R),abs_nonneg (Real.log a)]
  have hs := sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤|Real.log R|+|Real.log a|) |>.mpr habs
  nlinarith [sq_nonneg (|Real.log R|-|Real.log a|),sq_abs (Real.log R),sq_abs (Real.log a),sq_abs (Real.log t)]

lemma seminorm_log_sq_integrable {n : ℕ} [NeZero n] {g : Seminorm ℝ (Space n)} (hg : g ≠ 0) :
    Integrable (fun u : Sphere n => (Real.log (g u))^2) (sigma n) := by
  obtain ⟨R,e,hR,hm,hb⟩ := seminorm_coordinate_minorant g hg
  apply ((integrable_const (2*(Real.log R)^2)).add ((log_inner_sq_integrable e).const_mul 2)).mono'
    (((seminorm_continuous n g).comp continuous_subtype_val).measurable.log.pow_const 2).aestronglyMeasurable
  filter_upwards [inner_ne_zero_ae_sphere e] with u hu
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply log_sq_coercive_bound (abs_pos.mpr hu) _ hR _ (hm u)
  · simpa only [norm_coe,mul_one] using abs_real_inner_le_norm (e:Space n) (u:Space n)
  · simpa only [real_inner_comm] using hb u

lemma seminorm_log_integrable {n : ℕ} [NeZero n] {g : Seminorm ℝ (Space n)} (hg : g ≠ 0) :
    Integrable (fun u : Sphere n => Real.log (g u)) (sigma n) := by
  apply ((seminorm_log_sq_integrable hg).add (integrable_const (1:ℝ))).mono'
    (((seminorm_continuous n g).comp continuous_subtype_val).measurable.log.aestronglyMeasurable)
  filter_upwards with u
  rw [Real.norm_eq_abs]
  change |Real.log (g u)| ≤ (Real.log (g u))^2+1
  nlinarith [sq_nonneg (|Real.log (g u)|-1),sq_abs (Real.log (g u))]

lemma seminorm_log_coercivity {n : ℕ} [NeZero n] {g : Seminorm ℝ (Space n)}
    {R : ℝ} {e : Sphere n} (hR : 0<R) (hg : g ≠ 0)
    (hb : ∀ x : Space n,R*|⟪x,(e:Space n)⟫|≤g x) :
    Real.log R+mean (fun u : Sphere n => Real.log |⟪(pole n:Space n),(u:Space n)⟫|) ≤
      mean (fun u : Sphere n => Real.log (g u)) := by
  have hi := integral_mono_ae ((integrable_const (Real.log R)).add (log_inner_integrable e))
    (seminorm_log_integrable hg) (by
      filter_upwards [inner_ne_zero_ae_sphere e] with u hu
      have h := hb u
      rw [real_inner_comm] at h
      simpa only [Pi.add_apply,Real.log_mul hR.ne' (abs_pos.mpr hu).ne'] using
        Real.log_le_log (mul_pos hR (abs_pos.mpr hu)) h)
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const _) (log_inner_integrable e),integral_const] at hi
  simp only [probReal_univ,one_smul] at hi
  change (Real.log R)+mean (fun u : Sphere n => Real.log |⟪(e:Space n),(u:Space n)⟫|)≤_ at hi
  rwa [mean_inner_independent (fun t => Real.log |t|) e (pole n)] at hi

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma unifIntegrable_of_sq_bound {α : Type uα} {ι : Type uι} [MeasurableSpace α] {μ : Measure α}
    {f : ι → α → ℝ} {C : ℝ} (hC : 0≤C)
    (hi : ∀ i,Integrable (f i) μ) (hsq : ∀ i,Integrable (fun x => (f i x)^2) μ)
    (hb : ∀ i,(∫ x,(f i x)^2 ∂μ)≤C) : UnifIntegrable f 1 μ := by
  apply unifIntegrable_of le_rfl (by norm_num) (fun i => (hi i).aestronglyMeasurable)
  intro ε hε
  have hεreal : 0 < ε := hε
  let M : ℝ := C/ε+1
  have hM : 0<M := by dsimp [M]; positivity
  refine ⟨⟨M,hM.le⟩,fun i => ?_⟩
  let T := {x | (⟨M,hM.le⟩ : ℝ≥0)≤‖f i x‖₊}
  have hind : Integrable (T.indicator (f i)) μ := (hi i).indicator₀
    (nullMeasurableSet_le aemeasurable_const (hi i).aestronglyMeasurable.aemeasurable.nnnorm)
  change eLpNorm (T.indicator (f i)) 1 μ ≤ ENNReal.ofReal ε
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hind]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ x,(f i x)^2/M ∂μ := by
      apply integral_mono hind.norm ((hsq i).div_const M)
      intro x
      change ‖T.indicator (f i) x‖ ≤ (f i x)^2/M
      by_cases hx : x∈T
      · rw [indicator_of_mem hx,Real.norm_eq_abs]
        have hx' : M≤|f i x| := hx
        apply (le_div_iff₀ hM).mpr
        nlinarith [sq_abs (f i x)]
      · rw [indicator_of_notMem hx,norm_zero]
        positivity
    _ = (∫ x,(f i x)^2 ∂μ)/M := by simp only [div_eq_mul_inv,integral_mul_const]
    _ ≤ C/M := div_le_div_of_nonneg_right (hb i) hM.le
    _ ≤ ε := by
      apply (div_le_iff₀ hM).mpr
      dsimp [M]
      rw [mul_add,mul_div_cancel₀ _ hεreal.ne']
      linarith

lemma tendsto_integral_of_sq_bound {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : ℕ → α → ℝ} {g : α → ℝ} {C : ℝ} (hC : 0≤C)
    (hi : ∀ i,Integrable (f i) μ) (hsq : ∀ i,Integrable (fun x => (f i x)^2) μ)
    (hb : ∀ i,(∫ x,(f i x)^2 ∂μ)≤C) (hg : Integrable g μ)
    (hc : ∀ᵐ x ∂μ,Tendsto (fun i => f i x) atTop (𝓝 (g x))) :
    Tendsto (fun i => ∫ x,f i x ∂μ) atTop (𝓝 (∫ x,g x ∂μ)) := by
  apply tendsto_integral_of_L1' g hg.aestronglyMeasurable (Eventually.of_forall hi)
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by norm_num)
    (fun i => (hi i).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hg)
    (unifIntegrable_of_sq_bound hC hi hsq hb) hc

lemma seminorm_log_sq_bound {n : ℕ} [NeZero n] {g : Seminorm ℝ (Space n)}
    {r R : ℝ} (hr : 0<r) (hlo : ∃ u : Sphere n,r≤g u) (hhi : ∀ u : Sphere n,g u≤R) :
    mean (fun u : Sphere n => (Real.log (g u))^2) ≤
      2*(|Real.log r|+|Real.log R|)^2+
        2*mean (fun u : Sphere n => (Real.log |⟪(pole n:Space n),(u:Space n)⟫|)^2) := by
  have hg : g ≠ 0 := by
    rintro rfl
    obtain ⟨u,hu⟩ := hlo
    simpa using hr.not_ge hu
  obtain ⟨a,e,ha,hm,hb⟩ := seminorm_coordinate_minorant g hg
  have hla : r≤a := by obtain ⟨u,hu⟩ := hlo; exact hu.trans (hm u)
  have hha : a≤R := by
    have h := hb e
    rw [real_inner_self_eq_norm_sq,norm_coe] at h
    norm_num at h
    exact h.trans (hhi e)
  have hlogs : |Real.log a|≤|Real.log r|+|Real.log R| := by
    have h1 := Real.log_le_log hr hla
    have h2 := Real.log_le_log ha hha
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log r),abs_nonneg (Real.log R)]
    · linarith [le_abs_self (Real.log R),abs_nonneg (Real.log r)]
  have hlogs2 : (Real.log a)^2≤(|Real.log r|+|Real.log R|)^2 := by
    simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg _) (by positivity) |>.mpr hlogs
  have h := integral_mono_ae (seminorm_log_sq_integrable hg)
    ((integrable_const (2*(Real.log a)^2)).add ((log_inner_sq_integrable e).const_mul 2)) (by
      filter_upwards [inner_ne_zero_ae_sphere e] with u hu
      change (Real.log (g u))^2≤2*(Real.log a)^2+2*(Real.log |⟪(e:Space n),(u:Space n)⟫|)^2
      apply log_sq_coercive_bound (abs_pos.mpr hu) _ ha _ (hm u)
      · simpa only [norm_coe,mul_one] using abs_real_inner_le_norm (e:Space n) (u:Space n)
      · simpa only [real_inner_comm] using hb u)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) ((log_inner_sq_integrable e).const_mul 2),
    integral_const,integral_const_mul,probReal_univ,one_smul] at h
  change mean _ ≤ _+2*mean _ at h
  rw [mean_inner_independent (fun t => (Real.log |t|)^2) e (pole n)] at h
  linarith

lemma seminorm_log_integral_tendsto {n : ℕ} [NeZero n]
    {g : ℕ → Seminorm ℝ (Space n)} {f : Seminorm ℝ (Space n)} {r R : ℝ}
    (hr : 0<r) (hlo : ∀ i,∃ u : Sphere n,r≤g i u)
    (hhi : ∀ i (u : Sphere n),g i u≤R) (hf : f ≠ 0)
    (hc : ∀ u : Sphere n,Tendsto (fun i => g i u) atTop (𝓝 (f u))) :
    Tendsto (fun i => mean (fun u : Sphere n => Real.log (g i u))) atTop
      (𝓝 (mean (fun u : Sphere n => Real.log (f u)))) := by
  have hg (i : ℕ) : g i ≠ 0 := by
    intro h
    obtain ⟨u,hu⟩ := hlo i
    rw [h] at hu
    exact hr.not_ge hu
  apply tendsto_integral_of_sq_bound (C := 2*(|Real.log r|+|Real.log R|)^2+
    2*mean (fun u : Sphere n => (Real.log |⟪(pole n:Space n),(u:Space n)⟫|)^2))
  · have hp : 0 ≤ mean (fun u : Sphere n => (Real.log |⟪(pole n:Space n),(u:Space n)⟫|)^2) :=
      integral_nonneg (fun _ => sq_nonneg _)
    positivity
  · exact fun i => seminorm_log_integrable (hg i)
  · exact fun i => seminorm_log_sq_integrable (hg i)
  · exact fun i => seminorm_log_sq_bound hr (hlo i) (hhi i)
  · exact seminorm_log_integrable hf
  · filter_upwards [seminorm_pos_ae_sphere hf] with u hu
    exact (Real.continuousAt_log hu.ne').tendsto.comp (hc u)

end PettyProjection.Spherical
end

noncomputable section
open Set Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma seminorm_lipschitz_of_sphere_bound {n : ℕ} (g : Seminorm ℝ (Space n))
    {R : ℝ≥0} (hR : ∀ u : Sphere n,g u≤R) : LipschitzWith R g := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |g x-g y|≤(R:ℝ)*dist x y
  exact (abs_sub_map_le_sub g x y).trans (by
    simpa only [dist_eq_norm] using seminorm_le_max_norm g hR (x-y))

def radialExtension {n : ℕ} (f : Sphere n → ℝ) (x : Space n) : ℝ :=
  if hx : x=0 then 0 else ‖x‖*f ⟨‖x‖⁻¹ • x,by
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg
      (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)⟩

lemma radialExtension_sphere {n : ℕ} (f : Sphere n → ℝ) (u : Sphere n) :
    radialExtension f u=f u := by
  have hu0 : (u:Space n)≠0 := by intro h; have := norm_coe u; simp [h] at this
  simp only [radialExtension,dite_eq_right hu0,norm_coe,inv_one,one_smul,one_mul]

lemma radialExtension_seminorm {n : ℕ} (g : Seminorm ℝ (Space n)) (x : Space n) :
    radialExtension (fun u : Sphere n => g u) x=g x := by
  by_cases hx : x=0
  · simp [radialExtension,hx]
  · simp only [radialExtension,dite_eq_right hx,map_smul_eq_mul,Real.norm_of_nonneg
      (inv_nonneg.mpr (norm_nonneg _))]
    rw [← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_mul]

lemma radialExtension_tendsto {n : ℕ} {g : ℕ → Seminorm ℝ (Space n)}
    {f : Sphere n → ℝ} (h : ∀ u : Sphere n,Tendsto (fun i => g i u) atTop (𝓝 (f u)))
    (x : Space n) : Tendsto (fun i => g i x) atTop (𝓝 (radialExtension f x)) := by
  have he (i : ℕ) : g i x=radialExtension (fun u : Sphere n => g i u) x :=
    (radialExtension_seminorm (g i) x).symm
  simp_rw [he]
  unfold radialExtension
  split_ifs with hx
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds.mul (h _)

/-- Uniform sphere compactness of bounded seminorms, including all singular
limits. The limiting algebraic object is proved to be a seminorm. -/
theorem bounded_seminorm_subsequence {n : ℕ} (g : ℕ → Seminorm ℝ (Space n))
    {R : ℝ≥0} (hR : ∀ i (u : Sphere n),g i u≤R) :
    ∃ f : Seminorm ℝ (Space n), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun i (u : Sphere n) => g (φ i) u) (fun u => f u) atTop ∧
      (∀ x,Tendsto (fun i => g (φ i) x) atTop (𝓝 (f x))) := by
  let F : ℕ → (BoundedContinuousFunction (Sphere n) ℝ) := fun i =>
    BoundedContinuousFunction.mkOfCompact ⟨fun u => g i u,
      (seminorm_continuous n (g i)).comp continuous_subtype_val⟩
  have hL (i : ℕ) : LipschitzWith R (F i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (seminorm_lipschitz_of_sphere_bound (g i) (hR i)).dist_le_mul (x:Space n) (y:Space n)
  have hc : IsCompact (closure (range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Icc (0:ℝ) R) isCompact_Icc
    · intro f u hf
      obtain ⟨i,rfl⟩ := hf
      exact ⟨apply_nonneg (g i) (u:Space n),hR i u⟩
    · apply UniformEquicontinuous.equicontinuous
      apply LipschitzWith.uniformEquicontinuous _ R
      intro f
      obtain ⟨i,hi⟩ := f.property
      simpa only [hi] using hL i
  obtain ⟨f,_,φ,hφ,hconv⟩ := hc.tendsto_subseq (fun i => subset_closure (mem_range_self i))
  have hunif : TendstoUniformly (fun i => (F (φ i) : Sphere n → ℝ)) f atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  have hpoint := radialExtension_tendsto (g := fun i => g (φ i)) hunif.tendsto_at
  let q : Seminorm ℝ (Space n) := Seminorm.of (radialExtension f)
    (fun x y => le_of_tendsto_of_tendsto (hpoint (x+y)) ((hpoint x).add (hpoint y))
      (Eventually.of_forall (fun i => map_add_le_add (g (φ i)) x y)))
    (fun a x => tendsto_nhds_unique (hpoint (a • x)) (by
      simp_rw [map_smul_eq_mul]
      exact tendsto_const_nhds.mul (hpoint x)))
  refine ⟨q,φ,hφ,?_,hpoint⟩
  have he : (fun u : Sphere n => q u)=(f : Sphere n → ℝ) := by
    funext u; exact radialExtension_sphere f u
  rw [he]
  exact hunif

end PettyProjection.Spherical
end

noncomputable section
open Set Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

/-- Closed unit set of the actual seminorm. It is allowed to be a cylinder. -/
def seminormUnit {n : ℕ} (g : Seminorm ℝ (Space n)) : Set (Space n) := {x | g x≤1}

lemma seminormUnit_zero {n : ℕ} (g : Seminorm ℝ (Space n)) : 0∈seminormUnit g := by
  simp [seminormUnit]

lemma seminormUnit_closed {n : ℕ} (g : Seminorm ℝ (Space n)) : IsClosed (seminormUnit g) :=
  isClosed_le (seminorm_continuous n g) continuous_const

lemma seminormUnit_convex {n : ℕ} (g : Seminorm ℝ (Space n)) : Convex ℝ (seminormUnit g) := by
  simpa only [seminormUnit,← g.closedBall_zero_eq] using g.convex_closedBall 0 1

lemma seminormUnit_balanced {n : ℕ} (g : Seminorm ℝ (Space n)) : Balanced ℝ (seminormUnit g) := by
  simpa only [seminormUnit,← g.closedBall_zero_eq] using g.balanced_closedBall_zero 1

lemma seminormUnit_nhds {n : ℕ} (g : Seminorm ℝ (Space n)) : seminormUnit g∈𝓝 (0:Space n) := by
  have ho : IsOpen {x : Space n | g x<1} := isOpen_lt (seminorm_continuous n g) continuous_const
  exact Filter.mem_of_superset (ho.mem_nhds (by simp)) (fun x hx => show g x≤1 from hx.le)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere)

lemma integrable_abs_inner {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (y : Space n) :
    Integrable (fun x => |⟪x,y⟫|) μ := by
  apply (hμ.mul_const ‖y‖).mono' (by fun_prop)
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_abs] using abs_real_inner_le_norm x y)

/-- The actual cosine-transform norm furnished by a spanning measure. -/
def cosineSeminorm {n : ℕ} (μ : Measure (Space n))
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) : Seminorm ℝ (Space n) :=
  Seminorm.of (fun y => ∫ x,|⟪x,y⟫| ∂μ)
    (fun y z => by
      rw [← integral_add (integrable_abs_inner hμ y) (integrable_abs_inner hμ z)]
      apply integral_mono (integrable_abs_inner hμ (y+z))
        ((integrable_abs_inner hμ y).add (integrable_abs_inner hμ z))
      intro x
      change |⟪x,y+z⟫|≤ |⟪x,y⟫|+|⟪x,z⟫|
      rw [inner_add_right]
      exact abs_add_le _ _)
    (fun a y => by
      simp only [inner_smul_right,abs_mul,Real.norm_eq_abs,integral_const_mul])

lemma support_integrable {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty) :
    Integrable (support K) μ := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  apply (hμ.const_mul R).mono' (support_continuous hK).aestronglyMeasurable
  refine Eventually.of_forall (fun x => ?_)
  obtain ⟨y,hy,he⟩ := support_attained hK hne x
  rw [Real.norm_eq_abs,he]
  exact (abs_real_inner_le_norm x y).trans (by nlinarith [norm_nonneg x,hbound y hy])

lemma abs_inner_le_support {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hsym : ∀ y∈K,-y∈K) {y : Space n} (hy : y∈K) (x : Space n) :
    |⟪x,y⟫|≤ support K x := by
  rw [abs_le]
  constructor
  · have hh := inner_le_support hK (hsym y hy) x
    rw [inner_neg_right] at hh
    linarith
  · exact inner_le_support hK hy x

lemma cosine_le_functional {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {K : Set (Space n)} (hK : IsCompact K) (hsym : ∀ y∈K,-y∈K)
    {y : Space n} (hy : y∈K) : cosineSeminorm μ hμ y≤ supportFunctional μ K := by
  exact integral_mono (integrable_abs_inner hμ y) (support_integrable hμ hK ⟨y,hy⟩)
    (abs_inner_le_support hK hsym hy)

lemma functional_smul {n : ℕ} {μ : Measure (Space n)}
    {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty) {a : ℝ} (ha : 0≤a) :
    supportFunctional μ (a • K)=a*supportFunctional μ K := by
  unfold supportFunctional
  simp_rw [support_smul_set hK hne ha]
  exact integral_const_mul _ _

lemma functional_nonneg {n : ℕ} {μ : Measure (Space n)}
    {K : Set (Space n)} (hK : IsCompact K) (hK0 : 0∈K) : 0≤ supportFunctional μ K :=
  integral_nonneg (fun x => support_nonneg hK hK0 x)

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.RelativeGauges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

/-- A genuine extended gauge of a relative symmetric convex body. The lower
bound is only on its supporting subspace, so cylinders are retained. -/
structure RelativeGauge {n : ℕ} (V : Submodule ℝ (Space n)) where
  toSeminorm : Seminorm ℝ (Space n)
  projection : ∀ x,toSeminorm (V.starProjection x)=toSeminorm x
  lower : ∃ c : ℝ,0<c ∧ ∀ x,c*‖V.starProjection x‖≤toSeminorm x

instance instCoeFunRelativeGaugeForallSpaceReal {n : ℕ} {V : Submodule ℝ (Space n)} : CoeFun (RelativeGauge V) (fun _ => Space n → ℝ) :=
  ⟨fun g => g.toSeminorm⟩

namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

def body (g : RelativeGauge V) : Set (Space n) := (V : Set (Space n)) ∩ seminormUnit g.toSeminorm

lemma zero_mem (g : RelativeGauge V) : 0∈g.body := ⟨V.zero_mem,seminormUnit_zero _⟩
lemma nonempty (g : RelativeGauge V) : g.body.Nonempty := ⟨0,g.zero_mem⟩
lemma convex (g : RelativeGauge V) : Convex ℝ g.body := V.convex.inter (seminormUnit_convex _)
lemma closed (g : RelativeGauge V) : IsClosed g.body := V.closed_of_finiteDimensional.inter (seminormUnit_closed _)
lemma neg_mem (g : RelativeGauge V) {x : Space n} (hx : x∈g.body) : -x∈g.body := by
  exact ⟨V.neg_mem hx.1,by
    change g.toSeminorm (-x)≤1
    rw [map_neg_eq_map]
    exact hx.2⟩

lemma compact (g : RelativeGauge V) : IsCompact g.body := by
  obtain ⟨c,hc,hbound⟩ := g.lower
  apply (isCompact_closedBall (0:Space n) c⁻¹).of_isClosed_subset g.closed
  intro x hx
  rw [mem_closedBall,dist_zero_right,inv_eq_one_div,le_div_iff₀ hc]
  have hb := hbound x
  rw [V.starProjection_eq_self_iff.mpr hx.1] at hb
  have hh : g x≤1 := hx.2
  nlinarith

lemma ne_zero (g : RelativeGauge V) (hV : V≠⊥) : g.toSeminorm≠0 := by
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff V).mp hV
  obtain ⟨c,hc,hb⟩ := g.lower
  intro h
  have hh := hb x
  rw [V.starProjection_eq_self_iff.mpr hx,h] at hh
  have : 0<c*‖x‖ := mul_pos hc (norm_pos_iff.mpr hx0)
  exact this.not_ge hh

lemma pos (g : RelativeGauge V) {x : Space n} (hx : x∈V) (hx0 : x≠0) : 0<g x := by
  obtain ⟨c,hc,hb⟩ := g.lower
  have hh := hb x
  rw [V.starProjection_eq_self_iff.mpr hx] at hh
  exact (mul_pos hc (norm_pos_iff.mpr hx0)).trans_le hh

lemma radial_mem (g : RelativeGauge V) {x : Space n} (hx : x∈V) (hx0 : x≠0) :
    (g x)⁻¹ • x∈g.body := by
  refine ⟨V.smul_mem _ hx,?_⟩
  change g.toSeminorm ((g x)⁻¹ • x)≤1
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (apply_nonneg _ _)),
    inv_mul_cancel₀ (g.pos hx hx0).ne']

lemma cosine_le_gauge_functional (g : RelativeGauge V) {μ : MeasureTheory.Measure (Space n)}
    (hμ : MeasureTheory.Integrable (fun x : Space n => ‖x‖) μ) (x : Space n) :
    cosineSeminorm μ hμ (V.starProjection x)≤g x*supportFunctional μ g.body := by
  by_cases hx : V.starProjection x=0
  · rw [hx,map_zero]
    exact mul_nonneg (apply_nonneg _ _) (functional_nonneg g.compact g.zero_mem)
  have hp := g.pos (V.starProjection_apply_mem x) hx
  have hh := cosine_le_functional hμ g.compact (fun y hy => g.neg_mem hy)
    (g.radial_mem (V.starProjection_apply_mem x) hx)
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_le_iff₀ hp,
    g.projection] at hh
  simpa only [mul_comm] using hh

/-- Every positive dilation is again the exact relative gauge. -/
def scale (g : RelativeGauge V) (a : ℝ) (ha : 0<a) : RelativeGauge V where
  toSeminorm := Seminorm.of (fun x => a*g x)
    (fun x y => by simpa only [mul_add] using mul_le_mul_of_nonneg_left (map_add_le_add g.toSeminorm x y) ha.le)
    (fun r x => by rw [map_smul_eq_mul]; ring)
  projection x := by change a*g (V.starProjection x)=a*g x; rw [g.projection]
  lower := by
    obtain ⟨c,hc,hb⟩ := g.lower
    refine ⟨a*c,mul_pos ha hc,fun x => ?_⟩
    change a*c*‖V.starProjection x‖≤a*g x
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb x) ha.le

lemma body_scale (g : RelativeGauge V) (a : ℝ) (ha : 0<a) :
    (g.scale a ha).body=a⁻¹ • g.body := by
  ext x
  constructor
  · rintro ⟨hx,hg⟩
    refine ⟨a • x,⟨V.smul_mem a hx,?_⟩,inv_smul_smul₀ ha.ne' x⟩
    change g.toSeminorm (a • x)≤1
    rw [map_smul_eq_mul,Real.norm_of_nonneg ha.le]
    exact hg
  · rintro ⟨y,hy,rfl⟩
    refine ⟨V.smul_mem _ hy.1,?_⟩
    change a*g.toSeminorm (a⁻¹ • y)≤1
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr ha.le),← mul_assoc,
      mul_inv_cancel₀ ha.ne',one_mul]
    exact hy.2

lemma functional_scale (g : RelativeGauge V) (a : ℝ) (ha : 0<a)
    (μ : MeasureTheory.Measure (Space n)) :
    supportFunctional μ (g.scale a ha).body=a⁻¹*supportFunctional μ g.body := by
  rw [g.body_scale a ha,functional_smul g.compact g.nonempty (inv_nonneg.mpr ha.le)]

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

/-- Variational objective: the logarithmic endpoint (k=1), or the linear (k=2). -/
def objectiveIntegrand (logarithmic : Bool) (t : ℝ) : ℝ :=
  if logarithmic then Real.log t else t

def objective {n : ℕ} (logarithmic : Bool) (g : Seminorm ℝ (Space n)) : ℝ :=
  mean (fun u : Sphere n => objectiveIntegrand logarithmic (g u))

lemma seminorm_integrable {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n)) :
    Integrable (fun u : Sphere n => g u) (sigma n) :=
  continuous_integrable ((seminorm_continuous n g).comp continuous_subtype_val)

lemma objective_integrable {n : ℕ} [NeZero n] (b : Bool) {g : Seminorm ℝ (Space n)} (hg : g≠0) :
    Integrable (fun u : Sphere n => objectiveIntegrand b (g u)) (sigma n) := by
  cases b
  · exact seminorm_integrable g
  · exact seminorm_log_integrable hg

lemma objectiveIntegrand_strictMono (b : Bool) : StrictMonoOn (objectiveIntegrand b) (Ioi 0) := by
  cases b
  · exact fun _ _ _ _ h => h
  · exact Real.strictMonoOn_log

lemma objective_mono {n : ℕ} [NeZero n] (b : Bool) {g f : Seminorm ℝ (Space n)}
    (hg : g≠0) (hf : f≠0) (hle : ∀ x,g x≤f x) : objective b g≤objective b f := by
  apply integral_mono_ae (objective_integrable b hg) (objective_integrable b hf)
  filter_upwards [seminorm_pos_ae_sphere hg,seminorm_pos_ae_sphere hf] with u hu hv
  exact (objectiveIntegrand_strictMono b).monotoneOn hu hv (hle u)

lemma coordinate_mean_pos (n : ℕ) [NeZero n] :
    0 < mean (fun u : Sphere n => |⟪(pole n:Space n),(u:Space n)⟫|) := by
  let f := fun u : Sphere n => |⟪(pole n:Space n),(u:Space n)⟫|
  have hc : Continuous f := by fun_prop
  apply integral_pos_of_integrable_nonneg_nonzero (x := pole n) hc (continuous_integrable hc) (fun _ => abs_nonneg _)
  dsimp [f]
  simp only [real_inner_self_eq_norm_sq,norm_coe,one_pow,abs_one,one_ne_zero,not_false_eq_true]

/-- Objective sublevels impose a common Lipschitz bound, including cylinders. -/
lemma objective_coercive {n : ℕ} [NeZero n] (b : Bool) (M : ℝ) :
    ∃ R : ℝ,0<R ∧ ∀ g : Seminorm ℝ (Space n),g≠0 → objective b g≤M → ∀ u : Sphere n,g u≤R := by
  let c := mean (fun u : Sphere n => Real.log |⟪(pole n:Space n),(u:Space n)⟫|)
  let d := mean (fun u : Sphere n => |⟪(pole n:Space n),(u:Space n)⟫|)
  have hd : 0<d := coordinate_mean_pos n
  cases b
  · refine ⟨max 1 (M/d),lt_of_lt_of_le zero_lt_one (le_max_left _ _),fun g hg hM u => ?_⟩
    obtain ⟨R,e,hR,hm,hb⟩ := seminorm_coordinate_minorant g hg
    have hlow : R*d≤objective false g := by
      have hi : Integrable (fun u : Sphere n => |⟪(e:Space n),(u:Space n)⟫|) (sigma n) :=
        continuous_integrable (by fun_prop : Continuous (fun u : Sphere n => |⟪(e:Space n),(u:Space n)⟫|))
      have h := integral_mono (hi.const_mul R) (seminorm_integrable g) (fun u => by
        simpa only [real_inner_comm] using hb u)
      rw [integral_const_mul] at h
      change R*mean _≤_ at h
      rw [mean_inner_independent (fun t => |t|) e (pole n)] at h
      exact h
    exact (hm u).trans (((le_div_iff₀ hd).mpr (hlow.trans hM)).trans (le_max_right _ _))
  · refine ⟨Real.exp (M-c),Real.exp_pos _,fun g hg hM u => ?_⟩
    obtain ⟨R,e,hR,hm,hb⟩ := seminorm_coordinate_minorant g hg
    have hlow := seminorm_log_coercivity hR hg hb
    change mean (fun u : Sphere n => Real.log (g u))≤M at hM
    have hh : Real.log R≤M-c := by change Real.log R+c≤_ at hlow; linarith
    exact (hm u).trans ((Real.log_le_iff_le_exp hR).mp hh)

lemma objective_tendsto {n : ℕ} [NeZero n] (b : Bool)
    {g : ℕ → Seminorm ℝ (Space n)} {f : Seminorm ℝ (Space n)} {r R : ℝ}
    (hr : 0<r) (hlo : ∀ i,∃ u : Sphere n,r≤g i u) (hhi : ∀ i (u : Sphere n),g i u≤R)
    (hf : f≠0) (hc : ∀ u : Sphere n,Tendsto (fun i => g i u) atTop (𝓝 (f u))) :
    Tendsto (fun i => objective b (g i)) atTop (𝓝 (objective b f)) := by
  cases b
  · apply tendsto_integral_of_dominated_convergence (fun _ => |R|)
    · exact fun i => (seminorm_integrable (g i)).aestronglyMeasurable
    · exact integrable_const _
    · intro i
      exact Eventually.of_forall (fun u => by
        change ‖g i u‖≤|R|
        rw [Real.norm_of_nonneg (apply_nonneg (g i) _)]
        exact (hhi i u).trans (le_abs_self _))
    · exact Eventually.of_forall hc
  · exact seminorm_log_integral_tendsto hr hlo hhi hf hc

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

lemma seminorm_positive_subspace_bound {n : ℕ} (V : Submodule ℝ (Space n)) (hV : V≠⊥)
    (g : Seminorm ℝ (Space n)) (hg : ∀ x∈V,x≠0 → 0<g x) :
    ∃ c : ℝ,0<c ∧ ∀ x,c*‖V.starProjection x‖≤g (V.starProjection x) := by
  let S : Set (Space n) := (V : Set (Space n)) ∩ sphere 0 1
  obtain ⟨v,hv,hv0⟩ := (Submodule.ne_bot_iff V).mp hV
  have hne : S.Nonempty := ⟨‖v‖⁻¹ • v,V.smul_mem _ hv,by simp [norm_smul,hv0]⟩
  have hc : IsCompact S := (isCompact_sphere (0:Space n) 1).inter_left V.closed_of_finiteDimensional
  obtain ⟨u,hu,hmin⟩ := hc.exists_isMinOn hne (seminorm_continuous n g).continuousOn
  have hu1 : ‖u‖=1 := by simpa only [mem_sphere,dist_zero_right] using hu.2
  have hu0 : u≠0 := by intro h; simp [h] at hu1
  refine ⟨g u,hg u hu.1 hu0,fun x => ?_⟩
  by_cases hx : V.starProjection x=0
  · simp [hx]
  have hn : 0<‖V.starProjection x‖ := norm_pos_iff.mpr hx
  have hunit : ‖V.starProjection x‖⁻¹ • V.starProjection x∈S :=
    ⟨V.smul_mem _ (V.starProjection_apply_mem x),by simp [norm_smul,hn.ne']⟩
  have hh : g u≤g (‖V.starProjection x‖⁻¹ • V.starProjection x) := hmin hunit
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le)] at hh
  have h := mul_le_mul_of_nonneg_left hh hn.le
  rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul] at h
  simpa only [mul_comm] using h

namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

/-- Extended gauge of the unit ball in V. -/
def ball (V : Submodule ℝ (Space n)) : RelativeGauge V where
  toSeminorm := (normSeminorm ℝ (Space n)).comp V.starProjection.toLinearMap
  projection x := by
    change ‖V.starProjection (V.starProjection x)‖=‖V.starProjection x‖
    rw [V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)]
  lower := ⟨1,zero_lt_one,fun _ => by simp⟩

lemma cylinder_nhds {K : Set (Space n)}
    (hinner : ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈K) :
    V.starProjection ⁻¹' K∈𝓝 (0:Space n) := by
  obtain ⟨r,hr,hin⟩ := hinner
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0:Space n) hr)
  intro x hx
  apply hin _ (V.starProjection_apply_mem x)
  exact (V.norm_starProjection_apply_le x).trans (by
    have hh : ‖x‖<r := by simpa only [mem_ball,dist_zero_right] using hx
    exact hh.le)

/-- Recover the relative extended gauge from an actual relative convex body. -/
def ofBody {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (hb : Balanced ℝ K)
    (hinner : ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈K) : RelativeGauge V := by
  let Z := V.starProjection ⁻¹' K
  have hZc : Convex ℝ Z := hc.linear_preimage V.starProjection.toLinearMap
  have hZb : Balanced ℝ Z := by
    intro a ha y hy
    obtain ⟨z,hz,rfl⟩ := hy
    change V.starProjection (a • z)∈K
    rw [map_smul]
    exact hb a ha ⟨V.starProjection z,hz,rfl⟩
  have hZn : Z∈𝓝 (0:Space n) := cylinder_nhds hinner
  let g := gaugeSeminorm hZb hZc (absorbent_nhds_zero hZn)
  refine ⟨g,?_,?_⟩
  · intro x
    change gauge Z (V.starProjection x)=gauge Z x
    simp only [gauge_def',Z,mem_preimage,map_smul,
      V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)]
  · obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
    refine ⟨R⁻¹,inv_pos.mpr hR,fun x => ?_⟩
    change R⁻¹*‖V.starProjection x‖≤gauge Z x
    unfold gauge
    apply le_csInf (absorbent_nhds_zero hZn).gauge_set_nonempty
    rintro r ⟨hr,y,hy,rfl⟩
    rw [map_smul,norm_smul,Real.norm_of_nonneg hr.le]
    have hh : ‖V.starProjection y‖≤R := hbound _ hy
    calc
      R⁻¹*(r*‖V.starProjection y‖)≤R⁻¹*(r*R) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hr.le) (inv_nonneg.mpr hR.le)
      _ = r := by field_simp

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

lemma support_mono_compact {n : ℕ} {K L : Set (Space n)} (hK : IsCompact K)
    (hKn : K.Nonempty) (hL : IsCompact L) (hsub : K⊆L) (u : Space n) :
    support K u≤ support L u := by
  obtain ⟨x,hx,he⟩ := support_attained hK hKn u
  rw [he]
  exact inner_le_support hL (hsub hx) u

lemma functional_mono_compact {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {K L : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty) (hL : IsCompact L) (hsub : K⊆L) :
    supportFunctional μ K≤ supportFunctional μ L :=
  integral_mono (support_integrable hμ hK hKn) (support_integrable hμ hL (hKn.mono hsub))
    (support_mono_compact hK hKn hL hsub)

namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

lemma balanced (g : RelativeGauge V) : Balanced ℝ g.body := by
  intro a ha y hy
  obtain ⟨z,hz,rfl⟩ := hy
  refine ⟨V.smul_mem _ hz.1,?_⟩
  exact (seminormUnit_balanced g.toSeminorm) a ha ⟨z,hz.2,rfl⟩

lemma inner_ball (g : RelativeGauge V) : ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈g.body := by
  obtain ⟨ε,hε,hεg⟩ := Metric.mem_nhds_iff.mp (seminormUnit_nhds g.toSeminorm)
  refine ⟨ε/2,by positivity,fun x hx hnorm => ⟨hx,hεg ?_⟩⟩
  rw [mem_ball,dist_zero_right]
  linarith

lemma body_subset_smul (g f : RelativeGauge V) {a : ℝ} (ha : 0<a)
    (hle : ∀ x,f x≤a*g x) : g.body⊆a • f.body := by
  intro x hx
  refine ⟨a⁻¹ • x,⟨V.smul_mem _ hx.1,?_⟩,smul_inv_smul₀ ha.ne' x⟩
  change f.toSeminorm (a⁻¹ • x)≤1
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr ha.le),inv_mul_le_iff₀ ha,mul_one]
  exact (hle x).trans (mul_le_of_le_one_right ha.le hx.2)

lemma functional_le_scale (g f : RelativeGauge V) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {a : ℝ} (ha : 0<a)
    (hle : ∀ x,f x≤a*g x) : supportFunctional μ g.body≤a*supportFunctional μ f.body := by
  have hh := functional_mono_compact hμ g.compact g.nonempty (f.compact.smul a)
    (g.body_subset_smul f ha hle)
  rwa [functional_smul f.compact f.nonempty ha.le] at hh

lemma functional_pos (g : RelativeGauge V) (hV : V≠⊥) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x∈V,x≠0 → 0<cosineSeminorm μ hμ x) : 0 < supportFunctional μ g.body := by
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff V).mp hV
  have hy := g.radial_mem hx hx0
  have hqy := hq _ hy.1 (smul_ne_zero (inv_ne_zero (g.pos hx hx0).ne') hx0)
  exact hqy.trans_le (cosine_le_functional hμ g.compact (fun _ h => g.neg_mem h) hy)

lemma normalized_lower (g : RelativeGauge V) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hn : supportFunctional μ g.body=1) (x : Space n) :
    cosineSeminorm μ hμ (V.starProjection x)≤g x := by
  have hh := g.cosine_le_gauge_functional hμ x
  rwa [hn,mul_one] at hh

lemma support_bound (g : RelativeGauge V) {c : ℝ} (hc : 0<c)
    (hl : ∀ x,c*‖V.starProjection x‖≤g x) (u : Space n) : support g.body u≤c⁻¹*‖u‖ := by
  apply (support_le_iff g.compact g.nonempty).mpr
  intro x hx
  have hh := hl x
  rw [V.starProjection_eq_self_iff.mpr hx.1] at hh
  have hb : ‖x‖≤c⁻¹ := by
    rw [inv_eq_one_div,le_div_iff₀ hc]
    have hx1 : g x≤1 := hx.2
    nlinarith
  exact (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg u])

lemma functional_bound (g : RelativeGauge V) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {c : ℝ} (hc : 0<c)
    (hl : ∀ x,c*‖V.starProjection x‖≤g x) : supportFunctional μ g.body≤c⁻¹*(∫ x,‖x‖ ∂μ) := by
  have hh := integral_mono (support_integrable hμ g.compact g.nonempty) (hμ.const_mul c⁻¹)
    (g.support_bound hc hl)
  rwa [integral_const_mul] at hh

lemma seminorm_close_ambient [NeZero n] (g f : Seminorm ℝ (Space n)) {ε : ℝ}
    (hclose : ∀ u : Sphere n,|g u-f u|≤ε) (x : Space n) : |g x-f x|≤ε*‖x‖ := by
  by_cases hx : x=0
  · simp [hx]
  have hp : 0<‖x‖ := norm_pos_iff.mpr hx
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hp.ne']⟩
  have hh := hclose u
  change |g (‖x‖⁻¹ • x)-f (‖x‖⁻¹ • x)|≤ε at hh
  rw [map_smul_eq_mul,map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),← mul_sub,
    abs_mul,abs_of_pos (inv_pos.mpr hp),inv_mul_le_iff₀ hp] at hh
  simpa only [mul_comm] using hh

lemma close_le_scale [NeZero n] (g f : RelativeGauge V) {c ε : ℝ} (hc : 0<c) (hε : 0≤ε)
    (hl : ∀ x,c*‖V.starProjection x‖≤g x)
    (hclose : ∀ u : Sphere n,|g u-f u|≤ε) (x : Space n) : f x≤(1+ε/c)*g x := by
  have hh := seminorm_close_ambient g.toSeminorm f.toSeminorm hclose (V.starProjection x)
  rw [g.projection,f.projection] at hh
  have hdiff := (abs_le.mp hh).1
  have hprod := mul_le_mul_of_nonneg_left (hl x) (div_nonneg hε hc.le)
  have he : (ε/c)*(c*‖V.starProjection x‖)=ε*‖V.starProjection x‖ := by field_simp
  rw [he] at hprod
  nlinarith

lemma functional_close [NeZero n] (g f : RelativeGauge V) {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {c ε : ℝ} (hc : 0<c) (hε : 0≤ε)
    (hg : ∀ x,c*‖V.starProjection x‖≤g x) (hf : ∀ x,c*‖V.starProjection x‖≤f x)
    (hclose : ∀ u : Sphere n,|g u-f u|≤ε) :
    |supportFunctional μ g.body-supportFunctional μ f.body|≤(ε/c)*(c⁻¹*(∫ x,‖x‖ ∂μ)) := by
  have ha : 0<1+ε/c := by positivity
  have h1 := g.functional_le_scale f hμ ha (g.close_le_scale f hc hε hg hclose)
  have hclose' : ∀ u : Sphere n,|f u-g u|≤ε := fun u => by rw [abs_sub_comm]; exact hclose u
  have h2 := f.functional_le_scale g hμ ha (f.close_le_scale g hc hε hf hclose')
  have hb1 := mul_le_mul_of_nonneg_left (g.functional_bound hμ hc hg) (div_nonneg hε hc.le)
  have hb2 := mul_le_mul_of_nonneg_left (f.functional_bound hμ hc hf) (div_nonneg hε hc.le)
  rw [abs_le]
  constructor <;> nlinarith

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {V : Submodule ℝ (Space n)}

lemma functional_tendsto {g : ℕ → RelativeGauge V} {f : RelativeGauge V}
    {μ : Measure (Space n)} (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {c : ℝ} (hc : 0<c) (hg : ∀ i x,c*‖V.starProjection x‖≤g i x)
    (hf : ∀ x,c*‖V.starProjection x‖≤f x)
    (hunif : TendstoUniformly (fun i (u : Sphere n) => g i u) (fun u => f u) atTop) :
    Tendsto (fun i => supportFunctional μ (g i).body) atTop (𝓝 (supportFunctional μ f.body)) := by
  let C := c⁻¹*(c⁻¹*(∫ x,‖x‖ ∂μ))
  have hC : 0≤C := mul_nonneg (inv_nonneg.mpr hc.le)
    (mul_nonneg (inv_nonneg.mpr hc.le) (integral_nonneg (fun _ => norm_nonneg _)))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hδ : 0<ε/(C+1) := div_pos hε (by linarith)
  have hu := (Metric.tendstoUniformly_iff.mp hunif) (ε/(C+1)) hδ
  obtain ⟨N,hN⟩ := eventually_atTop.mp hu
  refine ⟨N,fun i hi => ?_⟩
  have hh := (g i).functional_close f hμ hc hδ.le (hg i) hf (fun u => by
    have h := hN i hi u
    rw [Real.dist_eq] at h
    simpa only [abs_sub_comm] using h.le)
  rw [Real.dist_eq]
  have he : (ε/(C+1)/c)*(c⁻¹*(∫ x,‖x‖ ∂μ))=(ε/(C+1))*C := by dsimp [C]; ring
  rw [he] at hh
  apply hh.trans_lt
  have ht : C/(C+1)<1 := (div_lt_one (by linarith : 0<C+1)).mpr (by linarith)
  have hm := mul_lt_mul_of_pos_left ht hε
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,mul_one] using hm

/-- Compactness of fixed-subspace normalized gauges. All constants arise
from the actual cosine norm and objective, not regularity assumptions. -/
theorem normalized_subsequence {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hV : V≠⊥)
    (hq : ∀ x∈V,x≠0 → 0<cosineSeminorm μ hμ x)
    (b : Bool) (g : ℕ → RelativeGauge V) (hn : ∀ i,supportFunctional μ (g i).body=1)
    {M : ℝ} (hM : ∀ i,Spherical.objective b (g i).toSeminorm≤M) :
    ∃ f : RelativeGauge V, ∃ φ : ℕ → ℕ, StrictMono φ ∧ supportFunctional μ f.body=1 ∧
      TendstoUniformly (fun i (u : Sphere n) => g (φ i) u) (fun u => f u) atTop ∧
      Tendsto (fun i => Spherical.objective b (g (φ i)).toSeminorm) atTop
        (𝓝 (Spherical.objective b f.toSeminorm)) := by
  obtain ⟨c,hc,hcb⟩ := seminorm_positive_subspace_bound V hV (cosineSeminorm μ hμ) hq
  have hlo (i : ℕ) (x : Space n) : c*‖V.starProjection x‖≤g i x :=
    (hcb x).trans ((g i).normalized_lower hμ (hn i) x)
  obtain ⟨R,hR,hRb⟩ := Spherical.objective_coercive (n := n) b M
  have hhi (i : ℕ) (u : Sphere n) : g i u≤R := hRb _ ((g i).ne_zero hV) (hM i) u
  obtain ⟨q,φ,hφ,hu,hpoint⟩ := Spherical.bounded_seminorm_subsequence
    (R := ⟨R,hR.le⟩) (fun i => (g i).toSeminorm) hhi
  have hqp : ∀ x,q (V.starProjection x)=q x := by
    intro x
    apply tendsto_nhds_unique (hpoint (V.starProjection x))
    simpa only [(g _).projection] using hpoint x
  have hql (x : Space n) : c*‖V.starProjection x‖≤q x :=
    ge_of_tendsto (hpoint x) (Eventually.of_forall (fun i => hlo (φ i) x))
  let f : RelativeGauge V := ⟨q,hqp,⟨c,hc,hql⟩⟩
  have hf : supportFunctional μ f.body=1 := by
    have ht := functional_tendsto (f := f) hμ hc (fun i => hlo (φ i)) hql hu
    have hc1 : Tendsto (fun i => supportFunctional μ (g (φ i)).body) atTop (𝓝 (1:ℝ)) := by
      simp_rw [hn]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique ht hc1
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff V).mp hV
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx0]⟩
  have huV : (u:Space n)∈V := V.smul_mem _ hx
  have hlow (i : ℕ) : ∃ v : Sphere n,c≤g i v := by
    refine ⟨u,?_⟩
    have h := hlo i u
    rwa [V.starProjection_eq_self_iff.mpr huV,Spherical.norm_coe,mul_one] at h
  refine ⟨f,φ,hφ,hf,hu,?_⟩
  exact Spherical.objective_tendsto b hc (fun i => hlow (φ i)) (fun i => hhi (φ i))
    (f.ne_zero hV) (fun u => hpoint u)

end RelativeGauge
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.VariationalMinimizers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {V : Submodule ℝ (Space n)}

omit [NeZero n] in
lemma exists_normalized {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hV : V≠⊥)
    (hq : ∀ x∈V,x≠0 → 0<cosineSeminorm μ hμ x) :
    ∃ g : RelativeGauge V,supportFunctional μ g.body=1 := by
  let g := ball V
  have hp := g.functional_pos hV hμ hq
  refine ⟨g.scale _ hp,?_⟩
  rw [functional_scale g _ hp μ,inv_mul_cancel₀ hp.ne']

/-- The actual fixed-subspace variational minimizer, including singular V. -/
theorem exists_minimizer {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hV : V≠⊥)
    (hq : ∀ x∈V,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) :
    ∃ g : RelativeGauge V,supportFunctional μ g.body=1 ∧
      ∀ f : RelativeGauge V,supportFunctional μ f.body=1 →
        Spherical.objective b g.toSeminorm≤Spherical.objective b f.toSeminorm := by
  let S : Set ℝ := {r | ∃ g : RelativeGauge V,supportFunctional μ g.body=1 ∧ Spherical.objective b g.toSeminorm=r}
  obtain ⟨g₀,hg₀⟩ := exists_normalized hμ hV hq
  have hS : S.Nonempty := ⟨_,g₀,hg₀,rfl⟩
  let q := (cosineSeminorm μ hμ).comp V.starProjection.toLinearMap
  have hq0 : q≠0 := by
    obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff V).mp hV
    intro he
    have hp := hq x hx hx0
    have hz : q x=0 := by rw [he]; rfl
    change cosineSeminorm μ hμ (V.starProjection x)=0 at hz
    rw [V.starProjection_eq_self_iff.mpr hx] at hz
    linarith
  have hSb : BddBelow S := by
    refine ⟨Spherical.objective b q,?_⟩
    rintro _ ⟨g,hg,rfl⟩
    exact Spherical.objective_mono b hq0 (g.ne_zero hV) (g.normalized_lower hμ hg)
  obtain ⟨r,hr,ht,hm⟩ := exists_seq_tendsto_sInf hS hSb
  choose g hgn hgr using hm
  obtain ⟨f,φ,hφ,hfn,hu,hfo⟩ := normalized_subsequence hμ hV hq b g hgn
    (M := r 0) (fun i => by rw [hgr i]; exact hr (Nat.zero_le i))
  have he : Spherical.objective b f.toSeminorm=sInf S := by
    apply tendsto_nhds_unique hfo
    have hh := ht.comp hφ.tendsto_atTop
    simpa only [Function.comp_def,← hgr] using hh
  refine ⟨f,hfn,fun g hg => ?_⟩
  rw [he]
  exact csInf_le hSb ⟨g,hg,rfl⟩

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

def midBody (g f : RelativeGauge V) : Set (Space n) := (1/2:ℝ) • (g.body+f.body)
lemma midBody_compact (g f : RelativeGauge V) : IsCompact (midBody g f) :=
  (g.compact.add f.compact).smul _
lemma midBody_convex (g f : RelativeGauge V) : Convex ℝ (midBody g f) :=
  (g.convex.add f.convex).smul _
lemma midBody_balanced (g f : RelativeGauge V) : Balanced ℝ (midBody g f) :=
  (g.balanced.add f.balanced).smul _
lemma midBody_inner (g f : RelativeGauge V) :
    ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈midBody g f := by
  obtain ⟨r,hr,hin⟩ := g.inner_ball
  refine ⟨r/2,by positivity,fun x hx hh => ?_⟩
  refine ⟨(2:ℝ) • x,⟨(2:ℝ) • x,hin _ (V.smul_mem _ hx) ?_,0,f.zero_mem,by simp⟩,by simp [smul_smul]⟩
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
  linarith

def midpoint (g f : RelativeGauge V) : RelativeGauge V :=
  ofBody (midBody_compact g f) (midBody_convex g f) (midBody_balanced g f) (midBody_inner g f)

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere sigma objective objectiveIntegrand objective_integrable)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {V : Submodule ℝ (Space n)}

omit [NeZero n] in
@[ext] lemma ext {g f : RelativeGauge V} (h : g.toSeminorm=f.toSeminorm) : g=f := by
  cases g; cases f; cases h; rfl

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere)

namespace RelativeGauge
variable {n : ℕ}

lemma top_body (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) : g.body=seminormUnit g.toSeminorm := by
  ext x; simp [body]
lemma top_nhds (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) : g.body∈𝓝 (0:Space n) := by
  rw [g.top_body]; exact seminormUnit_nhds _
lemma full_inner {K : Set (Space n)} (h0 : K∈𝓝 (0:Space n)) :
    ∃ r : ℝ,0<r ∧ ∀ x∈(⊤ : Submodule ℝ (Space n)),‖x‖≤r → x∈K := by
  obtain ⟨r,hr,hin⟩ := Metric.mem_nhds_iff.mp h0
  refine ⟨r/2,by positivity,fun x _ hx => hin ?_⟩
  rw [mem_ball,dist_zero_right]; linarith

def ofFullBody {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hb : Balanced ℝ K) (h0 : K∈𝓝 (0:Space n)) : RelativeGauge (⊤ : Submodule ℝ (Space n)) :=
  ofBody hK hc hb (full_inner h0)

end RelativeGauge

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.VariationalRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe mean sigma)

lemma normalizedVolume_pos {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) : 0 < normalizedVolume K :=
  div_pos (volumeRoot_pos hK hi) (Real.rpow_pos_of_pos (kappa_pos n) _)

namespace RelativeGauge
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma top_interior (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) : (interior g.body).Nonempty :=
  ⟨0,mem_interior_iff_mem_nhds.mpr g.top_nhds⟩

def volumeNormalize (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    RelativeGauge (⊤ : Submodule ℝ (Space n)) :=
  g.scale (normalizedVolume g.body) (normalizedVolume_pos g.compact g.top_interior)

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeField gaugeMoment)

def regime (n : ℕ) : Bool := decide (n=4)
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.FixedPointCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX uι uα

noncomputable section
open Set MeasureTheory Polynomial
open scoped BigOperators
namespace PettyProjection.FixedPoint

variable {X : Type uX} [TopologicalSpace X]

def ContinuousCoeffs (p : X → Polynomial ℝ) : Prop :=
  ∀ k, Continuous (fun x => (p x).coeff k)

lemma continuousCoeffs_const (p : Polynomial ℝ) : ContinuousCoeffs (fun _ : X => p) :=
  fun _ => continuous_const

lemma ContinuousCoeffs.mul {p q : X → Polynomial ℝ}
    (hp : ContinuousCoeffs p) (hq : ContinuousCoeffs q) :
    ContinuousCoeffs (fun x => p x * q x) := by
  intro k
  simp only [coeff_mul]
  exact continuous_finsetSum _ (fun ij _ => (hp ij.1).mul (hq ij.2))

lemma ContinuousCoeffs.sum {ι : Type uι} (s : Finset ι) {p : ι → X → Polynomial ℝ}
    (hp : ∀ i ∈ s, ContinuousCoeffs (p i)) :
    ContinuousCoeffs (fun x => ∑ i ∈ s, p i x) := by
  intro k
  simp only [finsetSum_coeff]
  exact continuous_finsetSum _ (fun i hi => hp i hi k)

lemma ContinuousCoeffs.prod {ι : Type uι} (s : Finset ι) {p : ι → X → Polynomial ℝ}
    (hp : ∀ i ∈ s, ContinuousCoeffs (p i)) :
    ContinuousCoeffs (fun x => ∏ i ∈ s, p i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousCoeffs_const (X := X) (1 : Polynomial ℝ)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hp i (Finset.mem_insert_self _ _)).mul
        (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

lemma ContinuousCoeffs.det {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {p : X → Matrix ι ι (Polynomial ℝ)}
    (hp : ∀ i j, ContinuousCoeffs (fun x => p x i j)) :
    ContinuousCoeffs (fun x => (p x).det) := by
  classical
  simp only [Matrix.det_apply]
  apply ContinuousCoeffs.sum
  intro e _
  have hprod := ContinuousCoeffs.prod Finset.univ (fun i _ => hp (e i) i)
  intro k
  simp only [coeff_smul]
  exact continuous_smul.comp (continuous_const.prodMk (hprod k))

/-- Integrating a uniformly bounded-degree polynomial coefficient by coefficient. -/
def integralPolynomial {α : Type uα} [MeasurableSpace α] (μ : Measure α)
    (p : α → Polynomial ℝ) (d : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (d+1), Polynomial.C (∫ x, (p x).coeff k ∂μ) * Polynomial.X^k

end PettyProjection.FixedPoint
end

noncomputable section
open Set Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.FixedPoint

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine nearest point; no fixed-point principle is used here. -/
def nearest (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hc : Convex ℝ K) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hcomplete hc x)

variable [CompleteSpace E]

def ballNearest (x : E) : E := nearest (closedBall (0:E) 1)
  (nonempty_closedBall.mpr (by norm_num)) isClosed_closedBall.isComplete (convex_closedBall _ _) x

end PettyProjection.FixedPoint
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.GaussianMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

/-- The actual one-dimensional radial Gaussian moment. -/
def gaussianRadial (d : ℕ) : ℝ := ∫ r in Ioi (0:ℝ),r^d*Real.exp (-(r^2))

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
variable {n : ℕ}

lemma norm_integrable_map {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (A : Space n →L[ℝ] Space n) :
    Integrable (fun x : Space n => ‖x‖) (μ.map A) := by
  apply (integrable_map_measure continuous_norm.aestronglyMeasurable A.continuous.measurable.aemeasurable).mpr
  exact (hμ.const_mul ‖A‖).mono' (continuous_norm.comp A.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Function.comp_apply,Real.norm_eq_abs,abs_norm] using A.le_opNorm x))

lemma cosine_map (μ : Measure (Space n)) (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (A : Space n →L[ℝ] Space n) (x : Space n) :
    cosineSeminorm (μ.map A) (norm_integrable_map hμ A) x=cosineSeminorm μ hμ (A.adjoint x) := by
  change (∫ y,|⟪y,x⟫| ∂μ.map A)=∫ y,|⟪y,A.adjoint x⟫| ∂μ
  rw [integral_map A.continuous.measurable.aemeasurable (by fun_prop)]
  congr 1
  funext y
  rw [ContinuousLinearMap.adjoint_inner_right]

lemma adjoint_ne_zero_on_range (A : Space n →L[ℝ] Space n) {x : Space n}
    (hx : x∈LinearMap.range A.toLinearMap) (hx0 : x≠0) : A.adjoint x≠0 := by
  intro h
  obtain ⟨y,rfl⟩ := hx
  change A.adjoint (A y)=0 at h
  change A y≠0 at hx0
  have hh := ContinuousLinearMap.adjoint_inner_right A y (A y)
  rw [h,inner_zero_right,real_inner_self_eq_norm_sq] at hh
  exact hx0 (norm_eq_zero.mp (by nlinarith [norm_nonneg (A y)]))

lemma cosine_map_pos {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x)
    (A : Space n →L[ℝ] Space n) (x : Space n)
    (hx : x∈LinearMap.range A.toLinearMap) (hx0 : x≠0) :
    0<cosineSeminorm (μ.map A) (norm_integrable_map hμ A) x := by
  rw [cosine_map]
  exact hq _ (adjoint_ne_zero_on_range A hx hx0)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (seminorm_continuous)
variable {n : ℕ}

def projectedUnit (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n)) : Set (Space n) :=
  closure (V.starProjection '' seminormUnit g)

lemma projectedUnit_convex (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n)) :
    Convex ℝ (projectedUnit V g) := (seminormUnit_convex g).linear_image V.starProjection.toLinearMap |>.closure

lemma projectedUnit_balanced (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n)) :
    Balanced ℝ (projectedUnit V g) := by
  apply Balanced.closure
  intro a ha y hy
  obtain ⟨z,⟨w,hw,rfl⟩,rfl⟩ := hy
  refine ⟨a • w,(seminormUnit_balanced g) a ha ⟨w,hw,rfl⟩,?_⟩
  exact map_smul V.starProjection a w

lemma projectedUnit_inner (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n)) :
    ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈projectedUnit V g := by
  obtain ⟨r,hr,hin⟩ := Metric.mem_nhds_iff.mp (seminormUnit_nhds g)
  refine ⟨r/2,by positivity,fun x hx hn => subset_closure ⟨x,hin ?_,?_⟩⟩
  · rw [mem_ball,dist_zero_right]; linarith
  · exact V.starProjection_eq_self_iff.mpr hx

lemma projectedUnit_compact (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n))
    {c : ℝ} (hc : 0<c) (hl : ∀ x,c*‖V.starProjection x‖≤g x) :
    IsCompact (projectedUnit V g) := by
  apply (isCompact_closedBall (0:Space n) c⁻¹).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  rintro _ ⟨x,hx,rfl⟩
  rw [mem_closedBall,dist_zero_right,inv_eq_one_div,le_div_iff₀ hc]
  change g x≤1 at hx
  nlinarith [hl x]

namespace RelativeGauge
variable {V : Submodule ℝ (Space n)}

def project (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n))
    {c : ℝ} (hc : 0<c) (hl : ∀ x,c*‖V.starProjection x‖≤g x) : RelativeGauge V :=
  ofBody (projectedUnit_compact V g hc hl) (projectedUnit_convex V g)
    (projectedUnit_balanced V g) (projectedUnit_inner V g)

end RelativeGauge
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.RankContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ}

lemma full_lower (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    ∃ c : ℝ,0< c ∧ ∀ x,c*‖x‖≤ f x := by
  obtain ⟨c,hc,hb⟩ := f.lower
  exact ⟨c,hc,fun x => by simpa only [Submodule.starProjection_top,ContinuousLinearMap.id_apply] using hb x⟩

def projectFull (V : Submodule ℝ (Space n))
    (f : RelativeGauge (⊤ : Submodule ℝ (Space n))) : RelativeGauge V :=
  project V f.toSeminorm f.full_lower.choose_spec.1 (fun x =>
    (mul_le_mul_of_nonneg_left (V.norm_starProjection_apply_le x) f.full_lower.choose_spec.1.le).trans
      (f.full_lower.choose_spec.2 x))

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

/-- A genuine full-dimensional approximation of an arbitrary relative gauge.
The sum regularization avoids any constant-rank assumption. -/
def thicken (g : RelativeGauge V) (ε : ℝ) (hε : 0<ε) :
    RelativeGauge (⊤ : Submodule ℝ (Space n)) where
  toSeminorm := Seminorm.of (fun x => g x+ε*‖x‖)
    (fun x y => by
      have hg := map_add_le_add g.toSeminorm x y
      have hn := mul_le_mul_of_nonneg_left (norm_add_le x y) hε.le
      linarith)
    (fun r x => by rw [map_smul_eq_mul,norm_smul]; ring)
  projection x := by simp only [Submodule.starProjection_top,ContinuousLinearMap.id_apply]
  lower := ⟨ε,hε,fun x => by
    change ε*‖(⊤ : Submodule ℝ (Space n)).starProjection x‖≤ g x+ε*‖x‖
    simp only [Submodule.starProjection_top,ContinuousLinearMap.id_apply]
    linarith [apply_nonneg g.toSeminorm x]⟩

end RelativeGauge
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.PositionMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere objective)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

abbrev NonzeroMap (n : ℕ) := {A : Space n →L[ℝ] Space n // LinearMap.range A.toLinearMap≠⊥}

def optimizer (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x) (b : Bool) (A : NonzeroMap n) :
    RelativeGauge (LinearMap.range A.val.toLinearMap) :=
  (exists_minimizer (norm_integrable_map hμ A) A.property (cosine_map_pos hμ hq A) b).choose

def optimizerSphere (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x) (b : Bool) (A : NonzeroMap n) :
    BoundedContinuousFunction (Sphere n) ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun u => optimizer hμ hq b A u,
    (Spherical.seminorm_continuous n _).comp continuous_subtype_val⟩

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
abbrev Mat (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)
variable {n : ℕ}
def matrix (A : Mat n) : Matrix (Fin n) (Fin n) ℝ := fun i j => A (i,j)
def op (A : Mat n) : Space n →L[ℝ] Space n := (matrix A).toEuclideanLin.toContinuousLinearMap
def tr (A : Mat n) : ℝ := ∑ i,A (i,i)
def quad (A : Mat n) (x : Space n) : ℝ := ⟪x,op A x⟫
def Symmetric (A : Mat n) : Prop := ∀ i j,A (i,j)=A (j,i)
def PSD (A : Mat n) : Prop := Symmetric A ∧ ∀ x,0≤quad A x
def domain (n : ℕ) : Set (Mat n) := {A | PSD A ∧ tr A=1}

lemma op_apply (A : Mat n) (x : Space n) (i : Fin n) : op A x i=∑ j,A (i,j)*x j := rfl
lemma quad_eq (A : Mat n) (x : Space n) : quad A x=∑ i,∑ j,A (i,j)*x i*x j := by
  simp only [quad,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,op_apply,Finset.sum_mul]
  congr 1; funext i
  apply Finset.sum_congr rfl
  intro j _; ring

lemma quad_basis (A : Mat n) (i : Fin n) : quad A (EuclideanSpace.single i 1)=A (i,i) := by
  simp [quad_eq]
lemma domain_range_ne_bot {A : Mat n} (hA : A∈domain n) : LinearMap.range (op A).toLinearMap≠⊥ := by
  intro h
  have hz : op A=0 := by
    apply ContinuousLinearMap.ext
    intro x
    exact (Submodule.mem_bot ℝ).mp (h ▸ LinearMap.mem_range_self _ x)
  have hdiag (i : Fin n) : A (i,i)=0 := by rw [← quad_basis,quad,hz]; simp
  have : tr A=0 := by simp [tr,hdiag]
  linarith [hA.2]
end PettyProjection.Position
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
open Spherical (Sphere mean sigma norm_coe continuous_integrable seminorm_continuous)
variable {n : ℕ} [NeZero n]

def momentField (g : Seminorm ℝ (Space n)) (k : ℕ) : Mat n :=
  WithLp.toLp 2 (fun ij => mean (fun u : Sphere n => g u^k*(u:Space n) ij.1*(u:Space n) ij.2)/
    mean (fun u : Sphere n => g u^k)-(if ij.1=ij.2 then 1 else 0)/(n:ℝ))

end PettyProjection.Position
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.AffinePosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeField gaugeMoment absolutePair)

/-- The genuine unpolarized cosine pairing of two (not necessarily even) measures. -/
def measurePair {n : ℕ} (μ ν : Measure (Space n)) : ℝ :=
  ∫ x,∫ y,|⟪x,y⟫| ∂ν ∂μ

def Represents {n : ℕ} (μ : Measure (Space n)) (g : Seminorm ℝ (Space n)) (k : ℕ) (s : ℝ) : Prop :=
  ∀ (φ : Space n → ℝ),Continuous φ → (∀ x,φ (-x)=φ x) →
    (∀ r : ℝ,0 < r → ∀ x,φ (r • x)=r*φ x) →
      (∫ x,φ x ∂μ)=s*mean (fun u : Sphere n => φ (gaugeField g k u))

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
open Spherical (Sphere mean seminorm_continuous)
open RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

abbrev Domain (n : ℕ) := {A : Mat n // A∈domain n}

def domainMap (A : Domain n) : NonzeroMap n := ⟨op A.val,domain_range_ne_bot A.property⟩

def positionField (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) (k : ℕ) (A : Domain n) : Mat n :=
  momentField (optimizer hμ hq b (domainMap A)).toSeminorm k

end PettyProjection.Position
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

def volumeFactor (T : Space n ≃L[ℝ] Space n) : ℝ := |LinearMap.det T.toLinearMap|^((n:ℝ)⁻¹)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection
namespace RelativeGauge
variable {n : ℕ} [NeZero n]

def IsMinimizer (μ : Measure (Space n)) (b : Bool) (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) : Prop :=
  supportFunctional μ g.body=1 ∧
    ∀ q : RelativeGauge (⊤ : Submodule ℝ (Space n)),supportFunctional μ q.body=1 →
      Spherical.objective b g.toSeminorm≤Spherical.objective b q.toSeminorm

end RelativeGauge
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.BilinearEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe seminorm_continuous)
variable {n : ℕ} [NeZero n] {K : Set (Space n)}

lemma gaugeMeasure_norm_integrable (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : K∈𝓝 (0:Space n)) : Integrable (fun x : Space n => ‖x‖) (gaugeProjectionMeasure K) := by
  let := gaugeMeasure_finite hK hc h0
  exact boundedMeasure_integrable_continuous (gaugeMeasure_bounded hc h0) continuous_norm

def projectionSeminorm (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) : Seminorm ℝ (Space n) := by
  let q := cosineSeminorm (gaugeProjectionMeasure K) (gaugeMeasure_norm_integrable hK hc h0)
  let c : ℝ := (n : ℝ)*kappa n/2
  have hc : 0 ≤ c := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (kappa_pos n).le) (by norm_num)
  exact Seminorm.of (fun x => c*q x)
    (fun x y => by
      simpa only [mul_add] using mul_le_mul_of_nonneg_left (map_add_le_add q x y) hc)
    (fun r x => by rw [map_smul_eq_mul];ring)

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

def normalizeBody (K : Set (Space n)) : Set (Space n) := (normalizedVolume K)⁻¹ • K

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.AffineCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma adjoint_inverse_comp (T : Space n ≃L[ℝ] Space n) :
    T.toContinuousLinearMap.adjoint.toLinearMap.comp T.symm.toContinuousLinearMap.adjoint.toLinearMap=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  change ⟪T.toContinuousLinearMap.adjoint (T.symm.toContinuousLinearMap.adjoint x),y⟫=⟪x,y⟫
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
  simp

/-- Invertibility of the transpose uses the transpose of the inverse. -/
def adjointEquiv (T : Space n ≃L[ℝ] Space n) : Space n ≃L[ℝ] Space n :=
  (LinearEquiv.ofLinearMap T.toContinuousLinearMap.adjoint.toLinearMap
    T.symm.toContinuousLinearMap.adjoint.toLinearMap
    (adjoint_inverse_comp T) (adjoint_inverse_comp T.symm)).toContinuousLinearEquiv

end PettyProjection
end

end OAI
end


