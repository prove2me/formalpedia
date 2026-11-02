-- Prove2me | Definitions.Def_OAIQ093D000
-- name    : OAIQ093D000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T15:59:40.975424+00:00
-- url     : https://prove2.me/theorems/212e7774-e426-4354-9ce2-649c61d4efde
-- title:
--   Definitions bundle OAIQ093D000 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 282 declarations of OpenAI's Lean: 92 definitions, 6 inductive types or structures, 40 instances and 144 theorems. The definitions and types are `Cx`, `Cx.coreC`, `Cx.fst`, `Cx.innerC`, `Cx.isometryProdL2`, `Cx.mapCLM`, `Cx.mapCLMHom`, `Cx.mapL`, `Cx.snd`, `Cx.toProdₗ`, `Cx.unitsMapHom`, `DerivedSets`, `FormalConjecturesCheck.CayleyBall`, `FormalConjecturesCheck.GrowthFunction`, `FormalConjecturesCheck.HasPolynomialGrowth`, `FormalConjecturesCheck.normGen`, `FreshInnerProduct`, `G'`, `Generates`, `GeneratesNS.B`, `GeneratesNS.B_3`, `GeneratesNS.B_c_r`, `GeneratesNS.B_finsets`, `GeneratesNS.B_half`, `GeneratesNS.B_half_finsets`, `GeneratesNS.B_r`, `GeneratesNS.C`, `GeneratesNS.ConstF`, `GeneratesNS.ConstLipschitzH`, `GeneratesNS.Conv`, `GeneratesNS.ConvExists`, `GeneratesNS.F_n`, `GeneratesNS.F_n_lp2`, `GeneratesNS.GoodScales`, `GeneratesNS.GoodScalesData`, `GeneratesNS.Harmonic`, `GeneratesNS.InterMult`, `GeneratesNS.InterMult_f`, `GeneratesNS.IsLipschitz`, `GeneratesNS.J` and 58 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `Complexification`, `Convolution`, `CriticalPercolation_Nilpotent_LowerCentralFG`, `CutoffInequality`, `Defs`, `Defs_Convolution`, `Defs_LipschitzH`, `Defs_Measure`, `Defs_WordMetric`, `FormalConjecturesCheck`, `Harmonic_Convolution`, `Harmonic_LaplaceLinear`, `Harmonic_MuConv`, `Harmonic_SelfAdjoint`, `Lemma326`, `LipschitzNorm`, `MatrixSubsum_Subsums`, `Packing`, `Poincare`, `PolycyclicRecognition_Algebra_HomogeneousWordCoefficients`, `QuadraticForm`, `TendstoNhdsMul`, `ToMathlib_LinearAlgebra_Matrix_Det`, `ToMathlib_LinearAlgebra_Matrix_PosDef`, `Unitary_Basic`, `Unitary_Packing`, `VWrapper`, `Vendor_Carleson_ToMathlib_MeasureTheory_Function_LpSeminorm_Basic`, `Vendor_Carleson_ToMathlib_MeasureTheory_Integral_MeanInequalities`, `Vendor_Carleson_ToMathlib_MeasureTheory_Measure_Haar_Unique`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D006`, `OAIQ093D007`, `OAIQ093D009` and `OAIQ093D011`; the statements `GeneratesNS.exists_theorem_3_1_input`, `GeneratesNS.growth_const_pos`, `GeneratesNS.growth_exponent_pos`, `GeneratesNS.theorem_3_1`, `GeneratesNS.three_two_S_n_generates`, `GeneratesNS.three_two_ker_fg`, `GeneratesNS.word_norm_list_prod_le`, `GeneratesNS.word_norm_pow`, `HnEpsData.central_trivial_virtually_abelian` and `volume_packing`; the proofs of `HnEpsData.central_trivial_virtually_abelian`, `compact_lie_virtually_abelian` and `volume_packing`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ093_PR.Complexification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Complexification of a real inner product space

This file builds the complexification `Cx V` of a real inner product space `V`, realised
concretely as pairs `(x, y)` thought of as `x + i y`.  It provides the complex module and
complex inner product space structure, the dimension formula
`finrank ℂ (Cx V) = finrank ℝ V`, and the complexification of a continuous real-linear map,
packaged as an injective monoid homomorphism on units.

`Cx V` is primarily a **complex** vector space; its real structure is the restriction of scalars
of the complex one (via `NormedSpace.complexToReal`), so the real normed/analysis instances agree
with the complex ones rather than forming a diamond.

This is the device that lets the Gromov development keep its Lipschitz harmonic functions
real-valued while still feeding the (irreducibly complex) compact-Lie / unitary-trick step:
the real representation is complexified here, just before the unitary machinery is invoked.
-/


open scoped ComplexConjugate

/-- The complexification of a real vector space `V`, realised as pairs `(x, y) ≃ x + i y`. -/
@[expose]
def Cx (V : Type*) := V × V

namespace Cx

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

instance instAddCommGroup : AddCommGroup (Cx V) := inferInstanceAs (AddCommGroup (V × V))

/-- Real part of an element of the complexification. -/
@[expose]
def fst (p : Cx V) : V := (p : V × V).1
/-- Imaginary part of an element of the complexification. -/
@[expose]
def snd (p : Cx V) : V := (p : V × V).2

omit [InnerProductSpace ℝ V] in
@[simp] lemma fst_mk (a b : V) : fst ((a, b) : Cx V) = a := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma snd_mk (a b : V) : snd ((a, b) : Cx V) = b := rfl
omit [InnerProductSpace ℝ V] in
@[ext] lemma ext {p q : Cx V} (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := Prod.ext h1 h2

omit [InnerProductSpace ℝ V] in
@[simp] lemma add_fst (p q : Cx V) : (p + q).fst = p.fst + q.fst := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma add_snd (p q : Cx V) : (p + q).snd = p.snd + q.snd := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma zero_fst : (0 : Cx V).fst = 0 := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma zero_snd : (0 : Cx V).snd = 0 := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma neg_fst (p : Cx V) : (-p).fst = -p.fst := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma neg_snd (p : Cx V) : (-p).snd = -p.snd := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma sub_fst (p q : Cx V) : (p - q).fst = p.fst - q.fst := rfl
omit [InnerProductSpace ℝ V] in
@[simp] lemma sub_snd (p q : Cx V) : (p - q).snd = p.snd - q.snd := rfl

/-- Complex scalar multiplication: `(a + b i) • (x + i y) = (a x - b y) + i (b x + a y)`. -/
noncomputable instance instSMulComplex : SMul ℂ (Cx V) where
  smul c p := (show V × V from (c.re • p.fst - c.im • p.snd, c.im • p.fst + c.re • p.snd))

@[simp] lemma csmul_fst (c : ℂ) (p : Cx V) : (c • p).fst = c.re • p.fst - c.im • p.snd := rfl
@[simp] lemma csmul_snd (c : ℂ) (p : Cx V) : (c • p).snd = c.im • p.fst + c.re • p.snd := rfl

noncomputable instance instModuleComplex : Module ℂ (Cx V) where
  one_smul p := by ext <;> simp
  mul_smul a b p := by ext <;> simp [Complex.mul_re, Complex.mul_im] <;> module
  smul_zero c := by ext <;> simp
  smul_add c p q := by ext <;> simp <;> module
  add_smul a b p := by ext <;> simp [Complex.add_re, Complex.add_im] <;> module
  zero_smul p := by ext <;> simp

/-- The Hermitian form on the complexification, conjugate-linear in the first argument. -/
@[expose]
noncomputable def innerC (u v : Cx V) : ℂ :=
  ((inner ℝ u.fst v.fst + inner ℝ u.snd v.snd : ℝ) : ℂ)
    + Complex.I * (((inner ℝ u.fst v.snd - inner ℝ u.snd v.fst : ℝ) : ℂ))

lemma innerC_self_re (u : Cx V) :
    (innerC u u).re = inner ℝ u.fst u.fst + inner ℝ u.snd u.snd := by
  simp only [innerC, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

/-- The inner product space core on the complexification. -/
@[expose]
noncomputable def coreC : InnerProductSpace.Core ℂ (Cx V) where
  inner := innerC
  conj_inner_symm u v := by unfold innerC; simp [Complex.ext_iff, real_inner_comm]
  re_inner_nonneg u := by
    show 0 ≤ (innerC u u).re
    rw [innerC_self_re]; exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left u v w := by unfold innerC; simp [inner_add_left] <;> ring
  smul_left c u v := by
    unfold innerC
    simp only [csmul_fst, csmul_snd, inner_sub_left, inner_add_left, real_inner_smul_left]
    push_cast
    simp [Complex.ext_iff]
    constructor <;> ring
  definite u h := by
    have hre := congrArg Complex.re h
    rw [innerC_self_re] at hre
    simp only [Complex.zero_re] at hre
    have a := real_inner_self_nonneg (x := u.fst)
    have b := real_inner_self_nonneg (x := u.snd)
    have h1 : inner ℝ u.fst u.fst = 0 := le_antisymm (by linarith) a
    have h2 : inner ℝ u.snd u.snd = 0 := le_antisymm (by linarith) b
    ext
    · exact inner_self_eq_zero.mp h1
    · exact inner_self_eq_zero.mp h2

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (Cx V) := coreC.toNormedAddCommGroup
noncomputable instance instInnerProductSpaceComplex : InnerProductSpace ℂ (Cx V) := InnerProductSpace.ofCore coreC.toCore

/-!
### Completeness

`Cx V` carries the `L²` norm of its two components, so it is isometric to `V × V` with the `L²`
norm and inherits completeness from `V`.  This is what makes `Cx V →L[ℂ] Cx V` a C⋆-algebra, and
hence what makes Mathlib's continuous functional calculus (`cfc`) available on complexified
operators: the `ContinuousFunctionalCalculus ℝ _ IsSelfAdjoint` instance is derived from the
complex one, so it is not available on `V →L[ℝ] V` itself.
-/

@[simp] lemma norm_sq_eq (p : Cx V) : ‖p‖ ^ 2 = ‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  show (innerC p p).re = _
  rw [innerC_self_re, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

lemma norm_eq (p : Cx V) : ‖p‖ = Real.sqrt (‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2) := by
  rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg p)]

/-- The complexification is isometric to `V × V` carrying the `L²` norm. -/
@[expose]
noncomputable def isometryProdL2 : Cx V ≃ᵢ WithLp 2 (V × V) where
  toFun p := WithLp.toLp 2 ((p.fst, p.snd) : V × V)
  invFun q := ((WithLp.ofLp q).1, (WithLp.ofLp q).2)
  left_inv _ := rfl
  right_inv _ := rfl
  isometry_toFun := by
    refine Isometry.of_dist_eq fun p q => ?_
    rw [dist_eq_norm, dist_eq_norm, WithLp.prod_norm_eq_of_L2, norm_eq]
    rfl

@[expose]
instance instCompleteSpace [CompleteSpace V] : CompleteSpace (Cx V) := isometryProdL2.completeSpace

/-!
### Real structure

The real module / normed structure is the restriction of scalars of the complex one, supplied by
`NormedSpace.complexToReal`.  The real scalar action is `r • p = (r : ℂ) • p`, componentwise.
-/

@[expose]
instance instIsScalarTowerRealComplex : IsScalarTower ℝ ℂ (Cx V) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

lemma rsmul_eq (r : ℝ) (p : Cx V) : r • p = (r : ℂ) • p := by
  rw [← algebraMap_smul ℂ r p, Complex.coe_algebraMap]

@[simp] lemma rsmul_fst (r : ℝ) (p : Cx V) : (r • p).fst = r • p.fst := by
  rw [rsmul_eq]
  simp only [csmul_fst, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
@[simp] lemma rsmul_snd (r : ℝ) (p : Cx V) : (r • p).snd = r • p.snd := by
  rw [rsmul_eq]
  simp only [csmul_snd, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]

/-- The complexification, as an `ℝ`-linear space, is `V × V`. -/
@[expose]
def toProdₗ : Cx V ≃ₗ[ℝ] V × V where
  toFun p := (p.fst, p.snd)
  map_add' p q := by simp
  map_smul' r p := by ext <;> simp
  invFun q := ((q.1, q.2) : Cx V)
  left_inv p := by ext <;> rfl
  right_inv q := by ext <;> rfl

@[expose]
instance instFiniteDimensionalReal [FiniteDimensional ℝ V] : FiniteDimensional ℝ (Cx V) :=
  toProdₗ.symm.finiteDimensional

@[expose]
instance instFiniteDimensionalComplexOfReal [FiniteDimensional ℝ V] : FiniteDimensional ℂ (Cx V) :=
  Module.Finite.of_restrictScalars_finite ℝ ℂ (Cx V)

@[simp] lemma finrank_eq [FiniteDimensional ℝ V] :
    Module.finrank ℂ (Cx V) = Module.finrank ℝ V := by
  have hreal : Module.finrank ℝ (Cx V) = 2 * Module.finrank ℝ V := by
    rw [toProdₗ.finrank_eq, Module.finrank_prod]; ring
  have htower : Module.finrank ℝ ℂ * Module.finrank ℂ (Cx V) = Module.finrank ℝ (Cx V) :=
    Module.finrank_mul_finrank ℝ ℂ (Cx V)
  have h2 : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  rw [h2] at htower
  omega

/-! ### Complexification of a real-linear map -/

/-- Complexification of a continuous real-linear map as a `ℂ`-linear map, acting componentwise
on `(x, y) ≃ x + i y`. -/
@[expose]
noncomputable def mapL (f : V →L[ℝ] V) : Cx V →ₗ[ℂ] Cx V where
  toFun p := (show V × V from (f p.fst, f p.snd))
  map_add' p q := by ext <;> simp [map_add] <;> rfl
  map_smul' c p := by ext <;> simp [map_sub, map_add, map_smul] <;> rfl

@[simp] lemma mapL_fst (f : V →L[ℝ] V) (p : Cx V) : (mapL f p).fst = f p.fst := rfl
@[simp] lemma mapL_snd (f : V →L[ℝ] V) (p : Cx V) : (mapL f p).snd = f p.snd := rfl


@[simp] lemma mapL_id : mapL (ContinuousLinearMap.id ℝ V) = LinearMap.id := by
  ext p <;> simp

lemma norm_mapL_le (f : V →L[ℝ] V) (p : Cx V) : ‖mapL f p‖ ≤ ‖f‖ * ‖p‖ := by
  have h1 : ‖f p.fst‖ ^ 2 + ‖f p.snd‖ ^ 2 ≤ (‖f‖ * ‖p‖) ^ 2 := by
    have s1 : ‖f p.fst‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖p.fst‖ ^ 2 := by
      have h := f.le_opNorm p.fst
      have := norm_nonneg (f p.fst)
      nlinarith
    have s2 : ‖f p.snd‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖p.snd‖ ^ 2 := by
      have h := f.le_opNorm p.snd
      have := norm_nonneg (f p.snd)
      nlinarith
    rw [mul_pow, norm_sq_eq p]
    linarith
  calc ‖mapL f p‖ = Real.sqrt (‖f p.fst‖ ^ 2 + ‖f p.snd‖ ^ 2) := by rw [norm_eq]; rfl
    _ ≤ Real.sqrt ((‖f‖ * ‖p‖) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ‖f‖ * ‖p‖ := Real.sqrt_sq (by positivity)

/-- Complexification of a continuous real-linear map as a continuous `ℂ`-linear map. -/
@[expose]
noncomputable def mapCLM (f : V →L[ℝ] V) : Cx V →L[ℂ] Cx V :=
  (mapL f).mkContinuous ‖f‖ (norm_mapL_le f)

@[simp] lemma mapCLM_apply (f : V →L[ℝ] V) (p : Cx V) : mapCLM f p = mapL f p := rfl

lemma mapCLM_sub (f g : V →L[ℝ] V) : mapCLM f - mapCLM g = mapCLM (f - g) := by
  ext p <;> rfl

/-- Complexification as a monoid homomorphism on endomorphisms (composition ↦ composition). -/
@[expose]
noncomputable def mapCLMHom : (V →L[ℝ] V) →* (Cx V →L[ℂ] Cx V) where
  toFun := mapCLM
  map_one' := by ext p <;> simp
  map_mul' f g := by ext p <;> simp

/-- Complexification as an injective group homomorphism on units. -/
@[expose]
noncomputable def unitsMapHom : (V →L[ℝ] V)ˣ →* (Cx V →L[ℂ] Cx V)ˣ := Units.map mapCLMHom

/-!
### Self-adjointness

The complexification of a self-adjoint operator is self-adjoint.  Together with the
`CompleteSpace (Cx V)` instance above, this is what lets `cfc f (mapCLM Δ) (p := IsSelfAdjoint)`
elaborate *and* lets the `cfc` API lemmas discharge their `IsSelfAdjoint` side conditions.
-/

lemma isSymmetric_mapCLM [CompleteSpace V] {f : V →L[ℝ] V} (hf : IsSelfAdjoint f) :
    (mapCLM f : Cx V →ₗ[ℂ] Cx V).IsSymmetric := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hf
  have hs' : ∀ a b : V, inner ℝ (f a) b = inner ℝ a (f b) := fun a b => hs a b
  intro u v
  show innerC (mapL f u) v = innerC u (mapL f v)
  simp only [innerC, mapL_fst, mapL_snd, hs']

lemma isSelfAdjoint_mapCLM [CompleteSpace V] {f : V →L[ℝ] V} (hf : IsSelfAdjoint f) :
    IsSelfAdjoint (mapCLM f) := (isSymmetric_mapCLM hf).isSelfAdjoint

/-!
### Spectrum

Complexification preserves the spectrum *at real points*: `mapCLM f` is invertible exactly when
`f` is, because `mapCLM f` acts componentwise and so is bijective exactly when `f` is.

Note this is **not** the same as saying `spectrum ℂ (mapCLM f) = ((↑) '' spectrum ℝ f)`, which is
false in general: rotation by a quarter turn on `ℝ²` has empty real spectrum but complex spectrum
`{I, -I}`.  Only the real points of `spectrum ℂ (mapCLM f)` correspond to `spectrum ℝ f`; see
`ofReal_mem_spectrum_mapCLM_iff`.  For a self-adjoint `f` the complex spectrum is real anyway, so
in that case nothing is lost.
-/

@[simp] lemma mapCLM_one : mapCLM (1 : V →L[ℝ] V) = 1 := by ext p <;> rfl

lemma mapCLM_rsmul (r : ℝ) (f : V →L[ℝ] V) : mapCLM (r • f) = r • mapCLM f := by
  ext p <;> simp

lemma mapCLM_algebraMap (r : ℝ) :
    mapCLM (algebraMap ℝ (V →L[ℝ] V) r) = algebraMap ℝ (Cx V →L[ℂ] Cx V) r := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mapCLM_rsmul, mapCLM_one]

lemma bijective_mapCLM_iff (f : V →L[ℝ] V) :
    Function.Bijective (mapCLM f) ↔ Function.Bijective f := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun x x' h => ?_, fun y => ?_⟩
    · have : ((x, 0) : Cx V) = ((x', 0) : Cx V) := hinj (by ext; exacts [h, rfl])
      exact congrArg Cx.fst this
    · obtain ⟨p, hp⟩ := hsurj ((y, 0) : Cx V)
      exact ⟨p.fst, congrArg Cx.fst hp⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun p q h => ?_, fun q => ?_⟩
    · exact Cx.ext (hinj (congrArg Cx.fst h)) (hinj (congrArg Cx.snd h))
    · obtain ⟨a, ha⟩ := hsurj q.fst
      obtain ⟨b, hb⟩ := hsurj q.snd
      exact ⟨((a, b) : Cx V), by ext; exacts [ha, hb]⟩

lemma isUnit_mapCLM_iff [CompleteSpace V] (f : V →L[ℝ] V) : IsUnit (mapCLM f) ↔ IsUnit f := by
  rw [ContinuousLinearMap.isUnit_iff_bijective, ContinuousLinearMap.isUnit_iff_bijective,
    bijective_mapCLM_iff]

/-- Complexification preserves the real spectrum.  This is the form the continuous functional
calculus wants, since `cfc` over `ℝ` is stated in terms of `spectrum ℝ`. -/
lemma spectrum_mapCLM [CompleteSpace V] (f : V →L[ℝ] V) :
    spectrum ℝ (mapCLM f) = spectrum ℝ f := by
  ext r
  simp only [spectrum.mem_iff]
  rw [← mapCLM_algebraMap, mapCLM_sub, isUnit_mapCLM_iff]


end Cx
end

section
-- module Solutions.OAIQ093_PR.Defs_WordMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The `Generates` class and the word metric

The `Generates` class packaging a finitely generated group with a symmetric generating set, the
definition of polynomial growth, and the word norm / word metric on `G` with its `MetricSpace`
@[expose]
instance.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

-- Based on https://github.com/YaelDillies/LeanCamCombi/blob/b6312bee17293272af6bdcdb47b3ffe98fca46a4/LeanCamCombi/GrowthInGroups/Lecture1.lean#L41
-- and the Vikman paper
@[expose] def HasPolynomialGrowthD {G: Type*} [Group G] [DecidableEq G] (S: Finset G) (d: ℕ): Prop := ∃ a: ℕ, ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d
@[expose] def HasPolynomialGrowth  {G: Type*} [Group G] [DecidableEq G] (S: Finset G): Prop := ∃ d, HasPolynomialGrowthD S d


-- TODO - I don't really understand why `S` needs to be an `outParam`?
-- If I remove that, then the `PseudoMetricSpace G` starts erroring
-- See also:
-- * `set_option synthInstance.checkSynthOrder false`
class Generates where
  G: Type*
  g_group: Group G
  g_eq: DecidableEq G
  S: Finset G
  hS: Nonempty S
  generates : ((closure (S : Set G) : Set G) = ⊤)
  -- This should be fine, since the growth rate doesn't depend on the generating set
  one_mem: (1 : G) ∈ S
  has_inv: ∀ g ∈ S, g⁻¹ ∈ S
  g_infinite: Infinite G
  -- TODO - should this carry data and the actual value 'd'?
  g_growth: HasPolynomialGrowth S

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

instance G_group: Group G := hGS.g_group
instance G_dec_eq: DecidableEq G := hGS.g_eq


lemma s_union_sinv : S ∪ S⁻¹ = S := by
  ext a
  have foo := hGS.has_inv (a⁻¹)
  simp only [inv_inv] at foo
  simpa using foo

lemma S_eq_Sinv: S = S⁻¹ := by
  ext a
  refine ⟨?_, ?_⟩
  . intro ha
    have a_inv := hGS.has_inv a ha
    exact Finset.mem_inv'.mpr a_inv
  . intro ha
    simp at ha
    have a_inv := hGS.has_inv a⁻¹ ha
    simp only [inv_inv] at a_inv
    exact a_inv


lemma mem_closure (x: G): x ∈ closure (S : Set G) := by
  have hg := hGS.generates
  simp only [Set.top_eq_univ, coe_eq_univ] at hg
  simp [hg]

-- Predicate stating that an element of G equals a product of elements of S
@[expose] def ProdS (x: G) (l: List S): Prop := l.unattach.prod = x

-- Each element of G can be written as a product of elements of S in at least one way
lemma mem_S_prod_list (x: G): ∃ l: List S, ProdS x l := by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  simp only [mem_toSubmonoid, Finset.mem_coe] at foo
  specialize foo (mem_closure x)
  norm_cast at foo
  rw [s_union_sinv] at foo
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold ProdS
  unfold List.unattach
  simp [prod_eq]

@[expose]
noncomputable def WordNorm (g: G) := sInf {n: ℕ | ∃ l: List S, l.length = n ∧ ProdS g l}

lemma word_norm_prod (g: G) (n: ℕ) (hgn: WordNorm g = n): ∃ l: List S, ProdS g l ∧ l.length = n := by
  have foo := Nat.sInf_mem (s := {n: ℕ | ∃ l: List S, l.length = n ∧ ProdS g l})
  obtain ⟨l, hl⟩ := mem_S_prod_list  g
  unfold ProdS at hl
  rw [Set.nonempty_def] at foo
  specialize foo ⟨l.length, ⟨l, ⟨by simp, hl⟩⟩⟩
  simp only [Set.mem_setOf_eq] at foo
  obtain ⟨l, ⟨hl, hl_prod⟩⟩ := foo
  rw [← hgn]
  exact ⟨l, ⟨hl_prod, hl⟩⟩

lemma word_norm_prod_self (g: G): ∃ l: List S, ProdS g l ∧ l.length = WordNorm  g := by
  exact word_norm_prod  g (WordNorm  g) rfl

lemma word_norm_le (g: G) (l: List S) (hgl: ProdS g l): WordNorm  g ≤ l.length := by
  unfold WordNorm
  apply Nat.sInf_le
  use l

-- TODO - this probably needs to be swapped to make 'gAct' work
@[expose] noncomputable def WordDist (x y: G) := WordNorm  (y * x⁻¹)

lemma WordDist_self (x: G): WordDist  x x = 0 := by
  unfold WordDist
  rw [mul_inv_cancel]
  unfold WordNorm
  simp only [Nat.sInf_eq_zero, Set.mem_setOf_eq, List.length_eq_zero_iff, exists_eq_left]
  left
  rfl

lemma WordDist_swap_le (x y: G): WordDist  y x ≤ WordDist  x y := by
  unfold WordDist
  obtain ⟨l, l_prod, l_len⟩ := word_norm_prod (y * x⁻¹) (WordNorm (y * x⁻¹)) (rfl)
  unfold ProdS at l_prod
  apply_fun (fun x => x⁻¹) at l_prod
  rw [mul_inv_rev, inv_inv] at l_prod
  rw [List.prod_inv_reverse] at l_prod

  have commute_unattach: List.map (Inv.inv) l.unattach = (l.map (fun x => ⟨x.val⁻¹, hGS.has_inv x.val x.property⟩)).unattach := by
    apply List.ext_getElem?
    intro i
    simp


  rw [commute_unattach, ← List.unattach_reverse] at l_prod
  have prod_le := word_norm_le  (x * y⁻¹) _ l_prod
  conv at prod_le =>
    rhs
    equals l.length =>
      simp
  rw [l_len] at prod_le
  exact prod_le

lemma WordDist_comm (x y: G): WordDist  x y = WordDist  y x := by
  have le_left := WordDist_swap_le  x y
  have le_right := WordDist_swap_le  y x
  exact Nat.le_antisymm le_right le_left

lemma WordDist_triangle (x y z: G): WordDist  x z ≤ WordDist  x y + WordDist  y z := by

  unfold WordDist
  obtain ⟨l_x_y, x_y_prod, x_y_len⟩ := word_norm_prod_self  (y * x⁻¹)
  obtain ⟨l_y_z, y_z_prod, y_z_len⟩ := word_norm_prod_self  (z * y⁻¹)
  unfold ProdS at x_y_prod
  unfold ProdS at y_z_prod

  have prod_append: ProdS  (z * x⁻¹) (l_y_z ++ l_x_y) := by
    unfold ProdS
    simp
    rw [x_y_prod, y_z_prod]
    rw [← mul_assoc]
    simp

  have le_append := word_norm_le  (z * x⁻¹) _ prod_append
  rw [List.length_append] at le_append
  rw [x_y_len, y_z_len] at le_append
  rw [add_comm] at le_append
  exact le_append

-- TODO - I'm not certain that these are actually the correct instances for the proof


noncomputable instance WordDist.instPseudoMetricSpace: PseudoMetricSpace G where
  dist x y := WordDist  x y
  dist_self x := by
    norm_cast
    exact WordDist_self  x
  dist_comm x y := by
    norm_cast
    exact WordDist_comm  x y
  dist_triangle x y z := by
    norm_cast
    exact WordDist_triangle  x y z

lemma word_norm_eq_zero {x y: G} (hdist: WordDist x y = 0): x = y := by
  simp [WordDist, WordNorm] at hdist
  match hdist with
  | .inl empty_prod =>
    unfold ProdS at empty_prod
    simp only [List.unattach_nil, List.prod_nil] at empty_prod
    apply_fun (fun y => y * x) at empty_prod
    simpa using empty_prod
  | .inr empty_set =>
    obtain ⟨l, hl⟩ := mem_S_prod_list  (y * x⁻¹)
    unfold ProdS at hl
    have len_in_set: l.unattach.length ∈ (∅ : Set ℕ) := by
      rw [← empty_set]
      simp only [List.length_unattach, Set.mem_setOf_eq]
      use l
      refine ⟨rfl, hl⟩
    simp only [Set.mem_empty_iff_false] at len_in_set

noncomputable instance WordDist.instMetricSpace: MetricSpace G where
  eq_of_dist_eq_zero := by
    intro x y hdist
    apply word_norm_eq_zero
    simp [dist] at hdist
    exact hdist

-- TODO - is there an easier way to transfer all of the theorems/instances from `G` to `Additive G`?


lemma word_norm_inv_le (x: G): WordNorm x ≤ WordNorm x⁻¹ := by
  simp [WordNorm]
  apply csInf_le'
  simp
  obtain ⟨lx, x_prod, x_len⟩ := word_norm_prod_self x⁻¹
  use (lx.map (fun (x: S) => ⟨x.val⁻¹, by (
      rw [← Finset.mem_inv']
      rw [← S_eq_Sinv]
      simp
    )⟩)).reverse
  refine ⟨?_, ?_⟩
  .
    simp
    exact x_len
  .
    simp [ProdS]

    clear x_len

    induction lx generalizing x with
    | nil =>
      simp
      simp [ProdS] at x_prod
      grind
    | cons head tail ih =>
      simp
      simp [ProdS] at x_prod
      simp [ProdS] at ih
      rw [ih (x := tail.unattach.prod⁻¹)]
      .
        rw[← inv_eq_iff_eq_inv] at x_prod
        simp [← x_prod]
      . simp


lemma word_norm_inv (x: G): WordNorm x = WordNorm x⁻¹ := by
  apply Nat.le_antisymm
  . apply word_norm_inv_le
  .
    conv =>
      rhs
      equals WordNorm x⁻¹⁻¹ => simp
    apply word_norm_inv_le


lemma WordDist_one (x: G): WordDist x 1 = WordNorm x := by
  simp [WordDist]
  rw [← word_norm_inv]

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Defs_Measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Topology, measurability and Haar measure on `G`

`G` is discrete, so its Haar measure is the counting measure. This file records the Borel and
measure-space instances and the resulting a.e.-triviality lemmas.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

noncomputable instance WordDist.instMeasurableSpace: MeasurableSpace G := borel G

noncomputable instance WordDist.instMeasureableSpaceOpp: MeasurableSpace (Additive G) := borel (Additive G)

@[expose]
noncomputable instance WordDist.instBorelSpace: BorelSpace G where
  measurable_eq := rfl


@[expose]
noncomputable instance WordDist.instBorelSpaceAddOpp: BorelSpace (Additive G) where
  measurable_eq := rfl

-- TODO - are we really supposed to be using a metric topology if it turns out to be the discrete topology?
lemma singleton_open (x: G): IsOpen {x} := by
  rw [Metric.isOpen_singleton_iff]
  use 1
  simp only [gt_iff_lt, zero_lt_one, true_and]
  intro y hy
  simp [dist] at hy
  have dist_zero := dist_eq_zero (x := y) (y := x)
  simp [dist] at dist_zero
  rw [dist_zero] at hy
  exact hy

@[expose]
instance discreteTopology: DiscreteTopology G := by
  rw [discreteTopology_iff_isOpen_singleton]
  exact singleton_open

@[expose]
instance instContinuousMulG : ContinuousMul G where
  continuous_mul := continuous_of_discreteTopology

@[expose]
instance instContinuousInvG : ContinuousInv G where
  continuous_inv := continuous_of_discreteTopology

@[expose]
instance instIsTopologicalGroupG: IsTopologicalGroup G where
  continuous_mul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology


-- Define Haar measure so that singleton sets have measure 1 -
-- I think this is what we want in order to be able to nicely convert integrals to sums
@[expose]
noncomputable def haarSingleton: TopologicalSpace.PositiveCompacts G := {
  carrier := {1}
  isCompact' := by
    simp
  interior_nonempty' := by
    have one_mem: (1 : G) ∈ interior {1} := by
      rw [mem_interior]
      use {1}
      simp
    apply Set.nonempty_def.mpr
    exact ⟨1, one_mem⟩
}

lemma mul_singleton_carrier: (haarSingleton.carrier) = ({1} : (Set G)) := by
  unfold haarSingleton
  rfl

noncomputable abbrev myHaar := MeasureTheory.Measure.haarMeasure haarSingleton

noncomputable instance WordDist.measureSpace: MeasureTheory.MeasureSpace G := {
  volume := myHaar
}

@[expose]
noncomputable def addHaarSingleton: TopologicalSpace.PositiveCompacts (Additive G) := {
  carrier := {0}
  isCompact' := by
    simp
  interior_nonempty' := by
    have zero_mem: (0 : Additive G) ∈ interior {0} := by
      rw [mem_interior]
      use {0}
      simp
    apply Set.nonempty_def.mpr
    exact ⟨0, zero_mem⟩
}

lemma singleton_carrier: (addHaarSingleton.carrier) = ({0} : (Set (Additive G))) := by
  unfold addHaarSingleton
  rfl

noncomputable abbrev myHaarAddOpp := MeasureTheory.Measure.addHaarMeasure (G := Additive G) addHaarSingleton


@[expose]
instance countable_G: Countable G := by
  apply Function.Surjective.countable (f := fun (x: List S) => x.unattach.prod)
  intro g
  obtain ⟨l, hl⟩ := mem_S_prod_list  g
  use l
  simp only
  unfold ProdS at hl
  rw [hl]


-- TODO - use the fact that G is finitely generated
@[expose]
instance countable_add_G: Countable (Additive G) := by
  exact inferInstanceAs (Countable G)


omit hGS in
lemma singleton_pairwise_disjoint {T: Type*} (s: Set (T)) : s.PairwiseDisjoint Set.singleton := by
  refine Set.pairwiseDisjoint_iff.mpr ?_
  intro a ha b hb hab
  unfold Set.singleton at hab
  simp at hab
  exact hab.symm


-- Use the fact that we have the discrete topology
set_option maxHeartbeats 500000 in
lemma my_add_haar_eq_count: (myHaarAddOpp) = MeasureTheory.Measure.count := by
  ext s hs
  by_cases s_finite: Set.Finite s
  .
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.Measure.count_apply_finite s s_finite]
    rw [MeasureTheory.measure_biUnion]
    .
      -- TODO - extract 'measure {a} = 1' to a lemma
      simp_rw [MeasureTheory.Measure.addHaar_singleton]
      unfold myHaarAddOpp
      simp_rw [← singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.addHaarMeasure_self]
      rw [ENNReal.tsum_set_const]
      simp
      norm_cast
      rw [Set.Finite.encard_eq_coe_toFinset_card s_finite]
    . exact Set.Finite.countable s_finite
    .
      apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp
  .
    have s_infinite: s.Infinite := by
      exact s_finite
    rw [MeasureTheory.Measure.count_apply_infinite s_infinite]
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.measure_biUnion]
    .
      simp_rw [MeasureTheory.Measure.addHaar_singleton]
      unfold myHaarAddOpp
      simp_rw [← singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.addHaarMeasure_self]
      simp only [ENNReal.tsum_one, ENat.toENNReal_eq_top, ENat.card_eq_top]
      exact Set.infinite_coe_iff.mpr s_finite
    . exact Set.to_countable s
    . apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp

lemma my_haar_eq_count: (myHaar) = MeasureTheory.Measure.count := by
  ext s hs
  by_cases s_finite: Set.Finite s
  .
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.Measure.count_apply_finite s s_finite]
    rw [MeasureTheory.measure_biUnion]
    .
      -- TODO - extract 'measure {a} = 1' to a lemma
      simp_rw [MeasureTheory.Measure.haar_singleton]
      unfold myHaar
      simp_rw [← mul_singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.haarMeasure_self]
      rw [ENNReal.tsum_set_const]
      simp
      norm_cast
      rw [Set.Finite.encard_eq_coe_toFinset_card s_finite]
    . exact Set.Finite.countable s_finite
    .
      apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp
  .
    have s_infinite: s.Infinite := by
      exact s_finite
    rw [MeasureTheory.Measure.count_apply_infinite s_infinite]
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.measure_biUnion]
    .
      simp_rw [MeasureTheory.Measure.haar_singleton]
      unfold myHaar
      simp_rw [← mul_singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.haarMeasure_self]
      simp only [ENNReal.tsum_one, ENat.toENNReal_eq_top, ENat.card_eq_top]
      exact Set.infinite_coe_iff.mpr s_finite
    . exact Set.to_countable s
    . apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp


@[expose]
instance my_add_haar_right_invariant: (myHaarAddOpp.IsAddRightInvariant (G := Additive (G))) := by
  rw [my_add_haar_eq_count]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)


-- With the counting measure, A.E is the same as everywgere
lemma count_ae_everywhere (p: G → Prop): (∀ᵐ g ∂(MeasureTheory.Measure.count), p g) = ∀ a: G, p a := by
  rw [MeasureTheory.ae_iff]
  simp [MeasureTheory.Measure.count_eq_zero_iff]
  -- TODO - there has to be a much simpler way of proving this
  refine ⟨?_, ?_⟩
  . intro h
    intro a
    by_contra this
    have a_in: a ∈ {a | ¬ p a} := by
      simp [this]
    have foo := Set.nonempty_of_mem a_in
    rw [← Set.not_nonempty_iff_eq_empty] at h
    contradiction
  . intro h
    by_contra this
    rw [← ne_eq] at this
    rw [← Set.nonempty_iff_ne_empty'] at this
    obtain ⟨a, ha⟩ := this
    specialize h a
    simp at ha
    contradiction

lemma ae_eventually_everywhere {f g: G → ℝ}: ((∀ᵐ (x : G), f x = g x)) ↔ (f = g) := by
  simp [MeasureTheory.volume]
  simp_rw [my_haar_eq_count]
  have foo := count_ae_everywhere (p := fun a => f a = g a)
  conv at foo =>
    rhs
    equals f = g =>
      have my_ext := funext_iff (f := f) (g := g)
      simp
      exact id (Iff.symm my_ext)

  simp
  simp at foo
  exact foo


@[simp]
lemma ae_eq_everywhere {f g: G → ℝ}: (f =ᶠ[MeasureTheory.ae MeasureTheory.volume (α := G)] g) ↔ (f = g) := by
  simp [Filter.EventuallyEq]
  apply ae_eventually_everywhere


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Defs_LipschitzH
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Lipschitz harmonic functions

The type `LipschitzH` of Lipschitz harmonic functions on `G`, its additive and vector space
structure, and finiteness of balls.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

@[expose] def Harmonic (f: G → ℝ): Prop := ∀ x: G, f x = ((1 : ℝ) / #(S)) * ∑ s ∈ S, f (s * x)
structure LipschitzH [Generates ] where
  -- The underlying function
  toFun: G → ℝ
  -- The function is Lipschitz for some constant C
  lipschitz: ∃ C, LipschitzWith C toFun
  -- The function is harmonic
  harmonic: Harmonic  toFun

@[expose] def IsLipschitz (f: G → ℝ) := ∃ C, LipschitzWith C f

instance instFunLikeLipschitzHGReal: FunLike (LipschitzH) G ℝ where
  coe := LipschitzH.toFun
  -- TODO - why does this work? I blindly copied it from `OneHom.funLike`
  coe_injective f g h := by cases f; cases g; congr

omit hGS in
@[ext]
theorem LipschitzH.ext [Generates ] {f g: LipschitzH} (h: ∀ x, f.toFun x = g.toFun x): f = g := DFunLike.ext _ _ h

instance LipschitzH.add [Generates ] : Add (LipschitzH) := {
  add := fun f g => {
    toFun := fun x => f.toFun x + g.toFun x
    lipschitz := by
      obtain ⟨C1, hC1⟩ := f.lipschitz
      obtain ⟨C2, hC2⟩ := g.lipschitz
      use C1 + C2
      exact LipschitzWith.add hC1 hC2
    harmonic := by
      unfold Harmonic
      intro x
      have ha := f.harmonic
      have hb := g.harmonic
      unfold Harmonic at ha hb
      simp_rw [ha x, hb x]
      field_simp
      rw [← Finset.sum_add_distrib]
  }
}


-- TODO - mark this as a simp lemma
omit hGS in
@[simp]
lemma LipschitzH_apply [Generates ] (f: LipschitzH) (x: G): f x = f.toFun x := rfl


lemma S_nonempty: S.Nonempty := by exact Finset.nonempty_coe_sort.mp hS

lemma S_card_ne_zero_re: (#(S) : ℝ) ≠ 0 := by
  norm_cast
  simp
  have foo := hS
  simp only [nonempty_subtype] at foo
  exact Finset.nonempty_iff_ne_empty.mp foo


@[expose] def ConstLipschitzH (z: ℝ) : LipschitzH := {
  toFun := fun x => z
  lipschitz := by
    use 0
    apply LipschitzWith.const
  harmonic := by
    unfold Harmonic
    intro x
    simp
    field_simp
    have foo := S_card_ne_zero_re
    field_simp
}


instance LipschitzH.zero [Generates ] : Zero (LipschitzH) := {
  zero := {
    toFun := fun x => 0
    lipschitz := by
      use 0
      exact LipschitzWith.const 0
    harmonic := by simp [Harmonic]
  }
}


@[simp]
theorem LipschitzH.add_apply (f g: LipschitzH) (x: G): (f + g).toFun x = f x + g x := by
  unfold LipschitzH.add
  rfl


instance lipschitzSMul: SMul ℝ (LipschitzH) := {
  smul := fun c f => {
    toFun := fun x => c * f.toFun x
    lipschitz := by
      conv =>
        rhs
        intro C
        rhs
        equals (fun (x: ℝ) => c * x) ∘ f.toFun =>
          unfold Function.comp
          simp
      obtain ⟨C, hC⟩ := f.lipschitz
      use ‖c‖₊ * C
      apply LipschitzWith.comp (lipschitzWith_smul _) hC
    harmonic := by
      unfold Harmonic
      intro x
      field_simp
      rw [← Finset.mul_sum]
      rw [← mul_div]
      rw [mul_eq_mul_left_iff]
      left
      have hf := f.harmonic x
      unfold Harmonic at hf
      simp at hf
      field_simp at hf
      exact hf
  }
}


instance negLipschitzH: Neg (LipschitzH) := {
  neg := fun f => {
    toFun := fun x => -f.toFun x
    lipschitz := by
      obtain ⟨C, hC⟩ := f.lipschitz
      use C
      exact LipschitzWith.neg hC
    harmonic := by
      have f_harmonic := f.harmonic
      simp [Harmonic] at f_harmonic
      unfold Harmonic
      intro g
      simp
      specialize f_harmonic g
      exact f_harmonic
  }
}

-- TODO - is there an existing instance we should be using here?
instance subLipschithZ: Sub (LipschitzH) := {
  sub := fun f g => f + -g
}


@[simp]
lemma lipschitz_neg_tofun (f: LipschitzH): (-f).toFun = -(f.toFun) := by
  rfl


@[simp]
lemma lipschitz_add_tofun (f g: LipschitzH): (f + g).toFun = f.toFun + g.toFun := by
  rfl

@[simp]
lemma lipschitz_sub_tofun (f g: LipschitzH): (f - g).toFun = f.toFun - g.toFun := by
  rfl

@[simp]
lemma lipschitz_smul_tofun (c: ℝ) (f: LipschitzH): (c • f).toFun = c • f.toFun := by
  rfl

instance LipschitzH.addMonoid [Generates ] : AddMonoid (LipschitzH) := {
  LipschitzH.zero,
  LipschitzH.add with
  add_assoc := fun _ _ _ => ext fun _ => add_assoc _ _ _
  zero_add := fun _ => ext fun _ => zero_add _
  add_zero := fun _ => ext fun _ => add_zero _
  nsmul := fun n f => (n : ℝ) • f
  nsmul_zero := by
    intro f
    dsimp [HSMul.hSMul, SMul.smul]
    dsimp [OfNat.ofNat]
    dsimp [Zero.zero]
    simp
  nsmul_succ := by
    intro n f
    ext g
    show (((n + 1 : ℕ) : ℝ) • f).toFun g = (((n : ℕ) : ℝ) • f).toFun g + f.toFun g
    simp [lipschitz_smul_tofun]
    push_cast
    ring
}


instance LipschitzH.instAddCommMonoid: AddCommMonoid (LipschitzH) := {
  LipschitzH.addMonoid with add_comm := fun _ _ => ext fun _ => add_comm _ _
}


instance LipschitzH.instAddCommGroup: AddCommGroup (LipschitzH) := {
  LipschitzH.instAddCommMonoid with
  sub_eq_add_neg := by
    intro f h
    ext g
    simp [lipschitz_sub_tofun, lipschitz_add_tofun, lipschitz_neg_tofun]
    rfl
  zsmul := fun n f => (n : ℝ) • f
  zsmul_zero' := by
    intro f
    ext g
    simp only [HSMul.hSMul, SMul.smul, DFunLike.coe, Int.cast_zero, zero_mul]
    rfl
  neg_add_cancel := by
    intro f
    ext g
    simp [negLipschitzH]
    rfl
  zsmul_succ' := by
    intro n f
    ext g
    show (((n + 1 : ℕ) : ℝ) • f).toFun g = (((n : ℕ) : ℝ) • f).toFun g + f.toFun g
    simp [lipschitz_smul_tofun]
    push_cast
    ring
  zsmul_neg' := by
    intro n hn
    ext g
    show ((Int.negSucc n : ℝ) • hn).toFun g = -((((n + 1 : ℕ) : ℝ)) • hn).toFun g
    simp [lipschitz_smul_tofun]
    push_cast
    ring
}


@[simp]
lemma zero_apply (x: G): (0: LipschitzH ).toFun x = 0 := by
  unfold LipschitzH.zero
  rfl


@[simp]
theorem LipschitzH.finset_sum_apply {ι: Type*} [Fintype ι] [DecidableEq ι] (s: Finset ι) (f: ι → LipschitzH) (x: G): (∑ i ∈ s, f i) x = (∑ i ∈ s, f i x) := by
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s a_not_mem ih =>
    rw [Finset.sum_insert a_not_mem]
    rw [LipschitzH_apply, add_apply]
    rw [ih]
    rw [Finset.sum_insert a_not_mem]


--set_option pp.all true

instance lipschitzHVectorSpace : Module ℝ (LipschitzH) := {
  smul := lipschitzSMul.smul
  one_smul := by simp [HSMul.hSMul, SMul.smul]
  mul_smul := by
    intro x y f
    simp [HSMul.hSMul, SMul.smul]
    ext g
    rw [mul_assoc]
  smul_zero := by
    intro c
    dsimp [HSMul.hSMul, SMul.smul]
    ext g
    simp
  smul_add := by
    intro a f g
    dsimp [HSMul.hSMul, SMul.smul]
    simp [mul_add]
    ext p
    simp [DFunLike.coe]
  add_smul := by
    intro a f g
    dsimp [HSMul.hSMul, SMul.smul]
    simp [add_mul]
    ext p
    simp [DFunLike.coe]
  zero_smul := by
    intro a
    ext g
    simp [HSMul.hSMul, SMul.smul, DFunLike.coe]
}

lemma finite_ball (x: G) (r: ℝ): Set.Finite (Metric.ball x r) := Set.Finite.of_finite_image (f := fun a => (word_norm_prod_self a).choose) (by
  have foo := List.finite_length_le S (WordNorm x + ⌈r⌉₊)
  rw [← Set.finite_coe_iff, Set.coe_setOf] at foo
  apply Finite.of_injective (β := {l : List S // l.length ≤ WordNorm x + ⌈r⌉₊}) (fun a => ⟨a.val, by (
    have ha := a.prop
    simp [-Subtype.coe_prop] at ha
    obtain ⟨y, hy, a_prod⟩ := ha
    have ⟨prod_eq, prod_len⟩ := (word_norm_prod_self y).choose_spec
    rw [a_prod] at prod_len
    rw [prod_len]
    simp [dist] at hy
    conv =>
      lhs
      equals WordDist 1 y =>
        simp [WordDist]


    grw [WordDist_triangle (y := x)]
    nth_rw 2 [WordDist_comm]
    simp [WordDist]
    simp [WordDist] at hy
    rw [← Nat.lt_ceil] at hy
    grind
  )⟩) ?_
  intro a b hab
  grind
) (by
  intro a ha b hb hab
  have a_prop := (word_norm_prod_self a).choose_spec.1
  have b_prop := (word_norm_prod_self b).choose_spec.1
  rw [← a_prop, ← b_prop]
  simp [hab]
)

-- TODO - deduplicate 99% of this with finite_ball
lemma finite_closed_ball (x: G) (r: ℝ): Set.Finite (Metric.closedBall x r) := Set.Finite.of_finite_image (f := fun a => (word_norm_prod_self a).choose) (by
  have foo := List.finite_length_le S (WordNorm x + ⌈r⌉₊)
  rw [← Set.finite_coe_iff, Set.coe_setOf] at foo
  apply Finite.of_injective (β := {l : List S // l.length ≤ WordNorm x + ⌈r⌉₊}) (fun a => ⟨a.val, by (
    have ha := a.prop
    simp [-Subtype.coe_prop] at ha
    obtain ⟨y, hy, a_prod⟩ := ha
    have ⟨prod_eq, prod_len⟩ := (word_norm_prod_self y).choose_spec
    rw [a_prod] at prod_len
    rw [prod_len]
    simp [dist] at hy
    conv =>
      lhs
      equals WordDist 1 y =>
        simp [WordDist]


    grw [WordDist_triangle (y := x)]
    nth_rw 2 [WordDist_comm]
    simp [WordDist]
    simp [WordDist] at hy
    -- This is the only part that's different from finite_ball
    grw [Nat.le_ceil (a := r)] at hy
    simpa using hy
  )⟩) ?_
  intro a b hab
  grind
) (by
  intro a ha b hb hab
  have a_prop := (word_norm_prod_self a).choose_spec.1
  have b_prop := (word_norm_prod_self b).choose_spec.1
  rw [← a_prop, ← b_prop]
  simp [hab]
)


-- TODO - I don't think we can use this, as `MeasureTheory.convolution' would require our group to be commutative
-- (via `NormedAddCommGroup`)

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Defs_Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Convolution on `G`

The convolution `Conv`, the measure `mu` and its iterates `muConv`, and the `Lp` packaging
`conv_mu_lp2`.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Convolution
open MeasureTheory

-- TODO - should we define this using 'Lp'?
-- NOTE - the Mathlib convolution uses the opposite order of arguments as in the Vikman paper (g(x - t) instead of g(t - x))
-- I originally used 'MulOpposite' make our usage agree with the paper, but this made it an enormous pain to work with
-- (since while Additive G is defeq to G, MulOpposite G is not defeq to G)
-- Nothing in the paper should actually depend on this (since we take a convolution over a symmetric generating set S)
-- Some of our definitions will have an inverse or order swap compared to the paper, but this is better than
-- fighting with 'MulOpposite' every time we need to prove something about a convolution

-- Note - there's some defeq abuse going on here, as we're passing in 'f' and 'g' directly (they take in G, not 'Additive G')
-- However, this makes it much easier to prove properties about this via the `MeasureTheory.ConvolutionExists` API
@[expose] noncomputable def Conv (f g: G → ℝ) (x: G) : ℝ :=
  (MeasureTheory.convolution (G := Additive G) f g (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp x)


@[expose] def ConvExists (f g: G → ℝ) := MeasureTheory.ConvolutionExists (G := Additive G) (fun x => f x.toMul) (fun x => g x.toMul) (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp

@[expose]
noncomputable def mu: G → ℝ := ((1 : ℝ) / (#(S) : ℝ)) • ∑ s ∈ S, Pi.single s (1 : ℝ)

-- Definition 3.11 in Vikman - the m-fold convolution of μ with itself
@[expose] noncomputable def muConv (n: ℕ): G → ℝ := (Nat.iterate (fun f => Conv  f (mu )) n) (mu )


-- TODO - this is left over from when I used MulOpposite
-- we should remove all usages of this
abbrev opAdd (g : G) := Additive.ofMul g


lemma conv_eq_sum {f h: G → ℝ} (hconv: ConvExists f h) (g: G): Conv f h g = ∑' (a : Additive G), f (a) * h (g * (Additive.toMul a)⁻¹) := by
  unfold Conv
  unfold MeasureTheory.convolution
  rw [MeasureTheory.integral_countable']
  .
    simp_rw [MeasureTheory.measureReal_def]
    unfold myHaarAddOpp
    simp_rw [MeasureTheory.Measure.addHaar_singleton]
    simp [MeasureTheory.Measure.addHaarMeasure_self]
    simp_rw [← singleton_carrier]
    simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
    simp [MeasureTheory.Measure.addHaarMeasure_self]
    field_simp

    -- TODO - avoid defeq abuse here
    conv =>
      lhs
      arg 1
      intro a
      rhs
      equals h (Additive.ofMul g - a) =>
        rfl

    conv =>
      rhs
      arg 1
      intro a
      rhs
      arg 1
      equals Additive.ofMul g - a =>
        rw [sub_eq_add_neg]
        rfl

  . exact (hconv (opAdd g))


lemma conv_eq_sum'  {f h: G → ℝ} (hconv: ConvExists f h): Conv f h = fun g => ∑' (a : Additive G), f ((Additive.toMul a)) * h (g * (Additive.toMul a)⁻¹) := by
  funext g
  exact conv_eq_sum hconv g


abbrev delta (s: G): G → ℝ := Pi.single s 1


-- A versi on of `conv_exists` where at least one of the functions has finite support
-- This lets us avoid dealing with 'MemLp' in most cases
lemma conv_exists_fin_supp (f g: G → ℝ) (hfg: f.support.Finite ∨ g.support.Finite): ConvExists f g := by
  unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt
  intro x
  apply Continuous.integrable_of_hasCompactSupport
  . exact continuous_of_discreteTopology
  .
    unfold HasCompactSupport
    rw [isCompact_iff_finite]
    dsimp [tsupport]
    rw [closure_discrete]
    simp only [Function.support_mul]
    match hfg with
    | .inl hf =>
      apply Set.Finite.inter_of_left
      apply Set.Finite.subset (s := opAdd '' f.support)
      . unfold opAdd
        exact Set.Finite.image (fun g ↦ Additive.ofMul g) hf
      . intro a ha
        simp at ha
        simp [opAdd]
        exact ha
    | .inr hg =>
      apply Set.Finite.inter_of_right
      let myFun := fun a => -(opAdd a) + x
      have finite_image := Set.finite_image_iff (f := myFun) (s := g.support) ?_
      .
        conv =>
          arg 1
          equals (myFun '' Function.support g) =>
            ext a
            simp
            refine ⟨?_, ?_⟩
            . intro ha
              use (Additive.toMul x) / ((Additive.toMul a))
              refine ⟨ha, ?_⟩
              simp [myFun, opAdd]
            . intro ha
              simp [myFun, opAdd] at ha
              obtain ⟨b, b_zero, a_eq⟩ := ha
              rw [← a_eq]
              simp [b_zero]
        rw [finite_image]
        exact hg
      .
        simp [myFun, opAdd]

-- Proposition 3.12, item 1, in Vikman
lemma f_conv_delta (f: G → ℝ) (g s: G): (Conv  f (delta s)) g = f (s⁻¹ * g) := by
  unfold delta
  rw [conv_eq_sum]
  .
    rw [tsum_eq_sum (s := {opAdd ((s⁻¹ * g))}) ?_]
    .
      simp
      rfl
    .
      intro b hb
      simp only [Finset.mem_singleton] at hb
      simp only [mul_eq_zero]
      right
      apply Pi.single_eq_of_ne
      apply_fun (fun x => s⁻¹ * x)
      simp
      apply_fun (fun x => (x * (Additive.toMul b)) )
      simp
      rw [eq_comm]
      unfold opAdd at hb
      apply_fun Additive.ofMul
      simp
      apply_fun (fun x => x + b)
      rw [add_assoc]
      simp
      exact hb
  .
    apply conv_exists_fin_supp
    right
    simp


lemma mu_finsupp: (mu ).support.Finite := by
  simp [mu]
  rw [Function.support_const_smul_of_ne_zero]
  .
    apply Set.Finite.subset (s := ⋃ i ∈ S, Function.support (Pi.single i (1 : ℝ)))
    .
      simp
      exact Set.toFinite (⋃ i ∈ S, {i})
    .
      conv =>
        lhs
        arg 1
        equals fun (x: G) => ∑ s ∈ S, Pi.single (M := fun _ : G => ℝ) s (1 : ℝ) x =>
          funext a
          simp
      apply Finset.support_sum (s := S) (f := fun i => Pi.single i (1: ℝ))
  . simp
    have foo := hS
    simp at foo
    exact Finset.nonempty_iff_ne_empty.mp foo

-- Proposition 3.12, item 2, in Vikman
lemma f_conv_mu (f: G → ℝ): (Conv  f (mu )) = fun g => ((1 : ℝ) / (#(S) : ℝ)) * ∑ s ∈ S, f (s * g) := by
  funext g
  rw [conv_eq_sum]
  .

    dsimp [mu]
    simp_rw [← mul_assoc]
    conv =>
      lhs
      arg 1
      intro a
      rhs
      equals (∑ s ∈ S, (Pi.single (M := fun _ : G => ℝ) s (1 : ℝ) ((g * (Additive.toMul a)⁻¹)))) =>
        simp

    simp_rw [Finset.mul_sum]
    rw [Summable.tsum_finsetSum]
    .
      have delta_conv := f_conv_delta  f g
      conv at delta_conv =>
        intro x
        rw [conv_eq_sum (by
          apply conv_exists_fin_supp
          right
          simp
        )]

      simp_rw [mul_comm, mul_assoc]
      conv =>
        lhs
        rhs
        intro x
        arg 1
        intro b
        rw [mul_comm]
        rw [mul_assoc]
      simp [delta] at delta_conv
      conv at delta_conv =>
        intro x
        lhs
        arg 1
        intro a
        rw [mul_comm]
      conv =>
        lhs
        rhs
        intro x
        rw [Summable.tsum_mul_left (hf := by (
          simp [Pi.single_apply]
          apply summable_of_finite_support
          apply Set.Finite.subset (s := {(opAdd (   x⁻¹ * g  ))})
          . simp
          . intro z hz
            simp
            simp at hz
            rw [← hz.1]
            simp
        ))]
        rw [delta_conv x]

      simp
      rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [mul_comm]
      simp
      left
      conv =>
        lhs
        arg 1
        equals S⁻¹ =>
          exact S_eq_Sinv
      simp
    .
      intro s hs
      by_cases card_zero: #(S) = 0
      .
        simp [card_zero]
      .
        conv =>
          arg 1
          intro a
          rw [mul_assoc, mul_comm, mul_assoc]
        rw [summable_mul_left_iff]
        .
          -- TODO - deduplicate this
          simp [Pi.single_apply]
          apply summable_of_finite_support
          apply Set.Finite.subset (s := {(opAdd (s⁻¹ * g ))})
          . simp
          . intro z hz
            simp
            simp at hz
            rw [← hz.1]
            simp
        .
          simp [card_zero]
  . apply conv_exists_fin_supp
    right
    apply mu_finsupp


@[expose]
noncomputable def conv_mu_lp2 (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := MeasureTheory.MemLp.toLp (Conv f (mu )) (by
  rw [MeasureTheory.MemLp]
  refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
  simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm']
  rw [f_conv_mu]
  simp_rw [Finset.mul_sum]
  have other := MeasureTheory.memLp_finset_sum (μ := MeasureTheory.volume (α := G)) (s := S) (p := 2) (f := fun s a => ((1 : ℝ) / (#(S) : ℝ)) * f (s * a)) (by
    intro s hs
    simp
    apply MeasureTheory.MemLp.const_mul
    rw [← Function.comp_def]
    apply MeasureTheory.MemLp.comp_of_map
    .
      simp [MeasureTheory.volume]
      simp_rw [my_haar_eq_count]
      rw [MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self s]
      have mem_f := Lp.memLp f
      simp [volume, my_haar_eq_count] at mem_f
      exact mem_f
    . apply AEMeasurable.of_discrete
  )
  have sum_norm := other.2
  simp [eLpNorm, eLpNorm'] at sum_norm
  field_simp at sum_norm
  field_simp
  exact sum_norm
)

-- The Vikman paper defines the Laplace operator as a function ' ∆ : ℓ2(G) → ℓ2(G)'
-- However, we later have '∆ H_n', where H_n is only known to be in L∞
-- We should eventually refactor this, but for we, we just define it twice, once with just plain functions
-- The 'b' is for 'base' (we should come up with a better name)

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Defs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The discrete Laplacian and the `G`-action

The Laplacian `Laplace_b` / `Laplace`, the constant functions `ConstF`, the quotient `W`, the
`G`-action `gAct`, and the closed-ball counting lemmas.

Root of the `Gromov.Defs` hierarchy: importing it pulls in the word metric, the measure
structure, `LipschitzH` and the convolution API.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Convolution
open MeasureTheory

@[expose] noncomputable def Laplace_b (f: G → ℝ): G → ℝ := f - (Conv f (mu ))
@[expose] noncomputable def Laplace (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := f - (conv_mu_lp2 f)


-- TODO - make this Finite to avoid a non-compuatable Fintype instance
noncomputable instance fintype_closedBall (x: G) (r: ℝ): Fintype ↑(Metric.closedBall x r) := Set.Finite.fintype (finite_closed_ball _ _)


-- Graphs and Discrete Direchlet Spaces
-- https://www.math.uni-potsdam.de/fileadmin/user_upload/Prof-GraphTh/Keller/KellerLenzWojciechowski_GraphsAndDiscreteDirichletSpaces_wu_version.pdf


@[expose]
def ConstF: Submodule ℝ (LipschitzH) := {
  carrier := Set.range ConstLipschitzH
  add_mem' := by
    intro a b ha hb
    simp at ha
    simp at hb
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    simp
    use (x + y)
    ext g
    simp [ConstLipschitzH]
    rw [← hx, ← hy]
    dsimp [ConstLipschitzH]
  zero_mem' := by
    use (0 : ℝ)
    simp [ConstLipschitzH]
    ext g
    simp
  smul_mem' := by
    intro c f hf
    simp at hf
    simp
    obtain ⟨x, hx⟩ := hf
    use (c * x)
    ext g
    simp [ConstLipschitzH]
    left
    rw [← hx]
    simp [ConstLipschitzH]
}

@[expose]
instance isometricGMul: IsIsometricSMul (MulOpposite G) (G) where
  isometry_smul := by
    intro g
    simp [Isometry]
    intro a b
    simp [edist]
    simp [PseudoMetricSpace.edist]
    simp [WordDist]


@[expose]
def gAct (g: G) (v: LipschitzH ): LipschitzH  := {
  toFun := fun x => v (x * g)
  lipschitz := by
    obtain ⟨C, hC⟩ := v.lipschitz
    use C
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [lipschitzWith_iff_dist_le_mul] at hC
    specialize hC (x * g) (y * g)
    simp [DFunLike.coe]
    grw [hC]
    simp [dist, WordDist]
  harmonic := by
    unfold Harmonic
    intro x
    simp
    have v_harmonic := v.harmonic
    simp [Harmonic] at v_harmonic
    specialize v_harmonic (x * g)
    rw [v_harmonic]
    simp_rw [← mul_assoc]
}


@[expose]
def gAct_const (g: G) (z: ℝ): gAct g (ConstLipschitzH z) = ConstLipschitzH z := by
  unfold gAct
  unfold ConstLipschitzH
  ext x
  simp [DFunLike.coe]

@[expose]
noncomputable def f_n (n: ℕ) (g: G): ℝ := ((1: ℝ) / ((n + 1): ℝ)) * ∑ m: Fin (n + 1), muConv  (m.val) g


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.LipschitzNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Lipschitz seminorm on `LipschitzH`

This file collects the Lipschitz seminorm `LipschitzSemiNorm` on functions `G → ℝ`, the basic
lemmas about it, and the resulting `SeminormedAddCommGroup` / `NormedSpace` instances on
`LipschitzH`. These instances are public so that they are available to downstream files.

Note that we only implement `SeminormedAddCommGroup` for `LipschitzH`, so this is only really a
seminormed space. The quotient space `W := LipschitzH ⧸ ConstF` is an actual normed space.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS

@[expose]
noncomputable def LipschitzSemiNorm (f: G → ℝ): NNReal := sInf { k: NNReal | LipschitzWith k f }

lemma lipschiz_norm_zero: LipschitzSemiNorm  (0) = 0 := by
  unfold LipschitzSemiNorm
  have zero_mem: 0 ∈ { k: NNReal | LipschitzWith k (0 : LipschitzH) } := by
    simp
  have sinf_le: sInf { k: NNReal | LipschitzWith k (0 : LipschitzH) } ≤ 0 := by
    exact csInf_le' zero_mem
  exact nonpos_iff_eq_zero.mp sinf_le


-- TODO - upstream to mathlib
lemma lipschitz_attains_norm (f: G → ℝ) (hf: IsLipschitz f): LipschitzWith (LipschitzSemiNorm f) f := by
  by_contra!
  simp [LipschitzWith] at this
  obtain ⟨x, y, hdist⟩ := this
  have edist_ne_zero: edist x y ≠ 0 := by
    by_contra!
    rw [this] at hdist
    simp at this
    rw [this] at hdist
    simp at hdist

  have edist_not_top: edist x y ≠ ⊤ := by
    rw [edist_nndist]
    exact ENNReal.coe_ne_top

  rw [← ENNReal.lt_div_iff_mul_lt (by simp) (Or.inl edist_not_top)] at hdist
  simp [LipschitzSemiNorm] at hdist
  have isglb_sinf := isGLB_csInf (s := { k: NNReal | LipschitzWith k f }) (by
    obtain ⟨K, hK⟩ := hf
    use K
    simp
    exact hK
  ) (by simp)


  have between := IsGLB.exists_between (b := (edist (f x) (f y) / edist x y).toNNReal) isglb_sinf (by
    rw [edist_nndist]
    rw [edist_nndist]
    conv =>
      rhs
      equals (nndist (f x) (f y)) / (nndist x y) =>
        rw [← ENNReal.coe_div]
        simp
        exact ENNReal.coe_ne_zero.mp edist_ne_zero

    rw [edist_nndist] at hdist
    rw [edist_nndist] at hdist
    have edist_gt_zero: edist x y > 0 := by
      exact pos_of_ne_zero edist_ne_zero

    have x_ne_y := edist_pos.mp edist_gt_zero

    conv at hdist =>
      rhs
      equals ENNReal.ofNNReal ((nndist (f x) (f y)) / (nndist x y)) =>
        rw [ENNReal.coe_div]
        simp [x_ne_y]


    norm_cast at hdist
  )
  obtain ⟨D, lipschitz_d, sinf_le_d, d_lt_slope⟩ := between
  simp [LipschitzWith] at lipschitz_d
  specialize lipschitz_d x y
  rw [mul_comm] at lipschitz_d
  apply ENNReal.div_le_of_le_mul' at lipschitz_d
  repeat rw [edist_nndist] at lipschitz_d
  repeat rw [edist_nndist] at d_lt_slope
  rw [← ENNReal.coe_div] at lipschitz_d
  .
    norm_cast at lipschitz_d
    rw [← ENNReal.coe_div] at d_lt_slope
    .
      norm_cast at d_lt_slope
      apply not_lt_of_ge at lipschitz_d
      contradiction
    . rw [edist_nndist] at edist_ne_zero
      exact fun a ↦ edist_ne_zero (congrArg ENNReal.ofNNReal a)
  . rw [edist_nndist] at edist_ne_zero
    exact fun a ↦ edist_ne_zero (congrArg ENNReal.ofNNReal a)


lemma lipschitz_norm_triangle (x y z: G → ℝ) (hx: IsLipschitz x) (hy: IsLipschitz y) (hz: IsLipschitz z): LipschitzSemiNorm (x - z) ≤ LipschitzSemiNorm (x - y) + LipschitzSemiNorm (y - z) := by
  simp [LipschitzSemiNorm]
  conv =>
    pattern x - z
    equals (x - y) + (y - z) =>
      simp


  have sum_norm_mem: (LipschitzSemiNorm (x - y)) + (LipschitzSemiNorm (y - z)) ∈ { k: NNReal | LipschitzWith k ((x - y) + (y - z)) } := by
    simp only [LipschitzSemiNorm]
    apply LipschitzWith.add
    .
      apply lipschitz_attains_norm
      simp [IsLipschitz]
      simp [IsLipschitz] at hx
      simp [IsLipschitz] at hy
      obtain ⟨X, hX⟩ := hx
      obtain ⟨Y, hY⟩ := hy
      use X + Y
      apply LipschitzWith.sub hX hY
    .
      apply lipschitz_attains_norm
      simp [IsLipschitz]
      simp [IsLipschitz] at hy
      simp [IsLipschitz] at hz
      obtain ⟨Y, hY⟩ := hy
      obtain ⟨Z, hZ⟩ := hz
      use Y + Z
      apply LipschitzWith.sub hY hZ

  have sinf_le_sum := csInf_le (by simp) sum_norm_mem
  simp [LipschitzSemiNorm] at sinf_le_sum
  conv at sinf_le_sum =>
    pattern x - z
    equals (x - y) + (y - z) =>
      simp
  exact sinf_le_sum


lemma lipschitzH_norm_triangle (x y z: LipschitzH): LipschitzSemiNorm (x - z) ≤ LipschitzSemiNorm (x - y) + LipschitzSemiNorm (y - z) := by
  apply lipschitz_norm_triangle x y z x.lipschitz y.lipschitz z.lipschitz

lemma lipschitzWith_neg_iff {f : G → ℝ} {K : NNReal} : LipschitzWith K (-f) ↔ LipschitzWith K f :=
  ⟨fun h => by simpa using h.neg, LipschitzWith.neg⟩

lemma lipschitzSemiNorm_neg (f : G → ℝ) : LipschitzSemiNorm (-f) = LipschitzSemiNorm f := by
  unfold LipschitzSemiNorm
  congr 1
  ext k
  simp only [Set.mem_setOf_eq, lipschitzWith_neg_iff]


set_option maxHeartbeats 1000000 in
noncomputable instance LipschitzH_seminorm: SeminormedAddCommGroup (LipschitzH) where
  norm := fun v => LipschitzSemiNorm v
  dist_self := by
    intro v
    simp [LipschitzSemiNorm]
    exact lipschiz_norm_zero
  dist_comm := by
    intro x y
    have key : LipschitzSemiNorm (⇑(-x + y)) = LipschitzSemiNorm (⇑(-y + x)) := by
      rw [← lipschitzSemiNorm_neg (⇑(-y + x))]
      congr 1
      ext a
      simp only [lipschitz_neg_tofun, lipschitz_add_tofun, LipschitzH_apply, Pi.add_apply,
        Pi.neg_apply]
      ring
    simpa using key
  dist_triangle := by
    intro x y z
    have key : LipschitzSemiNorm (⇑(-x + z)) ≤
        LipschitzSemiNorm (⇑(-x + y)) + LipschitzSemiNorm (⇑(-y + z)) := by
      have h := lipschitzH_norm_triangle z y x
      have e1 : (⇑(-x + z) : G → ℝ) = ⇑(z - x) := by
        ext a
        simp only [lipschitz_neg_tofun, lipschitz_add_tofun, lipschitz_sub_tofun, LipschitzH_apply,
          Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
        ring
      have e2 : (⇑(-x + y) : G → ℝ) = ⇑(y - x) := by
        ext a
        simp only [lipschitz_neg_tofun, lipschitz_add_tofun, lipschitz_sub_tofun, LipschitzH_apply,
          Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
        ring
      have e3 : (⇑(-y + z) : G → ℝ) = ⇑(z - y) := by
        ext a
        simp only [lipschitz_neg_tofun, lipschitz_add_tofun, lipschitz_sub_tofun, LipschitzH_apply,
          Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
        ring
      rw [e1, e2, e3, add_comm]
      exact h
    exact_mod_cast key

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.TendstoNhdsMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Products of one-sided limits

Staging ground for `Filter.TendstoNhdsWithinIoi.mul`, the two-function analogue of the existing
`Filter.TendstoNhdsWithinIoi.const_mul` / `Filter.TendstoNhdsWithinIoi.mul_const` lemmas in
`Mathlib.Topology.Algebra.Monoid`. Intended to be upstreamed into that file later.
-/


open Filter Topology Set

/-- If `f` and `g` tend to `c` and `d` respectively from the right, and both limit points are
nonnegative, then `f * g` tends to `c * d` from the right. This is the two-function analogue of
`Filter.TendstoNhdsWithinIoi.const_mul` and `Filter.TendstoNhdsWithinIoi.mul_const`; since neither
factor is constant it requires joint continuity of multiplication (`ContinuousMul`) rather than
merely `SeparatelyContinuousMul`. -/
theorem Filter.TendstoNhdsWithinIoi.mul {α 𝕜 : Type*} [MulZeroClass 𝕜] [Preorder 𝕜]
    [TopologicalSpace 𝕜] [ContinuousMul 𝕜] [PosMulStrictMono 𝕜] [MulPosMono 𝕜] {l : Filter α}
    {f g : α → 𝕜} {c d : 𝕜} (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : Tendsto f l (𝓝[>] c))
    (hg : Tendsto g l (𝓝[>] d)) : Tendsto (fun a => f a * g a) l (𝓝[>] (c * d)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin hf).mul (tendsto_nhds_of_tendsto_nhdsWithin hg)) <|
    ((tendsto_nhdsWithin_iff.mp hf).2.and (tendsto_nhdsWithin_iff.mp hg).2).mono
      fun _ ⟨hfa, hga⟩ => by rw [Set.mem_Ioi] at *; exact mul_lt_mul'' hfa hga hc hd
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_LinearAlgebra_Matrix_PosDef
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Positive semidefinite matrices

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


-- TODO - generalize and upstream
-- Based on https://math.stackexchange.com/questions/1101184/show-that-if-x-succeq-y-then-detx-ge-dety
lemma matrix_psd_det_one {n: Type*} [Fintype n] [DecidableEq n] (A: Matrix n n ℝ) (ha: A.PosSemidef): 1 ≤ (A + 1).det := by
  have foo := ha.isHermitian.spectral_theorem
  have H := ha.isHermitian
  simp at foo
  rw [foo]
  conv =>
    rhs
    arg 1
    equals H.eigenvectorUnitary * ((Matrix.diagonal H.eigenvalues) + 1) * (star H.eigenvectorUnitary) =>
      rw [mul_add, add_mul]
      simp

  rw [Matrix.det_conj_of_mul_eq_one]
  .
    rw [← Matrix.diagonal_one']
    rw [Matrix.diagonal_add]
    simp
    apply Finset.one_le_prod
    intro i _
    have foo := ha.eigenvalues_nonneg
    grind
  . simp
  . simp
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_LinearAlgebra_Matrix_Det
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Determinants of matrices of bilinear forms

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise


open MatrixOrder in
lemma matrix_det_montone {n: Type*} [Fintype n] [DecidableEq n] (A B: Matrix n n ℝ) (hb: B.PosDef) (hab: (A - B).PosSemidef): B.det ≤ A.det := by

  have invert_sqrt: Invertible (CFC.sqrt B) := by
    apply Matrix.invertibleOfIsUnitDet
    rw [Matrix.PosSemidef.det_sqrt hb.posSemidef]
    simp
    rw [← ne_eq, Real.sqrt_ne_zero]
    . grind [hb.det_pos]
    . grind [hb.det_pos]

  have det_prod_eq: A.det = B.det * ((CFC.sqrt B)⁻¹ * (A - B) * (CFC.sqrt B)⁻¹ + 1).det := by
    conv =>
      lhs
      arg 1
      equals (CFC.sqrt B) * (CFC.sqrt B)⁻¹ * A * (CFC.sqrt B)⁻¹ * (CFC.sqrt B) =>
        simp

    rw [mul_assoc, mul_assoc, mul_assoc]
    rw [Matrix.det_mul]
    rw [← mul_assoc, ← mul_assoc]
    rw [Matrix.det_mul]
    ring
    rw [hb.posSemidef.det_sqrt]
    simp only [RCLike.sqrt_real]
    rw [Real.sq_sqrt (by grind [hb.det_pos])]
    rw [mul_sub]
    rw [sub_mul]
    conv =>
      rhs
      rhs
      rhs
      lhs
      rhs
      arg 1
      arg 2
      rw [← CFC.sqrt_mul_sqrt_self (a := B)]

    simp

  rw [det_prod_eq]
  rw [le_mul_iff_one_le_right]
  .
    apply matrix_psd_det_one
    rw [hb.posSemidef.inv_sqrt]
    have foo := (CFC.sqrt_nonneg B⁻¹)
    rw [Matrix.le_iff] at foo
    simp at foo
    nth_rw 2 [← foo.isHermitian.eq]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    exact hab
  . apply hb.det_pos

-- TODO - upstream. Mathlib only has `Finset.sum_biUnion` (which needs `PairwiseDisjoint`)
-- and the `ENNReal` `tsum` versions.
theorem Finset.sum_biUnion_le {κ α : Type*} [DecidableEq α] {s: Finset κ} {t: κ → Finset α}
    {f: α → ℝ} (hf: ∀ x, 0 ≤ f x): ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have hnn: 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
    linarith
end

section
-- module Solutions.OAIQ093_PR.CutoffInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The cutoff inequality

`cutoff_inequality`, the discrete integration-by-parts estimate underlying Theorem 3.23.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

-- Reverse poincare inequality
-- Lemma 12.2
-- The gradient-squared for the *left* Cayley graph (edges `{x, s * x}`).
-- Note that, as with `Harmonic`, our multiplication order is swapped relative to the paper:
-- `f (s * x)` instead of `f (x * s)`. This is what makes it agree with `MeasureTheory.convolution`
-- (see the note above `Conv` in `Defs.lean`) and with the right-invariant `WordDist`, so that
-- the balls `B_c_r j r = B_r r * j` are right translates and no `MulOpposite` leaks into the
-- convolution terms. `deriv_sq` is invariant under right translation:
-- `deriv_sq (f ∘ (· * j)) x = deriv_sq f (x * j)`, which is what Lemma 3.25 (c) needs.
@[expose] noncomputable def deriv_sq (f: G → ℝ) (x: G) := ∑ s ∈ S, (f (s * x) - f x)^2

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.QuadraticForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The quadratic form `Q_R` and its determinant bound

The quadratic form `Q_R` on `LipschitzH`, its matrix `Q_R_matrix`, positive-definiteness, and
the determinant bound `det_bound` for a fixed finite-dimensional subspace `V`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

@[expose] noncomputable def Q_R (R : ℝ) (u v: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g) * (v g)

@[expose] noncomputable def Q_R_lin (V: Submodule ℝ LipschitzH) (R: ℝ): V →ₗ⋆[ℝ] V →ₗ[ℝ] ℝ := {
  toFun := fun u => {
    toFun := fun v => Q_R R u.val v.val
    map_add' := by
      intro a b
      simp [Q_R]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro x a
      simp [Q_R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  }
  map_add' := by
    intro a b
    ext y
    simp [Q_R]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro x a
    ext y
    simp [Q_R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
}


@[expose] noncomputable def Q_R_lin_plain (V: Submodule ℝ LipschitzH) (R: ℝ): V →ₗ[ℝ] V →ₗ[ℝ] ℝ := {
  toFun := fun u => {
    toFun := fun v => Q_R R u.val v.val
    map_add' := by
      intro a b
      simp [Q_R]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro x a
      simp [Q_R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  }
  map_add' := by
    intro a b
    ext y
    simp [Q_R]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro x a
    ext y
    simp [Q_R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
}

open scoped Topology

-- These definitions go outside, since we need to explicitly vary the V that we pass in for the theorem statement
@[expose]
noncomputable def V_basis (V: Submodule ℝ LipschitzH) := Module.Basis.ofVectorSpace ℝ V
@[expose] noncomputable def Q_R_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (R: ℝ) := ((Q_R_lin V R).toMatrix₂ b b)
@[expose] noncomputable def my_expr {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (d: ℝ) (R : ℕ) := #(S ^ R) * ((Q_R_matrix b R).det ^ ((1 : ℝ) / Module.finrank ℝ V)) / (R ^ d)
-- This is a liminf < ∞ in Vikman, but we can actually prove that it goes to 0, which makes things much easier to work with
@[expose] noncomputable def growth_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (d: ℝ) := Filter.Tendsto (fun (R: ℕ) => my_expr b d R) (Filter.atTop) ((𝓝[>] 0))

lemma Q_R_lin_symm (V: Submodule ℝ LipschitzH) (R: ℝ): (Q_R_lin V R).IsSymm := {
  eq := by
    intro u v
    simp [Q_R_lin, Q_R]
    simp_rw [mul_comm]
}

lemma Q_R_lin_hermetian {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} (b : Module.Basis ι ℝ ↥V) (R: ℝ): (Q_R_matrix b R).IsHermitian := by
  rw [Q_R_matrix, ← LinearMap.isSymm_iff_isHermitian_toMatrix]
  apply Q_R_lin_symm

lemma Q_R_lin_sub_pos_semi_def (V : Submodule ℝ LipschitzH) (R_1 R_2: ℝ) (hr: R_1 ≤ R_2): ((Q_R_lin V R_2) - Q_R_lin V R_1).IsPosSemidef := by
  rw [LinearMap.isPosSemidef_def]
  refine ⟨?_, ?_⟩
  .
    -- `Q_R_lin` lands in a nested linear-map type `V →ₗ⋆[ℝ] V →ₗ[ℝ] ℝ`; giving
    -- `sub_eq_add_neg` its arguments explicitly avoids a metavariable whose `Sub`
    -- instance would need a deeper `synthPending` than the default depth allows.
    rw [sub_eq_add_neg (Q_R_lin V R_2) (Q_R_lin V R_1)]
    apply LinearMap.IsSymm.add
    . apply Q_R_lin_symm
    .
      -- TODO - add smul/neg lemmas so that we don't need to inline the proof here
      exact {
        eq := by
          intro u v
          simp [Q_R_lin, Q_R]
          simp_rw [mul_comm]
    }
  .
    rw [LinearMap.isNonneg_def]
    intro x
    simp [Q_R_lin, Q_R]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    .
      simp [Metric.closedBall]
      grind
    . intro a ha a_not
      rw [← pow_two]
      positivity

lemma v_r_all_nonzero (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V]: ∃ R: ℝ, 1 < R ∧ ∀ u ∈ V, u ≠ 0 → ∃ g ∈ Metric.closedBall 1 R, u g ≠ 0 := by
  let zero_ball (n: ℕ): Submodule ℝ V := {
      carrier := {v: V | ∀ g ∈ Metric.closedBall 1 n, v.val g = 0}
      add_mem' := by
        intro a b ha hb
        simp at ha hb
        simp
        grind
      zero_mem' := by
        simp
      smul_mem' := by
        intro c x hx
        simp at hx
        simp
        intro g hg
        grind
  }

  let f: ℕ →o (Submodule ℝ V)ᵒᵈ := {
    toFun := zero_ball
    monotone' := by
      intro a b hab x hx
      simp [zero_ball] at hx
      simp [zero_ball]
      intro g hg
      apply hx g
      grw [hab] at hg
      exact hg
  }
  have artintian: IsArtinian ℝ V := by infer_instance
  rw [← monotone_stabilizes_iff_artinian] at artintian
  specialize artintian f
  obtain ⟨n, hn⟩ := artintian

  have inter_zero: ⨅ n: ℕ, zero_ball n = 0 := by
    ext a
    simp only [Submodule.mem_iInf, Submodule.zero_eq_bot, Submodule.mem_bot]
    refine ⟨?_, ?_⟩
    .
      intro hi
      ext g
      specialize hi (WordNorm g)
      simp [zero_ball] at hi
      specialize hi g
      simp [dist, WordDist_one] at hi
      simp [hi]
    . intro hi
      simp [hi]

  rw [← Antitone.iInf_nat_add (k := n)] at inter_zero
  .
    conv at inter_zero =>
      lhs
      arg 1
      intro k
      equals zero_ball n =>
        specialize hn (k + n) (by simp)
        simp [f] at hn
        exact hn.symm

    simp at inter_zero
    simp [zero_ball] at inter_zero
    use (max 2 n)
    refine ⟨by (grind), ?_⟩
    intro u hu
    rw [Set.ext_iff] at inter_zero
    specialize inter_zero ⟨u, hu⟩
    simp at inter_zero
    intro u_ne_zero
    simp [u_ne_zero] at inter_zero
    simp
    obtain ⟨x, h_x_1, h_x_2⟩ := inter_zero
    use x
    refine ⟨?_, ?_⟩
    . right
      exact h_x_1
    . exact h_x_2
  . intro a b hab
    simp [zero_ball]
    intro u hu hg
    intro g g_dist
    specialize hg g
    grw [hab] at g_dist
    specialize hg g_dist
    exact hg

@[expose] noncomputable def R'_ (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V] : ℝ := (v_r_all_nonzero V).choose

lemma R'_pos (V: Submodule ℝ LipschitzH) [FiniteDimensional ℝ V]: 1 < R'_ V := by
  have foo := (v_r_all_nonzero V).choose_spec.1
  exact foo

lemma Q_R_pos_on_R' {V: Submodule ℝ LipschitzH} (v: V) (hv: v ≠ 0) [FiniteDimensional ℝ V] (R: ℝ) (hR: (R'_ V) ≤ R): 0 < Q_R R v v := by
  simp [Q_R]
  rw [Finset.sum_pos_iff_of_nonneg]
  .
    by_contra!
    simp_rw [← pow_two] at this
    simp only [sq_nonpos_iff] at this
    have foo := (v_r_all_nonzero V).choose_spec.2 (v) (by apply Submodule.coe_mem) ?_
    .
      obtain ⟨g, g_mem, x_g_nonzero⟩ := foo
      specialize this g ?_
      .
        simp
        unfold R'_ at hR
        grw [hR] at g_mem
        simpa using g_mem
      .
        simp at x_g_nonzero
        contradiction
    .
      conv =>
        rhs
        equals (0: V) =>
          simp

      rw [ne_eq, ← Subtype.ext_iff]
      rw [← ne_eq]
      exact hv
  . intro y hy
    rw [← pow_two]
    positivity

lemma Q_R_matrix_pos_def {ι : Type*} [Fintype ι] [DecidableEq ι] {V: Submodule ℝ LipschitzH} [FiniteDimensional ℝ V] (b : Module.Basis ι ℝ ↥V) (R: ℝ) (hR: (R'_ V) ≤ R): (Q_R_matrix b R).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Q_R_lin_hermetian b _)
  intro x hx
  simp [Q_R_matrix]
  conv =>
    rhs
    lhs
    equals (star x) => simp
  rw [star_dotProduct_toMatrix₂_mulVec]
  apply Q_R_pos_on_R'
  . rw [LinearEquiv.map_ne_zero_iff]
    exact hx
  . exact hR

section V_variable

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

/-- The Lipschitz constant `‖(b i).val‖` of the `i`-th vector of the basis `b` of `V`. -/
@[expose]
noncomputable def v_lipschitz_constant {ι : Type*} (b : Module.Basis ι ℝ ↥V) (i : ι) : ℝ :=
  ‖(b i).val‖

/-- The value at the origin `‖(b i).val 1‖` of the `i`-th vector of the basis `b` of `V`. -/
@[expose]
noncomputable def v_origin_norm {ι : Type*} (b : Module.Basis ι ℝ ↥V) (i : ι) : ℝ :=
  ‖(b i).val 1‖

/-- The maximum, over vectors of the basis `b`, of the Lipschitz constant `v_lipschitz_constant`. -/
@[expose]
noncomputable def max_lipschitz {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : ℝ :=
  v_lipschitz_constant b (Finite.exists_max (v_lipschitz_constant b)).choose

/-- The maximum, over vectors of the basis `b`, of the value at the origin `v_origin_norm`. -/
@[expose]
noncomputable def max_origin {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : ℝ :=
  v_origin_norm b (Finite.exists_max (v_origin_norm b)).choose

/-- The `R`-independent constant appearing in `det_bound` (the `(1 + R) ^ 2` factor is kept
separate, in the statement of `det_bound`). -/
@[expose]
noncomputable def det_bound_const {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι ℝ ↥V) : ℝ :=
  ((Module.finrank ℝ ↥V) * max_lipschitz b + (Module.finrank ℝ ↥V) * max_origin b) ^ 2

end V_variable

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.VWrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The bundled subspace `V_Wrapper` and good scales

The `V_Wrapper` class bundling the standing hypotheses on `V`, and the scale functions `f`, `h`
used to locate a scale at which the growth of `V` is almost multiplicative.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Topology

-- Everything in this section freely references fields from V_Wrapper
section V_Wrapper_Section

/-- The standing hypotheses on the subspace `V`, bundled.

This is a `class` purely so that `open V_Wrapper` plus `variable [V_Wrapper]` below lets the whole
section talk about a single fixed `V` by name. Registering the two instance-valued projections
below means `FiniteDimensional`/`Nontrivial` for that `V` are found automatically wherever a
`V_Wrapper` is in scope — including at a call site that merely has `(data : V_Wrapper)` as an
ordinary hypothesis, which is how `theorem_3_23` quantifies over all such subspaces.
(`DecidableEq` needs no field: it follows from `LipschitzH_DecidableEq`.) -/
class V_Wrapper where
  V: Submodule ℝ LipschitzH
  V_finite: FiniteDimensional ℝ V
  V_nontrivial: Nontrivial V
  V_even: Even (Module.finrank ℝ V)

attribute [instance] V_Wrapper.V_finite V_Wrapper.V_nontrivial

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

@[expose]
noncomputable def R' := R'_ V

@[expose]
noncomputable def Q_R_single (R : ℝ) (u: G → ℝ): ℝ := ∑ g ∈ Metric.closedBall 1 R, (u g)^2

@[expose]
noncomputable def dim (V: Type*) [AddCommMonoid V] [Module ℝ V] : ℝ := Module.finrank ℝ V

@[expose]
noncomputable def i₀ : ℕ := Nat.clog 16 ⌈R'⌉₊

omit [Nonempty ι] in
lemma Q_R_matrix_pos_def_i₀ (b : Module.Basis ι ℝ V) (R: ℝ) (hR: 16 ^ (i₀) ≤ R): (Q_R_matrix b R).PosDef := by
  apply Q_R_matrix_pos_def
  simp [i₀] at hR
  have foo := Nat.le_pow_clog (b := 16) (x := ⌈R'_ V⌉₊) (by simp)
  have r_ceil := Nat.le_ceil (R')
  unfold R' at r_ceil
  grw [r_ceil]
  grw [foo]
  simp
  unfold R' at hR
  grw [hR]

@[expose]
noncomputable def f (b : Module.Basis ι ℝ V) (R: ℕ): ℝ := #(S ^ R) * (Q_R_matrix b R).det ^ (dim V)⁻¹
@[expose]
noncomputable def h (b : Module.Basis ι ℝ V) (i: ℕ): ℝ := Real.log (f b (16 ^ i))

-- Matrix.le_iff

omit [Nonempty ι] in
lemma f_monotone_on (bas : Module.Basis ι ℝ V): MonotoneOn (f bas) (Set.Ici ⌈R'⌉₊) := by
  intro x hx y hy hxy
  unfold f
  grw [Finset.pow_subset_pow_right (n := y)]
  .
    rw [mul_le_mul_iff_right₀]
    .
      rw [Real.rpow_le_rpow_iff]
      .
        apply matrix_det_montone
        .
          apply Q_R_matrix_pos_def bas x (by simp [R'] at hx; exact hx)
        .
          unfold Q_R_matrix
          rw [← map_sub]
          rw [← LinearMap.isPosSemidef_iff_posSemidef_toMatrix]
          apply Q_R_lin_sub_pos_semi_def
          simpa using hxy
      .
        have foo := Q_R_matrix_pos_def bas x (by simp [R'] at hx; exact hx)
        grind [foo.det_pos]
      .
        have foo := Q_R_matrix_pos_def bas y (by simp [R'] at hy; exact hy)
        grind [foo.det_pos]
      . simp [dim]
        exact Module.finrank_pos
    .
      simp
      apply Finset.Nonempty.pow
      apply S_nonempty

  . apply Real.rpow_nonneg
    have foo := Q_R_matrix_pos_def bas x (by simp [R'] at hx; exact hx)
    grind [foo.det_pos]
  . apply hGS.one_mem
  . exact hxy

lemma h_montone_on (bas : Module.Basis ι ℝ V): MonotoneOn (h bas) (Set.Ici i₀) := by
  unfold h
  rw [← Function.comp_def]
  apply MonotoneOn.comp
  . apply Real.strictMonoOn_log.monotoneOn
  .
    rw [← Function.comp_def]
    apply MonotoneOn.comp
    . apply f_monotone_on bas
    .
      conv =>
        arg 1
        equals fun n => 16 ^ n =>
          simp
      apply (pow_right_monotone (by simp)).monotoneOn
    . intro a ha
      simp [i₀] at ha
      simp
      rw [Nat.clog_le_iff_le_pow] at ha
      .
        rify at ha
        grw [Nat.le_ceil (a := R')]
        exact ha
      . simp
  .
    intro a ha
    simp
    simp at ha
    simp [f]
    apply mul_pos
    . simp
      apply Finset.Nonempty.pow
      apply S_nonempty
    .
      apply Real.rpow_pos_of_pos
      apply (Q_R_matrix_pos_def_i₀ bas _ ?_).det_pos
      rw [pow_le_pow_iff_right₀]
      . exact ha
      . simp

lemma growth_implies_lim_h (b : Module.Basis ι ℝ V) (d: ℕ) (h_growth: growth_bound b d): Filter.Tendsto (fun (i: ℕ) => (h b i - d * i * Real.log 16)) Filter.atTop Filter.atBot := by
  unfold growth_bound my_expr at h_growth
  have pow_tendsto: Filter.Tendsto (fun n => 16 ^ n) Filter.atTop Filter.atTop := by
    apply StrictMono.tendsto_atTop
    apply pow_right_strictMono₀
    simp

  have log_tendsto := Real.tendsto_log_nhdsGT_zero
  -- Real.tendsto_log_nhdsNE_zero
  have comp_pow := Filter.Tendsto.comp h_growth pow_tendsto
  have comp_log := log_tendsto.comp comp_pow
  simp [Function.comp_def] at comp_log
  rw [← Filter.tendsto_add_atTop_iff_nat i₀] at comp_log
  conv at comp_log =>
    arg 1
    intro x
    rw [Real.log_div (by
      rw [mul_ne_zero_iff]
      refine ⟨?_, ?_⟩
      . simp
        grind [S_nonempty]
      .
        have det_pos := (Q_R_matrix_pos_def_i₀ b (16 ^ (x + i₀)) (by
          rw [add_comm]
          rw [pow_add]
          simp
          norm_cast
          apply Nat.one_le_pow
          simp
        )).det_pos

        rw [Real.rpow_ne_zero]
        . grind
        . grind
        .
          norm_cast
          rw [inv_eq_zero]
          norm_cast
          rw [← ne_eq, Nat.ne_zero_iff_zero_lt]
          apply Module.finrank_pos
    ) (by simp)]
    simp
  simp [h, f, dim]
  simp_rw [← mul_assoc] at comp_log
  rw [← Filter.tendsto_add_atTop_iff_nat i₀]
  simp
  exact comp_log

@[expose]
noncomputable def a (d: ℕ) := 4 * d * Real.log 16

lemma exists_j_0_for_h (b : Module.Basis ι ℝ V) (w d: ℕ) (hw: 0 < w) (hd: 0 < d) (h_growth: growth_bound b d): ∃ j_0: ℕ, h b (i₀ + 3 * w * (j_0 + 1)) - h b (i₀ + 3 * w * j_0) < w * (a d) := by
  by_contra!

  have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h b (i₀ + 3 * w * n)) (m := 0) (n := N) (by simp)
  simp_rw [eq_comm, sub_eq_iff_eq_add] at h_sum

  have h_gt (N: ℕ): h b (i₀ + (3 * w * N)) ≥ 4 * d * w * N * (Real.log 16) + h b i₀ := by
    rw [h_sum]
    grw [← Finset.card_nsmul_le_sum (n := w * (a d))]
    .
      simp
      simp [a]
      grind
    . intro n hn
      apply this

  have h_diff_ge (N: ℕ): h b (i₀ + (3 * w * N)) - d * (i₀ + 3 * w * N) * Real.log 16 ≥ d * (w * N - i₀) * (Real.log 16) + h b i₀ := by
    grw [h_gt]
    simp
    grind

  have rhs_diverges: Filter.Tendsto (fun N => d * (w * N - i₀) * (Real.log 16) + h b i₀) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    rw [Filter.tendsto_mul_const_atTop_of_pos (by positivity)]
    rw [Filter.tendsto_const_mul_atTop_of_pos (by positivity)]
    simp_rw [sub_eq_add_neg]
    apply Filter.tendsto_atTop_add_const_right
    conv =>
      arg 1
      equals fun x => w * x =>
        simp
    rw [Filter.tendsto_const_mul_atTop_of_pos (by positivity)]
    apply Filter.tendsto_id

  apply growth_implies_lim_h at h_growth
  rw [Filter.tendsto_atTop_atBot] at h_growth
  rw [Filter.tendsto_atTop_atTop] at rhs_diverges

  obtain ⟨positive_start, h_positive_start⟩ := rhs_diverges 1
  obtain ⟨negative_start, h_negative_start⟩ := h_growth 0

  specialize h_positive_start (max ⌈positive_start⌉₊ negative_start) (by
    apply le_max_of_le_left
    apply Nat.le_ceil
  )
  -- TODO - why can't grind just solve this?
  specialize h_negative_start (i₀ + 3 * w * max ⌈positive_start⌉₊ negative_start) (by
    conv =>
      lhs
      equals 0 + negative_start => simp
    apply Nat.add_le_add
    . simp
    .
      conv =>
        lhs
        equals 1 * negative_start => simp
      apply Nat.mul_le_mul
      . grind
      . simp
  )

  have h_ge_one := h_diff_ge (max ⌈positive_start⌉₊ negative_start)
  norm_cast at h_ge_one
  norm_cast at h_positive_start
  grw [← h_positive_start] at h_ge_one
  grind

structure Lemma3_24_data (b : Module.Basis ι ℝ V) (d w: ℕ) where
  i_1 : ℕ
  i_2 : ℕ
  i_1_ge: i₀ ≤ i_1
  i_2_ge: i₀ ≤ i_2
  i_1_pos: 0 < i_1
  i_2_pos: 0 < i_2
  i_diff_mem: i_2 - i_1 ∈ Set.Ioo w (3 * w)
  h_diff_lt_w: h b (i_2 + 1) - h b i_1 < w * (a d)
  first_h_i: h b (i_1 + 1) - h b i_1 < (a d)
  second_h_i : h b (i_2 + 1) - h b i_2 < (a d)

lemma lemma_3_24 (b : Module.Basis ι ℝ V) (w d: ℕ) (hw: 0 < w) (hd: 0 < d) (h_growth: growth_bound b d): Nonempty (Lemma3_24_data b d w) := by
  obtain ⟨j_0, h_j_0⟩ := exists_j_0_for_h b w d hw hd h_growth
  let m := i₀ + 3 * w * j_0

  have exists_i1: ∃ i_1: ℕ, i_1 ∈ Set.Ico m (m + w) ∧ h b (i_1 + 1) - h b i_1 < (a d) := by
    by_contra!

    have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h b (m + n)) (m := 0) (n := w) (by simp)
    simp only [Nat.Ico_zero_eq_range, add_zero, forall_const] at h_sum

    have h_m_diff_le: h b (m + w) - h b (m) ≤ h b (i₀ + 3 * w * (j_0 + 1)) - h b (i₀ + 3 * w * (j_0)) := by
      apply sub_le_sub
      .
        apply h_montone_on b
        . simp [m]
          grind
        . simp
        . simp [m]
          grind
      . apply h_montone_on b
        . simp [m]
        . simp [m]
        . simp [m]

    have h_le_w_a_d : h b (m  + w) - h b m ≤ w * (a d) := by
      grw [h_m_diff_le]
      grw [h_j_0]

    have w_a_le_h : w * (a d) ≤ h b (m + w) - h b m := by
      rw [h_sum.symm]
      grw [← Finset.card_nsmul_le_sum (n := (a d))]
      . simp
      . intro x hx
        apply this
        simpa using hx
    grind

  -- TODO - can this be deduplicated with exists_i1 ?
  have exists_i2: ∃ i_2: ℕ, i_2 ∈ Set.Ico (m + 2*w) (m + 3 * w) ∧ h b (i_2 + 1) - h b i_2 < (a d) := by
    by_contra!

    have h_sum (N: ℕ) := Finset.sum_Ico_sub (f := fun n => h b (m + n)) (m := (2 * w)) (n := (3 * w)) (by grind)
    simp only [Nat.Ico_zero_eq_range, add_zero, forall_const] at h_sum

    have h_m_diff_le: h b (m + 3 * w) - h b (m + 2 * w) ≤ h b (i₀ + 3 * w * (j_0 + 1)) - h b (i₀ + 3 * w * (j_0)) := by
      apply sub_le_sub
      .
        apply h_montone_on b
        . simp [m]
          grind
        . simp
        . simp [m]
          grind
      . apply h_montone_on b
        . simp [m]
        . simp [m]
          grind
        . simp [m]

    have h_le_w_a_d : h b (m  + 3 * w) - h b (m + 2 * w) ≤ w * (a d) := by
      grw [h_m_diff_le]
      grw [h_j_0]

    have w_a_le_h : w * (a d) ≤ h b (m + 3 * w) - h b (m + 2* w) := by

      rw [h_sum.symm]
      grw [← Finset.card_nsmul_le_sum (n := (a d))]
      . simp
        rw [← Nat.sub_mul]
        simp
      . intro x hx
        apply this
        simp
        simp at hx
        exact hx
    grind

  obtain ⟨i_1, h_i_1⟩ := exists_i1
  obtain ⟨i_2, h_i_2⟩ := exists_i2
  have diff_i_lt: h b (i_2 + 1) - h b i_1 < w * (a d) := by
    grw [h_montone_on b _ _ (b := i₀ + 3 * w * (j_0 + 1))]
    .
      apply LE.le.trans_lt ?_ h_j_0
      apply sub_le_sub_left
      apply h_montone_on b
      . simp
      . simp
        grind
      . grind
    . simp at h_i_2
      grind
    . simp
      simp at h_i_2
      grind
    . simp [m]

  have foo := h_i_1.1
  simp at foo
  have i_1_ge := foo.1
  simp [m] at i_1_ge
  have i_0_pos: 0 < i₀ := by
    simp [i₀]
    apply Nat.clog_pos
    . simp
    . simp [R']
      rw [Nat.lt_ceil]
      simp [R'_]
      have r_pos := R'_pos V
      exact r_pos
  apply Nonempty.intro
  exact {
    i_1 := i_1
    i_2 := i_2
    i_1_ge := by grind
    i_2_ge := by grind
    i_1_pos := by grind
    i_2_pos := by grind
    i_diff_mem := by grind
    h_diff_lt_w := diff_i_lt
    first_h_i := h_i_1.2
    second_h_i := h_i_2.2
  }

-- Controlled cover

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Packing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Ball packing at a good scale

The packing sets `B`, `B_half`, `B_3` at a good scale, their finiteness and disjointness, and
the intersection-multiplicity bound `card_B_le_exp_wa`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Topology

section V_Wrapper_Section

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {b : Module.Basis ι ℝ V}

variable {b : Module.Basis ι ℝ V}

structure GoodScalesData (b : Module.Basis ι ℝ V) where
  w: ℕ
  d: ℕ
  hw: 0 < w
  hd: 0 < d
  w_gt: 4 < w
  h_growth: growth_bound b d

@[expose]
noncomputable def GoodScales (data: GoodScalesData b) := Classical.choice (lemma_3_24 b data.w data.d data.hw data.hd data.h_growth)

@[expose] noncomputable def R_1 (data: GoodScalesData b) := 2 * 16^(GoodScales data).i_1
@[expose] noncomputable def R_2 (data: GoodScalesData b) := 16^(GoodScales data).i_2

-- TODO - does it matter than 'Metric.maximalSeparatedSet' uses 'R_1 < dist' instead of 'R_1 <= dist' ?
@[expose] def X_j (data: GoodScalesData b) := Metric.maximalSeparatedSet (R_1 data) ((Metric.closedBall (1: G) (R_2 data)))
-- A collection of disjoint balls that cover the ball R_2
@[expose] def B (data: GoodScalesData b) := (fun a => Metric.closedBall a (R_1 data)) '' (X_j data)
@[expose] def B_half (data: GoodScalesData b) := (fun a => Metric.closedBall a (R_1 data / 2)) '' (X_j data)
@[expose]
def B_3 (data: GoodScalesData b) := (fun a => Metric.closedBall a (3 * (R_1 data + 1))) '' (X_j data)

lemma X_j_finite (data: GoodScalesData b): (X_j data).Finite := by
  apply Set.Finite.subset (finite_closed_ball (1 : G) (R_2 data))
  simp [X_j]
  apply Metric.maximalSeparatedSet_subset

lemma B_ball_injective_on (data: GoodScalesData b) (R: ℝ) (R_pos: 0 ≤ R) (hR: R ≤ R_1 data): Set.InjOn (fun a => Metric.closedBall a (R)) (X_j data) := by
  intro a ha b hb hab
  by_contra!
  simp at hab
  simp [X_j] at ha hb

  have sep := Metric.isSeparated_maximalSeparatedSet (ε := (R_1 data)) (A := (Metric.closedBall (1 : G) ↑(R_2 data)))
  specialize sep ha hb this

  have b_mem: b ∈ Metric.closedBall a ((R)) := by
    rw [hab]
    simp
    grind

  simp at b_mem
  simp [edist, PseudoMetricSpace.edist] at sep
  rw [dist_comm] at b_mem
  simp [dist] at b_mem
  norm_cast at b_mem
  rify at sep
  grw [b_mem] at sep
  norm_cast at sep
  grind

lemma B_covers_R2 (data: GoodScalesData b): Metric.closedBall 1 (R_2 data) ⊆ ⋃₀ (B data) := by
  by_contra!
  rw [Set.not_subset] at this
  obtain ⟨x, x_mem, x_not_mem⟩ := this

  -- Metric.maximalSeparatedSet_subset
  have card_le := Metric.encard_le_of_isSeparated (C := (X_j data) ∪ {x}) (ε := (R_1 data)) (A := ( (Metric.closedBall 1 (R_2 data)))) ?_ ?_ ?_
  .
    simp [X_j] at card_le
    rw [Set.encard_insert_of_notMem] at card_le
    rw [Set.Finite.encard_eq_coe_toFinset_card] at card_le
    . norm_cast at card_le

      grind
    .
      apply Set.Finite.subset (s := Metric.closedBall 1 (R_2 data))
      . apply finite_closed_ball
      . apply Metric.maximalSeparatedSet_subset
    .
      simp at x_not_mem
      simp only [B, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        not_lt, X_j] at x_not_mem

      by_contra!
      specialize x_not_mem x this
      simp [R_1] at x_not_mem
  .
    apply Set.union_subset
    . simp [X_j]
      grw [Metric.maximalSeparatedSet_subset]
    .
      simp at x_mem
      simpa using x_mem
  .
    simp
    apply Metric.IsSeparated.insert
    . simp [X_j]
      apply Metric.isSeparated_maximalSeparatedSet
    . intro y hy hxy
      simp [B] at x_not_mem
      specialize x_not_mem y hy
      simp [edist, PseudoMetricSpace.edist]
      simp [dist] at x_not_mem
      exact x_not_mem
  .
    rw [← lt_top_iff_ne_top]
    grw [Metric.packingNumber_le_encard_self]
    simp
    apply finite_closed_ball

lemma B_half_disjoint (data: GoodScalesData b): (B_half data).PairwiseDisjoint id := by
  simp [Set.pairwiseDisjoint_iff]
  intro X hX Y hY hXY
  obtain ⟨a, ha⟩ := hXY
  simp [B_half] at hX hY
  obtain ⟨x, x_mem, hx⟩ := hX
  obtain ⟨y, y_mem, hy⟩ := hY

  by_cases x_eq_y : x = y
  .
    rw [x_eq_y] at hx
    rw [← hx, ← hy]

  rw [← hx, ← hy] at ha
  simp at ha
  obtain ⟨a_dist_x, a_dist_y⟩ := ha

  simp [X_j] at x_mem
  have is_sep := Metric.isSeparated_maximalSeparatedSet (ε := ((R_1 data))) (A := Metric.closedBall (1: G) (R_2 data))

  unfold Metric.IsSeparated Set.Pairwise at is_sep
  have x_sep := is_sep x_mem y_mem x_eq_y
  simp at x_sep

  have x_y_dist_bad := dist_triangle x a y
  rw [dist_comm x a] at x_y_dist_bad
  grw [a_dist_x, a_dist_y] at x_y_dist_bad
  simp at x_y_dist_bad
  -- TODO - we need a lemma that edist = ↑dist
  simp [edist, PseudoMetricSpace.edist] at x_sep
  simp [dist] at x_y_dist_bad
  grind

-- Intersection multiplicity. See https://www.math.ucdavis.edu/~kapovich/EPR/kapovich_drutu.pdf page 24 for the definition
-- (search for 'multiplicity')
@[expose]
noncomputable def InterMult_f  (S: Set (Set G)) := (fun A => (Set.encard A).toNat) '' { A: Set (Set G) | A ⊆ S ∧ ⋂₀ A ≠ ∅ }
@[expose]
noncomputable def InterMult (S: Set (Set G)) := sSup (InterMult_f S)

lemma B_finite (data: GoodScalesData b): (B data).Finite := by
  simp [B]
  apply Set.Finite.image
  simp [X_j]
  apply Set.Finite.subset ?_ (Metric.maximalSeparatedSet_subset)
  apply finite_closed_ball

@[expose] noncomputable def B_finsets (data: GoodScalesData b): Finset (Finset G) := Finset.image ((fun a => (finite_closed_ball a (R_1 data )).toFinset)) (X_j_finite data).toFinset

-- TODO - combine this with 'B_half'
@[expose]
noncomputable def B_half_finsets (data: GoodScalesData b): Finset (Finset G) := Finset.image ((fun a => (finite_closed_ball a (R_1 data / 2)).toFinset)) (X_j_finite data).toFinset

@[expose] noncomputable def B_r (r: ℝ) := (finite_closed_ball 1 r).toFinset
@[expose] noncomputable def B_c_r (g: G) (r: ℝ) := (finite_closed_ball g r).toFinset

omit v_wrapper_inst in
lemma B_c_r_eq_smul (a: G) (r: ℝ): B_c_r a r = (MulOpposite.op a) • B_r r := by
  rw [B_c_r, B_r]
  rw [← Finset.coe_inj]
  simp

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Poincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Poincaré inequality

`poincare_inequality` and the packing-averaged form `lemma_3_25_poincare`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Topology

section V_Wrapper_Section

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {b : Module.Basis ι ℝ V}

@[expose]
noncomputable def f_avg (R: ℝ) (f : G → ℝ) := (#((finite_closed_ball 1 R).toFinset) : ℝ)⁻¹ * ∑ y ∈ (finite_closed_ball 1 R).toFinset, f y
@[expose] noncomputable def f_avg_c (g: G) (R: ℝ) (f : G → ℝ) := (#((finite_closed_ball 1 R).toFinset) : ℝ)⁻¹ * ∑ y ∈ B_c_r g R, f y

@[expose]
noncomputable def deriv_sq_R (f: G → ℝ) (x: G) := ∑ s ∈ S, (f (x * s) - f x)^2

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Lemma326
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Lemma 3.26 and basis changes

`lemma_3_26_a` together with the behaviour of `Q_R_matrix` and `growth_bound` under a change of
basis.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

open scoped Finset
open scoped Pointwise

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped Topology

section V_Wrapper_Section

open V_Wrapper

variable [v_wrapper_inst: V_Wrapper]
include v_wrapper_inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {b : Module.Basis ι ℝ V}

@[expose]
noncomputable def J (data: GoodScalesData b) := #((X_j_finite data).toFinset)
@[expose]
noncomputable def phi (data: GoodScalesData b): V →ₗ[ℝ] EuclideanSpace ℝ (B_finsets data) := {
  toFun := fun u => WithLp.toLp 2 (fun (j: B_finsets data) => ((#j.val : ℝ)⁻¹) * ∑ x ∈ j.val, u.val x)
  map_add' := by
    intro x y
    simp
    simp_rw [Finset.sum_add_distrib]
    simp_rw [mul_add]
    ext a
    simp
  map_smul' := by
    intro k V
    ext a
    simp
    simp_rw [← Finset.mul_sum]
    ring
}

@[expose] def C: ℝ := 32 * (#S)

end V_Wrapper_Section

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Vendor_Carleson_ToMathlib_MeasureTheory_Function_LpSeminorm_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Vendored from the Carleson project

Verbatim port of `Carleson/ToMathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` from
<https://github.com/fpvandoorn/carleson> (branch `young-add-group`).

`AEMeasurable` variants of the `AEStronglyMeasurable` lemmas about `eLpNorm` and pushforward
measures, needed by the vendored Young convolution inequality.
-/

set_option linter.style.header false

section

open MeasureTheory
open scoped ENNReal

variable {α ε E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε]

namespace MeasureTheory

section MapMeasure

variable {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → E}

theorem eLpNormEssSup_map_measure' [MeasurableSpace E] [OpensMeasurableSpace E]
    (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  essSup_map_measure hg.enorm hf

theorem eLpNorm_map_measure' [MeasurableSpace E] [OpensMeasurableSpace E]
    (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · aesop
  by_cases hp_top : p = ∞
  · rw [hp_top, eLpNorm_exponent_top]
    exact eLpNormEssSup_map_measure' hg hf
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp_zero hp_top]
  rw [lintegral_map' (hg.enorm.pow_const p.toReal) hf]
  rfl

theorem eLpNorm_comp_measurePreserving' {ν : Measure β} [MeasurableSpace E]
    [OpensMeasurableSpace E] (hg : AEMeasurable g ν) (hf : MeasurePreserving f μ ν) :
    eLpNorm (g ∘ f) p μ = eLpNorm g p ν :=
  Eq.symm <| hf.map_eq ▸ eLpNorm_map_measure' (hf.map_eq ▸ hg) hf.aemeasurable

end MapMeasure

end MeasureTheory
end
end

section
-- module Solutions.OAIQ093_PR.Vendor_Carleson_ToMathlib_MeasureTheory_Measure_Haar_Unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Vendored from the Carleson project

Verbatim port of `Carleson/ToMathlib/MeasureTheory/Measure/Haar/Unique.lean` from
<https://github.com/fpvandoorn/carleson> (branch `young-add-group`).

Generalizes Mathlib's `IsHaarMeasure.isInvInvariant_of_regular` (which requires a commutative
group) to any regular bi-invariant Haar measure. This is what makes the non-abelian version of
Young's convolution inequality go through.
-/

set_option linter.style.header false

section

open MeasureTheory Measure
open scoped ENNReal

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

namespace MeasureTheory
namespace Measure

-- This is a generalization of `IsHaarMeasure.isInvInvariant_of_regular`, using the same proof.
/-- Any regular bi-invariant Haar measure is invariant under inversion. -/
@[to_additive /-- Any regular bi-invariant additive Haar measure is invariant under negation. -/]
instance (priority := 100) IsHaarMeasure.isInvInvariant_of_isMulRightInvariant (μ : Measure G)
    [μ.IsHaarMeasure] [LocallyCompactSpace G] [μ.IsMulRightInvariant] [μ.Regular] :
    IsInvInvariant μ := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul_of_regular μ.inv μ
  have : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    simpa [map_map continuous_inv.measurable continuous_inv.measurable] using this
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 this
  have : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective this
  rw [hc, this, one_smul]

end Measure
end MeasureTheory
end
end

section
-- module Solutions.OAIQ093_PR.Vendor_Carleson_ToMathlib_MeasureTheory_Integral_MeanInequalities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Vendored from the Carleson project

Port of `Carleson/ToMathlib/MeasureTheory/Integral/MeanInequalities.lean` from
<https://github.com/fpvandoorn/carleson> (branch `young-add-group`, commit `3b35c86`), which is
the non-abelian generalization of Young's convolution inequality.

The `eLpNorm_Ioc_convolution_le_*` theorems at the end of the upstream file are omitted: they are
unused here and would drag in the whole `Carleson/ToMathlib/MeasureTheory/Integral/Periodic.lean`
(`liftIoc`) development.
-/

set_option linter.style.header false

section

open NNReal ENNReal MeasureTheory Finset

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace ENNReal

-- Add after `lintegral_prod_norm_pow_le`
/-- A version of Hölder with multiple arguments, allowing `∞` as an exponent. -/
theorem lintegral_prod_norm_pow_le' {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Finset ι} {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    {p : ι → ℝ≥0∞} (hp : ∑ i ∈ s, (p i)⁻¹ = 1) :
    ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  classical
  revert hp hf
  refine Finset.strongInduction (fun s hs hf hp ↦ ?_) s (p := fun s ↦
    (∀ i ∈ s, AEMeasurable (f i) μ) → (∑ i ∈ s, (p i)⁻¹ = 1) →
    ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ)
  by_cases exists_top : ∃ i₀ ∈ s, p i₀ = ∞    -- If one of the exponents is `∞`, we reduce to the
  · obtain ⟨i₀, hi₀, pi₀_eq_top⟩ := exists_top -- case without it and use the inductive hypothesis
    calc ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ
      _ = ∫⁻ (a : α), f i₀ a * ∏ i ∈ s.erase i₀, f i a ∂μ :=
        lintegral_congr (fun a ↦ (Finset.mul_prod_erase s (f · a) hi₀).symm)
      _ ≤ eLpNorm (f i₀) (p i₀) μ * ∫⁻ (a : α), ∏ i ∈ s.erase i₀, f i a ∂μ := by
        rw [← lintegral_const_mul'', pi₀_eq_top]
        · exact lintegral_mono_ae <| (ae_le_essSup (f i₀)).mono (fun a ha ↦ mul_le_mul_left ha _)
        · exact Finset.aemeasurable_fun_prod _ (fun i hi ↦ hf i (Finset.mem_of_mem_erase hi))
      _ ≤ eLpNorm (f i₀) (p i₀) μ * ∏ i ∈ s.erase i₀, eLpNorm (f i) (p i) μ := by
        apply mul_right_mono
        apply hs (s.erase i₀) (s.erase_ssubset hi₀) (fun i hi ↦ hf i (s.erase_subset i₀ hi))
        simpa [← Finset.add_sum_erase s _ hi₀, pi₀_eq_top] using hp
      _ = _ := Finset.mul_prod_erase s (fun i ↦ eLpNorm (f i) (p i) μ) hi₀
  -- If all exponents are finite, we're in the case covered by `ENNReal.lintegral_prod_norm_pow_le`
  have hf' : ∀ i ∈ s, AEMeasurable (fun a ↦ ((f i a) ^ (p i).toReal)) μ :=
    fun i hi ↦ (hf i hi).pow_const (p i).toReal
  have hp₁ : ∑ i ∈ s, (p i).toReal⁻¹ = 1 := by
    simp_rw [← (ENNReal.toReal_eq_one_iff 1).mpr rfl, ← ENNReal.toReal_inv]
    suffices (∑ x ∈ s, (p x)⁻¹).toReal = ∑ x ∈ s, (p x)⁻¹.toReal by rw [← this, hp]
    refine ENNReal.toReal_sum (fun i hi eq_top ↦ ?_)
    exact ENNReal.one_ne_top <| hp ▸ ENNReal.sum_eq_top.mpr ⟨i, hi, eq_top⟩
  have hp₂ : ∀ i ∈ s, 0 ≤ (p i).toReal⁻¹ := by intros; positivity
  have p_ne_0 : ∀ i ∈ s, p i ≠ 0 :=
    fun i hi eq0 ↦ one_ne_top <| hp.symm.trans <| ENNReal.sum_eq_top.mpr ⟨i, hi, by simp [eq0]⟩
  have p_ne_top : ∀ i ∈ s, p i ≠ ∞ := fun i hi h ↦ exists_top ⟨i, hi, h⟩
  convert ENNReal.lintegral_prod_norm_pow_le s hf' hp₁ hp₂ with a i₀ hi₀ i hi
  · rw [← ENNReal.rpow_mul, mul_inv_cancel₀, rpow_one]
    exact ENNReal.toReal_ne_zero.mpr ⟨p_ne_0 i₀ hi₀, (exists_top ⟨i₀, hi₀, ·⟩)⟩
  · simp [eLpNorm, eLpNorm', p_ne_0 i hi, p_ne_top i hi]

/-- **Hölder's inequality** for functions `α → ℝ≥0∞`, using exponents in `ℝ≥0∞` -/
theorem lintegral_mul_le_eLpNorm_mul_eLqNorm {p q : ℝ≥0∞} (hpq : p.HolderConjugate q)
    {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ (a : α), (f * g) a ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  -- adaptation note: `ENNReal.HolderConjugate` is now a class (`HolderTriple p q 1`), so the
  -- upstream dot-notation API (`hpq.symm`, `hpq.conj_eq`, `hpq.toReal_of_ne_top`) is gone.
  haveI := hpq
  simp_rw [Pi.mul_apply]
  have hp0 : p ≠ 0 := HolderConjugate.ne_zero p q
  have hq0 : q ≠ 0 := HolderConjugate.ne_zero q p
  rcases eq_or_ne p ∞ with hp | hp
  · have hq1 : q = 1 := (HolderConjugate.eq_top_iff_eq_one p q).mp hp
    calc ∫⁻ a, f a * g a ∂μ
      _ ≤ ∫⁻ a, essSup f μ * g a ∂μ :=
        lintegral_mono_ae <| (ae_le_essSup f).mono fun a ha ↦ mul_le_mul_left ha _
      _ = essSup f μ * ∫⁻ a, g a ∂μ := lintegral_const_mul'' _ hg
      _ = _ := by simp [eLpNorm, eLpNorm', eLpNormEssSup, hp, hq1]
  rcases eq_or_ne q ∞ with hq | hq
  · have hp1 : p = 1 := (HolderConjugate.eq_top_iff_eq_one q p).mp hq
    calc ∫⁻ a, f a * g a ∂μ
      _ ≤ ∫⁻ a, f a * essSup g μ ∂μ :=
        lintegral_mono_ae <| (ae_le_essSup g).mono fun a ha ↦ mul_le_mul_right ha _
      _ = (∫⁻ a, f a ∂μ) * essSup g μ := lintegral_mul_const'' _ hf
      _ = _ := by simp [eLpNorm, eLpNorm', eLpNormEssSup, hp1, hq]
  -- Both exponents are finite: reduce to the real-exponent version.
  have hpt : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hqt : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hsum : p.toReal⁻¹ + q.toReal⁻¹ = 1 := by
    rw [← ENNReal.toReal_inv, ← ENNReal.toReal_inv,
      ← ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hp0) (ENNReal.inv_ne_top.mpr hq0),
      HolderConjugate.inv_add_inv_eq_one p q, ENNReal.toReal_one]
  have hpq' : p.toReal.HolderConjugate q.toReal := by
    refine Real.holderConjugate_iff.mpr ⟨(inv_lt_one₀ hpt).mp ?_, hsum⟩
    have : 0 < q.toReal⁻¹ := by positivity
    linarith
  convert ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq' hf hg
  all_goals simp [eLpNorm, eLpNorm', hp, hq, hp0, hq0]

end ENNReal


section Convolution

open scoped Convolution

-- Used in the proof of Young's convolution inequality
lemma r_sub_p_nonneg {p q r : ℝ} (p0 : 0 < p) (hq : 1 ≤ q) (r0 : 0 < r)
    (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) : 0 ≤ r - p := by
  rw [sub_nonneg, ← inv_le_inv₀ r0 p0, ← add_le_add_iff_right, hpqr]
  gcongr
  exact (inv_le_one₀ (lt_of_lt_of_le one_pos hq)).mpr hq

namespace ENNReal

universe u𝕜 uG uE uE' uF

variable {𝕜 : Type u𝕜} {G : Type uG} [MeasurableSpace G] {μ : Measure G}
  {E : Type uE} {E' : Type uE'} {F : Type uF}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  {f : G → E} {g : G → E'}

-- Used in the proof of `enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm`
open ENNReal in
lemma eLpNorm_eq_eLpNorm_rpow (h : G → E) {r e : ℝ} (r0 : 0 < r) (e0 : 0 < e)
    (re0 : 0 ≤ r - e) (μ0 : μ ≠ 0) :
    eLpNorm (‖h ·‖ₑ ^ ((r - e) / r)) (ENNReal.ofReal (e * r) / ENNReal.ofReal (r - e)) μ =
    eLpNorm h (ENNReal.ofReal e) μ ^ ((r - e) / r) := by
  have er_pos : 0 < e * r := _root_.mul_pos e0 r0
  by_cases exp_zero : 0 = r - e
  · simp [eLpNorm, eLpNorm', ← exp_zero, er_pos.not_ge, eLpNormEssSup_const _ μ0]
  have r_sub_e_pos : 0 < r - e := lt_of_le_of_ne re0 exp_zero
  have lt_top : ENNReal.ofReal (e * r) / ENNReal.ofReal (r - e) < ∞ :=
    div_lt_top ofReal_ne_top <| (not_iff_not.mpr ofReal_eq_zero).mpr r_sub_e_pos.not_ge
  simp only [eLpNorm, eLpNorm', reduceIte, div_eq_zero_iff, ofReal_eq_zero, ofReal_ne_top,
    lt_top.ne, er_pos.not_ge, e0.not_ge, or_self, enorm_eq_self, ← rpow_mul]
  -- adaptation note: `field_simp` no longer sees through the `ENNReal.toReal` of the exponents,
  -- so we compute them by hand first.
  have hrne : r - e ≠ 0 := r_sub_e_pos.ne'
  have hene : e ≠ 0 := e0.ne'
  have hrne0 : r ≠ 0 := r0.ne'
  have h2 : (0 : ℝ) ≤ e * r := by positivity
  congr
  · ext
    congr
    simp only [ENNReal.toReal_div, ENNReal.toReal_ofReal h2,
      ENNReal.toReal_ofReal e0.le, ENNReal.toReal_ofReal r_sub_e_pos.le]
    field_simp
  · simp only [ENNReal.toReal_div, ENNReal.toReal_ofReal h2,
      ENNReal.toReal_ofReal e0.le, ENNReal.toReal_ofReal r_sub_e_pos.le]
    field_simp

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
variable {L : E →L[𝕜] E' →L[𝕜] F}

-- Used to handle trivial case `c ≤ 0` when proving versions of Young's convolution inequality
-- assuming `∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖)`
theorem convolution_zero_of_c_nonpos [AddGroup G] {f : G → E} {g : G → E'} {c : ℝ}
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (hc : c ≤ 0) : f ⋆[L, μ] g = 0 := by
  have : ∀ (x y : G), L (f x) (g y) = 0 :=
    fun x y ↦ norm_le_zero_iff.mp <| (hL x y).trans <| mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg (f x))) (norm_nonneg (g y))
  unfold MeasureTheory.convolution
  simp only [this, integral_zero]
  rfl

-- Auxiliary inequality used to prove inequalities with simpler conditions on f and g.
theorem eLpNorm_top_convolution_le_aux [AddGroup G] {p q : ℝ≥0∞}
    (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'} (hf : AEMeasurable (‖f ·‖ₑ) μ)
    (hg : ∀ x : G, AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (hg' : ∀ x : G, eLpNorm (‖g <| x - ·‖ₑ) q μ = eLpNorm (‖g ·‖ₑ) q μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  by_cases hc : c ≤ 0
  · simp [convolution_zero_of_c_nonpos hL hc]
  push_neg at hc
  rw [eLpNorm_exponent_top, eLpNormEssSup]
  refine essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun x ↦ ?_)
  apply le_trans <| enorm_integral_le_lintegral_enorm _
  calc ∫⁻ y, ‖(L (f y)) (g (x - y))‖ₑ ∂μ
    _ ≤ ∫⁻ y, ENNReal.ofReal c * ‖f y‖ₑ * ‖g (x - y)‖ₑ ∂μ := by
      simp_rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc.le]
      refine lintegral_mono (fun y ↦ ?_)
      rw [← ENNReal.ofReal_mul <| mul_nonneg hc.le (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal <| hL y (x - y)
    _ ≤ _ := by
      simp_rw [mul_assoc, lintegral_const_mul' _ _ ofReal_ne_top]
      simpa [hg' x] using
        mul_right_mono (ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm hpq hf (hg x))

variable [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]
  [μ.IsAddHaarMeasure] [LocallyCompactSpace G] [SecondCountableTopology G]

-- Auxiliary inequality used to prove versions with simpler conditions on `f` and `g`
open ENNReal in
omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm_aux
    [μ.IsNegInvariant] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) {f : G → E} {g : G → E'}
    (hf : AEMeasurable (‖f ·‖ₑ) μ) (hg : ∀ x : G, AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤
      .ofReal c * eLpNorm (fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)) (.ofReal r) μ *
      ((eLpNorm f (.ofReal p) μ) ^ ((r - p) / r) *
      (eLpNorm g (.ofReal q) μ) ^ ((r - q) / r)) := by
  by_cases hc : c ≤ 0
  · simp [convolution_zero_of_c_nonpos hL hc]
  push_neg at hc
  by_cases μ0 : μ = 0
  · simp [μ0, MeasureTheory.convolution]
  push_neg at μ0
  let F (i : Fin 3) : G → ℝ≥0∞ :=
    match i with
    | 0 => fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)
    | 1 => fun y ↦ ‖f y‖ₑ ^ ((r - p) / r)
    | 2 => fun y ↦ ‖g (x - y)‖ₑ ^ ((r - q) / r)
  let P : Fin 3 → ℝ≥0∞ :=
    ![.ofReal r, .ofReal (p * r) / .ofReal (r - p), .ofReal (q * r) / .ofReal (r - q)]
  have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  have q0 : 0 < q := lt_of_lt_of_le one_pos hq
  have r0 : 0 < r := lt_of_lt_of_le one_pos hr
  have rp0 : 0 ≤ r - p := r_sub_p_nonneg p0 hq r0 hpqr
  have rq0 : 0 ≤ r - q := r_sub_p_nonneg q0 hp r0 <| add_comm p⁻¹ q⁻¹ ▸ hpqr
  calc
    _ ≤ ∫⁻ y, ‖L (f y) (g (x - y))‖ₑ ∂μ := by
      exact enorm_integral_le_lintegral_enorm (fun y ↦ L (f y) (g (x - y)))
    _ ≤ ∫⁻ y, .ofReal c * ‖f y‖ₑ * ‖g (x - y)‖ₑ ∂μ := by
      refine lintegral_mono (fun y ↦ ?_)
      rw [← enorm_norm, ← enorm_norm (f y), ← enorm_norm (g (x - y)), mul_assoc, ← enorm_mul]
      rw [Real.enorm_of_nonneg (norm_nonneg _)]
      rw [Real.enorm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      rw [← ENNReal.ofReal_mul hc.le]
      exact ENNReal.ofReal_le_ofReal <| le_of_le_of_eq (hL y (x - y)) (mul_assoc _ _ _)
    _ = ∫⁻ y, ENNReal.ofReal c * ‖f y‖ₑ ^ (p / r + (r - p) / r) *
                           ‖g (x - y)‖ₑ ^ (q / r + (r - q) / r) ∂μ := by
      refine lintegral_congr (fun y ↦ ?_)
      suffices p / r + (r - p) / r = 1 ∧ q / r + (r - q) / r = 1 by simp [this]
      rw [← add_div, ← add_div, add_sub_cancel, add_sub_cancel, and_self, div_self r0.ne.symm]
    _ = ∫⁻ y, ENNReal.ofReal c * (F 0) y * ((F 1) y * (F 2) y) ∂μ := by
      refine lintegral_congr (fun y ↦ ?_)
      simp_rw [F, mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr (one_pos.le.trans hr))]
      repeat rw [← ENNReal.rpow_mul, ENNReal.rpow_add_of_nonneg]
      · ring_nf
      all_goals positivity
    _ = ∫⁻ y, ENNReal.ofReal c * ∏ i ∈ Finset.univ, (F i) y ∂μ := by
      simp [mul_assoc, Fin.prod_univ_succ]
    _ ≤ ENNReal.ofReal c * eLpNorm (F 0) (P 0) μ *
          (eLpNorm (F 1) (P 1) μ * eLpNorm (F 2) (P 2) μ) := by
      rw [lintegral_const_mul' _ _ ofReal_ne_top, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le (a := ENNReal.ofReal c))
      -- Check that the assumptions of `lintegral_prod_norm_pow_le'` apply
      have ae_meas_g := hg x
      have := (hf.pow_const p).mul (ae_meas_g.pow_const q)
      have ae_meas : ∀ i ∈ Finset.univ, AEMeasurable (F i) μ :=
        fun ⟨v, _⟩ _ ↦ by interval_cases v <;> exact AEMeasurable.pow_const (by assumption) _
      suffices ∑ i, (P i)⁻¹ = 1 by
        simpa [Fin.prod_univ_succ] using lintegral_prod_norm_pow_le' ae_meas this
      -- It remains to check ∑ (P i)⁻¹ = 1, which is trivial, aside from technicalities in `ℝ≥0∞`
      simp_rw [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        Finset.univ_eq_empty, Finset.sum_empty, add_zero, P, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Matrix.cons_val_zero]
      repeat rw [ENNReal.inv_div]
      · rw [ofReal_sub r p0.le, ofReal_sub r q0.le, ofReal_mul p0.le, ofReal_mul q0.le]
        repeat rw [ENNReal.sub_div (by simp [p0, q0, r0])]
        nth_rewrite 2 5 [← one_mul (ENNReal.ofReal r)]
        nth_rewrite 2 [← mul_one (ENNReal.ofReal p), ← mul_one (ENNReal.ofReal q)]
        repeat rw [ENNReal.mul_div_mul_right _ _ (by simp [r0]) (by simp), one_div]
        repeat rw [ENNReal.mul_div_mul_left _ _ (by simp [p0, q0]) (by simp), one_div]
        rw [← ENNReal.ofReal_one, ← congr_arg ENNReal.ofReal (sub_eq_iff_eq_add'.mpr hpqr)]
        rw [ofReal_sub _ (inv_pos.mpr r0).le, ← add_assoc]
        rw [ofReal_add (inv_pos.mpr p0).le (inv_pos.mpr q0).le]
        have : AddLECancellable (ENNReal.ofReal r)⁻¹ := ENNReal.cancel_of_ne (by simp [r0])
        rw [← this.add_tsub_assoc_of_le, ← this.add_tsub_assoc_of_le, this.add_tsub_cancel_left]
        · rw [ofReal_inv_of_pos p0, ofReal_inv_of_pos q0, ofReal_inv_of_pos r0]
        all_goals exact ENNReal.inv_le_inv.mpr <| ofReal_le_ofReal (sub_nonneg.mp (by assumption))
      all_goals simp [p0, q0, r0]
    _ = _ := by
      congr
      · exact eLpNorm_eq_eLpNorm_rpow f r0 p0 rp0 μ0
      · simp_rw [P, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        rw [eLpNorm_eq_eLpNorm_rpow (g <| x - ·) r0 q0 rq0 μ0]
        simp [eLpNorm, eLpNorm', lintegral_sub_left_eq_self (‖g ·‖ₑ ^ (ENNReal.ofReal q).toReal) x]

-- Auxiliary inequality used to prove versions with simpler conditions on `f` and `g`
theorem eLpNorm_convolution_le_ofReal_aux
    [μ.IsAddRightInvariant] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) {f : G → E} {g : G → E'}
    (hf : AEMeasurable (‖f ·‖ₑ) μ) (hg : ∀ x : G, AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (hg' : AEMeasurable (fun (x : G × G) ↦ ‖(g ∘ fun p ↦ p.1 - p.2) x‖ₑ ^ q) (μ.prod μ))
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) (.ofReal r) μ ≤
    .ofReal c * eLpNorm f (.ofReal p) μ * eLpNorm g (.ofReal q) μ := by
  have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  have q0 : 0 < q := lt_of_lt_of_le one_pos hq
  have r0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hf' := hf.pow_const p
  have hfg := hf'.comp_snd.mul hg'
  replace hg' := hg'.pow_const q
  rw [← ENNReal.rpow_le_rpow_iff r0]
  repeat rw [ENNReal.mul_rpow_of_nonneg _ _ r0.le]
  calc eLpNorm (f ⋆[L, μ] g) (ENNReal.ofReal r) μ ^ r
    _ = ∫⁻ (x : G), ‖(f ⋆[L, μ] g) x‖ₑ ^ r ∂μ := by simp [eLpNorm, eLpNorm', r0, r0.le, r0.ne.symm]
    _ ≤ _ :=
      lintegral_mono <| fun x ↦ ENNReal.rpow_le_rpow (h₂ := r0.le) <|
        enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm_aux hp hq hr hpqr hf hg c hL x
    _ = (ENNReal.ofReal c) ^ r *
        (∫⁻ x, (eLpNorm (fun y ↦ (‖f y‖ₑ^p * ‖g (x-y)‖ₑ^q) ^ (1/r)) (ENNReal.ofReal r) μ) ^ r ∂μ) *
        (eLpNorm f (ENNReal.ofReal p) μ ^ (r - p) * eLpNorm g (ENNReal.ofReal q) μ ^ (r - q)) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ r0.le]
      rw [lintegral_mul_const'', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, lintegral_const_mul']
      · field_simp
      · exact ENNReal.rpow_ne_top_of_nonneg r0.le ofReal_ne_top
      · apply AEMeasurable.const_mul
        simpa [eLpNorm, eLpNorm', r0.not_ge, r0.ne.symm, r0.le] using hfg.lintegral_prod_right'
    _ = _ := by
      have (a b : ℝ≥0∞) : a ^ r * b ^ r = (a ^ p * b ^ q) * (a ^ (r - p) * b ^ (r - q)) := calc
        _ = (a ^ p * a ^ (r - p)) * (b ^ q * b ^ (r - q)) := by
          rw [← ENNReal.rpow_add_of_nonneg p _ p0.le, ← ENNReal.rpow_add_of_nonneg q _ q0.le,
            add_sub_cancel, add_sub_cancel]
          · exact r_sub_p_nonneg q0 hp r0 <| add_comm p⁻¹ q⁻¹ ▸ hpqr
          · exact r_sub_p_nonneg p0 hq r0 hpqr
        _ = _ := by ring
      rw [mul_assoc, mul_assoc, this]
      congr
      calc
        _ = ∫⁻ x, ((∫⁻ y, ((‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ r⁻¹) ^ r ∂μ) ^ r⁻¹) ^ r ∂μ := by
          simp [eLpNorm, eLpNorm', r0.not_ge, ENNReal.toReal_ofReal r0.le]
        _ = ∫⁻ x, (∫⁻ y, (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ∂μ) ∂μ := by
          simp_rw [← ENNReal.rpow_mul, inv_mul_cancel₀ r0.ne.symm, ENNReal.rpow_one]
        _ = ∫⁻ y, (∫⁻ x, (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ∂μ) ∂μ :=
          lintegral_lintegral_swap hfg
        _ = (∫⁻ y, ‖f y‖ₑ ^ p ∂μ) * (∫⁻ x, ‖g x‖ₑ ^ q ∂μ) := by
          have {y : G} : ‖f y‖ₑ ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg p0.le enorm_ne_top
          simp_rw [lintegral_const_mul' _ _ this, ← lintegral_mul_const'' _ hf',
            lintegral_sub_right_eq_self (‖g ·‖ₑ ^ q) _]
        _ = eLpNorm f (ENNReal.ofReal p) μ ^ p * eLpNorm g (ENNReal.ofReal q) μ ^ q := by
          simp [eLpNorm, eLpNorm', ← ENNReal.rpow_mul, inv_mul_cancel₀,
            p0.not_ge, q0.not_ge, p0.le, q0.le, p0.ne.symm, q0.ne.symm]

-- Auxiliary result to prove the following versions with simpler assumptions on `f` and `g`
theorem eLpNorm_convolution_le_of_norm_le_mul_aux
    [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable (‖f ·‖ₑ) μ)
    (hg : ∀ (x : G), AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (hg' : ∀ (x : G), eLpNorm (‖g <| x - ·‖ₑ) q μ = eLpNorm (‖g ·‖ₑ) q μ)
    (hg'' : AEMeasurable (fun x ↦ ‖(g ∘ fun p ↦ p.1 - p.2) x‖ₑ ^ q.toReal) (μ.prod μ))
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ .ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  -- First use `eLpNorm_top_convolution_le` to handle the cases where any exponent is `∞`
  by_cases r_top : r = ∞
  · rw [r_top, ENNReal.inv_top, zero_add] at hpqr
    have hpq : p.HolderConjugate q := holderConjugate_iff.mpr hpqr
    rw [r_top]
    refine eLpNorm_top_convolution_le_aux hpq hf hg hg' c hL
  have hpq : 1 < p⁻¹ + q⁻¹ := by
    rw [hpqr]
    nth_rewrite 1 [← zero_add 1]
    apply ENNReal.add_lt_add_right ENNReal.one_ne_top
    exact (zero_le (a := r⁻¹)).lt_or_eq.resolve_right (ENNReal.inv_ne_zero.mpr r_top).symm
  have p_ne_top : p ≠ ∞ := by contrapose! hq; simpa [hq] using hpq
  have q_ne_top : q ≠ ∞ := by contrapose! hp; simpa [hp] using hpq
  -- When all exponents are finite, apply `eLpNorm_convolution_le_ofReal`
  rw [← ENNReal.ofReal_toReal_eq_iff.mpr p_ne_top, ← ENNReal.ofReal_toReal_eq_iff.mpr q_ne_top,
    ← ENNReal.ofReal_toReal_eq_iff.mpr r_top]
  refine eLpNorm_convolution_le_ofReal_aux ?_ ?_ ?_ ?_ hf hg hg'' c hL; rotate_right
  · simp_rw [← ENNReal.toReal_one, ← ENNReal.toReal_inv]
    rw [← ENNReal.toReal_add _ ENNReal.one_ne_top, ← ENNReal.toReal_add, hpqr]
    all_goals exact ENNReal.inv_ne_top.mpr (fun h ↦ (h ▸ one_pos).not_ge (by assumption))
  all_goals rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top (by assumption)]

variable (L)

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. Here `‖L‖ₑ` is replaced with a bound for `L` restricted to the ranges
of `f` and `g`; see `eLpNorm_convolution_le_enorm_mul` for a version using `‖L‖ₑ` explicitly. -/
theorem eLpNorm_convolution_le_of_norm_le_mul [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E']
    [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ .ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  refine eLpNorm_convolution_le_of_norm_le_mul_aux hp hq hr hpqr hf.enorm ?_ ?_ ?_ c hL
  · intro x; exact hg.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)
  · intro x; exact eLpNorm_comp_measurePreserving' hg (μ.measurePreserving_sub_left x)
  · exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ) |>.enorm.pow_const _

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. -/
theorem eLpNorm_convolution_le_enorm_mul [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E']
    [μ.IsAddRightInvariant] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg L)]
  exact eLpNorm_convolution_le_of_norm_le_mul L hp hq hr hpqr hf hg ‖L‖ <| fun x y ↦
    ((L (f x)).le_opNorm (g y)).trans <| mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)

end ENNReal

end Convolution
end
end

section
-- module Solutions.OAIQ093_PR.Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Convolution on a finitely generated group
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

-- Proving associativity in full generality is very annoying
-- Fortunately, we only need to use it once, so we can use restrictive hypothesis that match
-- the functions we invoke this with
lemma conv_assoc {f g h: G → ℝ} (h_fg: ConvExists f g) (h_gh: ConvExists g h) (g_finsupp: g.support.Finite) (g_nonneg: ∀ a : G, 0 ≤ g a) (h_finsupp: h.support.Finite) (h_nonneg: ∀ a : G, 0 ≤ h a): Conv (Conv f g) h = Conv f (Conv g h) := by
  unfold Conv
  unfold ConvExists at h_fg
  funext x
  conv =>
    lhs
    arg 1
    simp
    eta_reduce
  rw [MeasureTheory.convolution_assoc (L := ContinuousLinearMap.mul ℝ ℝ) (L₂ := ContinuousLinearMap.mul ℝ ℝ) (L₃ := ContinuousLinearMap.mul ℝ ℝ) (L₄ := ContinuousLinearMap.mul ℝ ℝ)]
  . rfl
  . intro x y z
    simp
    rw [mul_assoc]
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  . apply MeasureTheory.AEStronglyMeasurable.of_discrete
  .
    apply Filter.Eventually.of_forall
    exact h_fg
  . apply Filter.Eventually.of_forall
    intro a
    conv =>
      arg 1
      intro b
      rw [Real.norm_of_nonneg (g_nonneg b)]

    conv =>
      arg 2
      intro b
      rw [Real.norm_of_nonneg (h_nonneg b)]
    apply h_gh a
  .

    have g_supp_compact: HasCompactSupport fun x ↦ ‖g x‖ := by
      apply HasCompactSupport.intro (K := g.support)
      . apply Set.Finite.isCompact
        apply g_finsupp
      . simp

    have h_supp_compact: HasCompactSupport fun x ↦ ‖h x‖ := by
      apply HasCompactSupport.intro (K := h.support)
      . apply Set.Finite.isCompact
        apply h_finsupp
      . simp

    apply HasCompactSupport.convolutionExists_right
    .
      apply HasCompactSupport.convolution
      .
        apply g_supp_compact
      . apply h_supp_compact
    . apply Continuous.locallyIntegrable
      exact continuous_of_discreteTopology
    .
      apply HasCompactSupport.continuous_convolution_right
      . apply h_supp_compact
      .
        apply Continuous.locallyIntegrable
        exact continuous_of_discreteTopology
      . exact continuous_of_discreteTopology

lemma mu_conv_finsupp (m: ℕ): (muConv  m).support.Finite := by
  induction m with
  | zero =>
    simp [muConv]
    apply mu_finsupp
  | succ n ih =>
    unfold muConv
    rw [Function.iterate_succ_apply']

    conv =>
      arg 1
      arg 1
      rw [conv_eq_sum' (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      )]


      intro g
      rw [tsum_eq_sum (s := (Finset.image Additive.ofMul (ih).toFinset)) (by
        intro a ha
        simp at ha
        simp
        unfold muConv at ha
        left
        have foo := ha (a.toMul)
        simp at foo
        exact foo
      )]


    apply Set.Finite.subset (ht := Finset.support_sum _ _)
    .

      simp [-Function.mem_support]
      apply Set.Finite.biUnion'
      . exact ih
      .
        intro i hi
        apply Set.Finite.inter_of_right
        apply Set.Finite.of_injOn (f := fun x => x * i⁻¹) (t := (mu_finsupp ).toFinset)
        .
          intro x hx
          simp at hx
          simp
          exact hx
        .
          intro y hy z hz
          simp
        . simp
          apply (mu_finsupp )

lemma conv_sum {T: Type*} (H: Finset T) (f: T → G → ℝ) (h: G → ℝ) (h_finsupp: h.support.Finite): Conv (∑ t ∈ H, f t) h = ∑ t ∈ H, (Conv (f t) h) := by
  funext g
  rw [conv_eq_sum]
  .
    simp
    conv =>
      rhs
      arg 2
      intro t
      rw [conv_eq_sum (by
        apply conv_exists_fin_supp
        right
        exact h_finsupp
      )]

    conv =>
      lhs
      arg 1
      intro a
      rw [Finset.sum_mul]

    rw [Summable.tsum_finsetSum]
    intro s hs
    apply summable_of_hasFiniteSupport
    change (Function.support _).Finite
    simp only [Function.support_mul]
    apply Set.Finite.inter_of_right
    rw [← Function.comp_def]
    rw [Function.support_comp_eq_preimage]
    apply Set.Finite.preimage
    .
      intro y hy z hz
      simp
    . exact h_finsupp
  . apply conv_exists_fin_supp
    right
    exact h_finsupp

-- The convolution of an Lp2 function with a finitely-supported function is LP2
--set_option maxHeartbeats 1000000 in
@[expose]
noncomputable def conv_finsupp_lp2 (f: (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G)))) (g : G → ℝ) (hg : g.support.Finite): (MeasureTheory.Lp ℝ 2 (MeasureTheory.volume (α := G))) := MeasureTheory.MemLp.toLp (Conv f g) (by
  simp [MemLp]
  refine ⟨by apply AEStronglyMeasurable.of_discrete, ?_⟩
  have norm_bound := ENNReal.eLpNorm_convolution_le_enorm_mul (G := Additive G)  (f := f) (g := g) (E' := ℝ) (E := ℝ) (F := ℝ) (𝕜 := ℝ) (p := 2) (q := 1) (r := 2) (μ := myHaarAddOpp) (ContinuousLinearMap.mul ℝ ℝ)
    (by simp) (by simp) (by simp) (by simp) (by apply AEMeasurable.of_discrete) (by apply AEMeasurable.of_discrete)

  unfold Conv
  eta_reduce
  rw [my_add_haar_eq_count]
  dsimp [volume]
  simp_rw [my_haar_eq_count]
  rw [my_add_haar_eq_count] at norm_bound
  refine lt_of_le_of_lt norm_bound ?_
  apply WithTop.mul_lt_top
  . apply WithTop.mul_lt_top
    . exact enorm_lt_top
    . rw [← my_add_haar_eq_count]
      apply (MeasureTheory.Lp.memLp f).2
  .
    simp [eLpNorm, eLpNorm']
    rw [MeasureTheory.lintegral_count]
    rw [tsum_eq_sum (s := hg.toFinset) (β := Additive G)]
    . simp_rw [Real.enorm_eq_ofReal_abs]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      . -- TODO - why can't simp' find this?
        apply ENNReal.ofReal_lt_top
      . simp
    . intro b hb
      have hgb : g b = 0 := by
        by_contra hne
        exact hb (hg.mem_toFinset.mpr (Function.mem_support.mpr hne))
      rw [hgb]
      simp
)

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.CriticalPercolation_Nilpotent_LowerCentralFG
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable (G : Type*) [Group G]

def lowerFactor (n : ℕ) : Subgroup (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (n+1)) :=
  ((⊤ : Subgroup G).lowerCentralSeries n).map
    (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1)))

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ093_PR.Harmonic_Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Convolution and the Laplacian

Basic compatibility of the discrete Laplacian with convolution: additivity, scalar
multiplication, and `laplace_conv_eq_laplace_right`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates


variable [hGS: Generates]
include hGS


variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]


open scoped Finset
open scoped Pointwise


lemma haar_eq_haar_add : myHaar = myHaarAddOpp := by
  rfl

open scoped Convolution
open MeasureTheory


-- Linearity lemmas for convolution - this is basically just wrapping the MeasureTheory.ConvolutionExists lemmas,
-- specialized for our own Additive/MulOpposite wrappers
lemma conv_add_right {f g h: G → ℝ} (h_fg: ConvExists f g) (h_fh : ConvExists f h):  Conv f (g + h) = Conv f g + Conv f h := by
  unfold Conv
  conv =>
    lhs
    intro x
    arg 2
    equals (fun x => g ((Additive.toMul x))) + (fun x => h ((Additive.toMul x))) =>
      rfl

  rw [MeasureTheory.ConvolutionExists.distrib_add]
  . rfl
  . exact h_fg
  . exact h_fh

lemma conv_add_left {f g h: G → ℝ} (h_fh: ConvExists f h) (h_gh : ConvExists g h):  Conv (f + g) h = Conv f h + Conv g h := by
  unfold Conv
  conv =>
    lhs
    intro x
    arg 1
    equals (fun x => f ((Additive.toMul x))) + (fun x => g ((Additive.toMul x))) =>
      rfl

  rw [MeasureTheory.ConvolutionExists.add_distrib]
  . rfl
  . exact h_fh
  . exact h_gh

lemma conv_smul {f h: G → ℝ} (k: ℝ): Conv (k • f) h = k • Conv f h := by
  funext g
  show MeasureTheory.convolution (G := Additive G) (k • f) h (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp g
     = k • MeasureTheory.convolution (G := Additive G) f h (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp g
  simp only [MeasureTheory.convolution_def]
  rw [← MeasureTheory.integral_smul]
  congr 1
  funext t
  simp only [Pi.smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring

lemma smul_conv (f h: G → ℝ) (k: ℝ): Conv f (k • h) = k • Conv f h := by
  funext g
  show MeasureTheory.convolution (G := Additive G) f (k • h) (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp g
     = k • MeasureTheory.convolution (G := Additive G) f h (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp g
  simp only [MeasureTheory.convolution_def]
  rw [← MeasureTheory.integral_smul]
  congr 1
  funext t
  simp only [Pi.smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring


lemma laplace_conv_eq_laplace_right (f g: G → ℝ) (hfg: ConvExists f g) (g_nonneg: ∀ a: G, 0 ≤ g a) (g_finsupp: g.support.Finite): Laplace_b (Conv f g) = Conv f (Laplace_b g) := by
  simp_rw [Laplace_b]
  rw [conv_assoc]

  nth_rw 2 [sub_eq_add_neg]
  rw [conv_add_right]
  -- TODO - figure out how to do this without a 'conv' block
  conv =>
    rhs
    rhs
    equals Conv f ((-1 : ℝ) • (Conv g (mu ))) =>
      simp
  rw [smul_conv]
  simp
  . rw [← sub_eq_add_neg]
  . exact hfg
  .
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt]
    intro a
    simp_rw [f_conv_mu]
    simp_rw [← mul_assoc, mul_comm, mul_assoc]
    apply MeasureTheory.Integrable.const_mul
    simp_rw [Finset.mul_sum]
    apply MeasureTheory.integrable_finset_sum
    intro s hs
    simp [ConvExists, MeasureTheory.ConvolutionExists, MeasureTheory.ConvolutionExistsAt] at hfg
    specialize hfg (s * a)
    simp_rw [mul_div]
    exact hfg
  . exact hfg
  .
    apply conv_exists_fin_supp
    right
    exact mu_finsupp
  . apply g_finsupp
  . exact g_nonneg
  . exact mu_finsupp
  . intro a
    simp [mu]
    positivity


lemma f_n_fin_supp (n: ℕ): (f_n  n).support.Finite := by
  unfold f_n
  simp
  apply Set.Finite.inter_of_right
  apply Set.Finite.subset (hs := ?_) (ht := Finset.support_sum _ _)
  refine Set.Finite.biUnion' ?_ ?_
  . exact Set.toFinite (Membership.mem Finset.univ.val)
  . intro m hm
    apply mu_conv_finsupp


-- The expression 'Σ s_1, ..., s_n ∈ S, f(s_1 * ... * s_n)'
-- This is a sum over all n-tuples of elements in S, where each term in is f (s_1 * ... * s_n)
-- TODO - is there aless horrible way to write in in mathlib?
@[expose]
def NTupleSum (n: ℕ) (f: G → ℝ): ℝ := ∑ s : (Fin n → S), f ((List.ofFn s).unattach.prod)


-- Proposition 3.12, item 3, in Vikman
-- The 'm + 1' terms are due to the fact that 'muConv 0' still applies mu once (without any convolution)

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_MuConv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Iterated convolution with `mu`

`mu_conv_eq_sum` expressing `muConv` as a sum over tuples, its nonnegativity and `L¹` norm, and
the telescoping identity `f_n_sub_conv`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

theorem mu_conv_eq_sum (m: ℕ): muConv m = fun g => (((1 : ℝ) / (#(S) : ℝ)) ^ (m + 1)) * (NTupleSum  (m + 1) (delta g))  := by
  induction m with
  | zero =>
    funext g
    simp [muConv, NTupleSum, mu, delta, Pi.single, Function.update]
    by_cases g_in_s: g ∈ S
    .
      simp [g_in_s]
      conv =>
        rhs
        rhs
        rhs
        rhs
        equals {fun (a : Fin 1) => ⟨g, g_in_s⟩} =>
          ext a
          simp
          refine ⟨?_, ?_⟩
          . intro a_zero_eq
            ext x
            simp
            have x_eq_zero: x = 0 := by
              exact Fin.fin_one_eq_zero x
            rw [x_eq_zero]
            exact a_zero_eq
          . intro a_eq
            simp [a_eq]
      simp
    .
      simp [g_in_s]
      right
      by_contra this
      .
        simp at this
        obtain ⟨x, hx⟩ := this
        rw [← hx] at g_in_s
        simp at g_in_s
  | succ n ih =>
    unfold muConv
    rw [Function.iterate_succ_apply']
    nth_rw 3 [mu]
    funext g
    nth_rw 1 [conv_eq_sum]
    simp [-Finset.sum_pi_single]
    simp_rw [mul_comm]
    simp_rw [mul_assoc]
    rw [Summable.tsum_mul_left]
    simp_rw [Finset.sum_mul]
    rw [Summable.tsum_finsetSum]
    .
      conv =>
        lhs
        rhs
        arg 2
        intro x
        equals (Conv (muConv n) (delta x) ) g =>
          rw [conv_eq_sum]
          .
            unfold muConv
            unfold delta
            simp_rw [mul_comm]
          .
            apply conv_exists_fin_supp
            right
            simp [delta]


      simp_rw [f_conv_delta]
      simp_rw [ih]
      rw [← Finset.mul_sum]
      conv =>
        lhs
        rhs
        rhs
        arg 2
        intro s
        simp only [NTupleSum]

      rw [← mul_assoc]
      conv =>
        lhs
        lhs
        simp
        equals (((#S) : ℝ) ^ (n + 1 + 1))⁻¹ =>
          field_simp
          nth_rw 2 [pow_succ]
          simp
          rw [mul_comm]
      simp only [mul_eq_mul_left_iff, inv_eq_zero, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
        and_self, not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero, Finset.card_eq_zero]
      left
      rw [← Finset.sum_attach]
      rw [← Finset.sum_product']
      apply Fintype.sum_bijective (e := fun (x) => (fun (i: Fin (n + 1 + 1)) => if hi: i.val = 0 then x.fst else x.snd ⟨i - 1, by omega⟩))
      .
        refine ⟨?_, ?_⟩
        .
          intro a b hab
          simp at hab
          ext p
          .
            have fst_eq := congrFun hab (⟨0, by omega⟩)
            simp at fst_eq
            rw [fst_eq]

          .
            have p_lt_n_plus := p.prop
            have p_val_neq: p.val ≠ n + 1 := by omega


            have snd_eq := congrFun hab (⟨p + 1, by omega⟩)
            by_cases p_eq_zero: p = 0
            .
              simp [p_eq_zero] at snd_eq
              rw [p_eq_zero]
              rw [snd_eq]
            .
              simp [p_eq_zero] at snd_eq
              rw [snd_eq]
        .
          intro f
          use ((f (⟨0, by omega⟩)), fun i => f (⟨i + 1, by omega⟩))
          funext i
          simp
          by_cases i_eq_zero: i = 0
          . simp [i_eq_zero]
          .
            simp [i_eq_zero]
            have i_val_neq_zero: i.val ≠ 0 := by
              simp [i_eq_zero]
            have one_le_i: 1 ≤ i.val := by omega
            simp [Nat.sub_add_cancel one_le_i]
      .
        intro x
        simp only [delta]
        rw [Pi.single_apply]
        rw [Pi.single_apply]


        split_ifs
        .
          rename _ => hi
          simp [hi]
        .
          rename_i g_eq g_mul_neq
          apply_fun (fun y =>  (x.fst.val) * y ) at g_eq
          rw [← mul_assoc] at g_eq
          simp at g_eq
          rw [← g_eq] at g_mul_neq
          rw [List.ofFn_succ] at g_mul_neq
          norm_cast at g_mul_neq
          conv at g_mul_neq =>
            arg 1
            lhs
            simp


          contradiction
        . rename_i g_mul_neq g_eq

          simp [List.ofFn_succ] at g_eq
          rw [← g_eq] at g_mul_neq
          simp at g_mul_neq
        . rfl
    . intro s hs
      simp [Pi.single_apply]
      rw [← summable_norm_iff]
      apply Summable.of_nonneg_of_le (f := fun a => ‖(fun f ↦ Conv f mu)^[n] mu ((Additive.toMul a))‖)
      .
        intro x
        simp
      . intro x
        split_ifs
        . rfl
        . simp
      .
        rw [summable_norm_iff]
        have conv_finsupp := mu_conv_finsupp  n
        unfold muConv at conv_finsupp

        apply summable_of_hasFiniteSupport
        apply Set.Finite.of_injOn (f := fun a => ( (Additive.toMul a))) (ht := conv_finsupp)
        .
          intro a ha
          exact ha
        . intro a ha b hb
          simp
    -- TODO - deduplicate this with the above goal
    .
      simp [Pi.single_apply]
      rw [← summable_norm_iff]
      apply Summable.of_nonneg_of_le (f := fun a => ‖(fun f ↦ Conv f mu)^[n] mu ((Additive.toMul a))‖)
      .
        intro x
        simp
      . intro x
        split_ifs
        . rfl
        . simp
      .
        rw [summable_norm_iff]
        have conv_finsupp := mu_conv_finsupp  n
        unfold muConv at conv_finsupp

        apply summable_of_hasFiniteSupport
        apply Set.Finite.of_injOn (f := fun a => ( (Additive.toMul a))) (ht := conv_finsupp)
        .
          intro a ha
          exact ha
        . intro a ha b hb
          simp
    .
      apply conv_exists_fin_supp
      right
      simp [delta]
      apply Set.Finite.subset (ht := Function.support_const_smul_subset _ _)
      have supp_sum := Finset.support_sum (s := S) (f := fun s => Pi.single (M := fun _ : G => ℝ) s (1: ℝ))
      conv =>
        arg 1
        arg 1
        equals fun x => ∑ s ∈ S, Pi.single (M := fun _ : G => ℝ) s (1 : ℝ) x =>
          funext a
          simp

      apply Set.Finite.subset (ht := supp_sum)
      simp
      exact Set.toFinite (⋃ i ∈ S, {i})

lemma mu_conv_nonneg (n: ℕ): ∀ g, 0 ≤ muConv  n g := by
  intro g
  induction n with
  | zero =>
    simp [muConv, mu]
    split_ifs
    . simp
    . simp
  | succ n ih =>
    rw [mu_conv_eq_sum]
    apply mul_nonneg
    . simp
    .
      simp [NTupleSum]
      apply Finset.sum_nonneg
      intro i hi
      simp [delta, Pi.single_apply]
      split_ifs
      . simp
      . simp


lemma f_n_nonneg: ∀ n: ℕ, ∀ g: G,  0 ≤ f_n n g := by
  intro n g
  simp [f_n]
  apply mul_nonneg
  . positivity
  . apply Finset.sum_nonneg
    intro i hi
    apply mu_conv_nonneg

lemma conv_laplce_norm (n: ℕ) (H_n: ℕ → G → ℝ): eLpNorm ((Laplace_b ((Conv (H_n n)) (f_n n)))) ⊤ (μ := volume (α := G)) ≤ eLpNorm (H_n n) ⊤ * (eLpNorm (Laplace_b (f_n n)) 1 (μ := volume (α := G))) := by
  rw [laplace_conv_eq_laplace_right]
  .
    unfold Conv
    eta_reduce
    simp only [volume]
    rw [haar_eq_haar_add]

    have my_norm := ENNReal.eLpNorm_convolution_le_enorm_mul (f := H_n n) (G := (Additive G)) (L := (ContinuousLinearMap.mul ℝ ℝ))
      (g := Laplace_b (f_n n)) (r := ⊤) (p := ⊤) (q := 1) (μ := myHaarAddOpp)
      (by simp)
      (by simp)
      (by simp)
      (by simp)
      (by apply AEMeasurable.of_discrete)
      (by apply AEMeasurable.of_discrete)


    refine le_trans my_norm ?_
    have hmul : ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 := by
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_one]
      exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    rw [mul_assoc]
    exact le_trans (mul_le_mul_left hmul _) (le_of_eq (one_mul _))
  .
    apply conv_exists_fin_supp
    right
    exact f_n_fin_supp n
  . apply f_n_nonneg
  . exact f_n_fin_supp n


lemma lintegral_g_eq_add (f: G → ENNReal): (∫⁻ (g: G), f g) = (∑' (g : G), f g) := by
  rw [MeasureTheory.lintegral_countable']
  simp [MeasureTheory.volume, my_haar_eq_count]


lemma mu_norm_one (m: ℕ): MeasureTheory.eLpNorm (muConv  m) 1 = 1 := by
  simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm']
  rw [lintegral_g_eq_add]
  simp [mu_conv_eq_sum]
  rw [ENNReal.tsum_mul_left]
  simp [NTupleSum, delta]
  conv =>
    lhs
    rhs
    equals ENNReal.ofReal (∑' (i : G), (∑ x : (Fin (m + 1) → { x // x ∈ S }), if (List.ofFn x).unattach.prod = i then 1 else 0 )) =>
      conv =>
        lhs
        arg 1
        intro i
        rw [Real.enorm_of_nonneg (by
          apply Finset.sum_nonneg
          intro x hx
          simp [delta, Pi.single_apply]
          split_ifs
          . simp
          . simp
        )]


      rw [← ENNReal.ofReal_tsum_of_nonneg]
      simp [Pi.single_apply]
      . intro g
        apply Finset.sum_nonneg
        intro i
        simp [Pi.single_apply]
        split_ifs
        . simp
        . simp
      .
        apply summable_sum
        intro i hi
        simp only [Pi.single_apply]
        apply summable_of_hasFiniteSupport
        apply Set.Finite.subset (s := {(List.ofFn i).unattach.prod})
        . simp
        . intro a ha
          simp
          simp at ha
          rw [ha]
  rw [Summable.tsum_finsetSum]
  .
    conv =>
      lhs
      rhs
      rhs
      arg 2
      intro i
      simp only [eq_comm]
      rw [tsum_ite_eq]
    simp
    rw [Real.enorm_of_nonneg (by
      simp
    )]
    field_simp
    rw [← ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_pow]
    rw [← ENNReal.ofReal_mul]
    .
      field_simp
      simp
      exact Finset.nonempty_iff_ne_empty.mp S_nonempty
    . simp
    . simp
  .
    -- TODO - deduplicate this with the above goal
    intro a ha
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (s := {(List.ofFn a).unattach.prod})
    . simp
    . intro a ha
      simp
      simp at ha
      rw [ha]


--set_option pp.analyze true

-- Proposition 3.15.1 from Vikman
theorem f_n_norm_one (n: ℕ): MeasureTheory.eLpNorm (f_n  n) 1 = 1 := by
  unfold f_n
  simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm']
  rw [lintegral_g_eq_add]
  rw [ENNReal.tsum_mul_left]
  conv =>
    lhs
    arg 2
    arg 1
    intro g
    equals ∑ m: Fin (n + 1), ‖muConv (↑m) g‖ₑ =>
      rw [Real.enorm_of_nonneg (by
        apply Finset.sum_nonneg
        intro i hi
        apply mu_conv_nonneg
      )]
      rw [ENNReal.ofReal_sum_of_nonneg (by
        intro i hi
        apply mu_conv_nonneg
      )]
      conv =>
        lhs
        arg 2
        intro i
        rw [← Real.enorm_of_nonneg (by
          apply mu_conv_nonneg
        )]

  rw [Summable.tsum_finsetSum]
  .
    have mu_norm := mu_norm_one
    simp [MeasureTheory.eLpNorm, MeasureTheory.eLpNorm'] at mu_norm
    simp_rw [lintegral_g_eq_add] at mu_norm
    simp_rw [mu_norm]
    simp
    norm_cast
    rw [Real.enorm_of_nonneg (by
      simp
      linarith
    )]
    rw [← ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_mul]
    .
      field_simp
      simp
    . simp
      linarith
  .
    simp


-- Proposition 3.15.2 from Vikman
theorem f_n_sub_conv (n: ℕ): MeasureTheory.eLpNorm ((f_n  n) - (Conv (f_n  n) (mu ))) 1 ≤ ENNReal.ofReal ((2 : ℝ) / ((n + 1) : ℝ)) := by
  unfold f_n
  conv =>
    lhs
    arg 1


  conv =>
    lhs
    arg 1
    arg 1
    equals ((1: ℝ) / (n + 1)) • ∑ m: Fin (n + 1), muConv (↑m) =>
      funext p
      simp
  simp_rw [← smul_eq_mul]
  conv =>
    lhs
    arg 1
    rhs
    arg 1
    rw [← Pi.smul_def]


  rw [conv_smul]
  conv =>
    lhs
    arg 1
    rhs
    equals ((1 : ℝ) / ((n + 1) : ℝ)) • (Conv (∑ m: Fin (n + 1), muConv (m)) (mu )) =>
      funext g
      simp
      left
      conv =>
        lhs
        arg 1
        equals ∑ m: Fin (n + 1), muConv  (m) =>
          funext y
          simp

  rw [conv_sum]
  .
    rw [← smul_sub]
    rw [← Finset.sum_sub_distrib]
    conv =>
      lhs
      arg 1
      rhs
      arg 2
      intro x
      rhs
      equals muConv (↑x + 1) =>
        unfold muConv
        rw [Function.iterate_succ_apply']

    conv =>
      lhs
      arg 1
      rhs
      equals -∑ x: Fin (n + 1), ((muConv  (↑x + 1)) - (muConv  (x.val))) =>
        simp


    conv =>
      lhs
      arg 1
      rhs
      rhs
      equals (muConv (n + 1)) - muConv (0) =>
        induction n with
        | zero =>
          simp

        | succ y iy =>
          rw [Finset.sum_fin_eq_sum_range]
          rw [Finset.sum_range_succ_comm]
          rw [Finset.sum_fin_eq_sum_range] at iy
          simp at iy
          simp
          conv =>
            lhs
            rhs
            rw [Finset.sum_congr (s₂ := Finset.range (y + 1)) rfl (g := fun x => if x < y + 1 then muConv (x + 1) - muConv (x) else 0) (by
              intro x hx
              simp
              simp at hx
              split_ifs
              . simp
              . omega
            )]


          simp [iy]

    simp
    nth_rw 1 [muConv]
    simp
    calc
      _ ≤ ‖((n + 1): ℝ)⁻¹‖ₑ * MeasureTheory.eLpNorm ((mu - muConv (n + 1))) 1 MeasureTheory.volume := by
        apply MeasureTheory.eLpNorm_const_smul_le
      _ ≤ ‖((n + 1): ℝ)⁻¹‖ₑ * (MeasureTheory.eLpNorm ((mu)) 1 MeasureTheory.volume + (MeasureTheory.eLpNorm ((muConv (n + 1))) 1 MeasureTheory.volume)) := by
        have sub_le := MeasureTheory.eLpNorm_sub_le (p := 1) (f := mu ) (g := muConv  (n + 1)) (μ := MeasureTheory.volume) ?_ ?_ (by simp)
        .
          apply mul_le_mul_right sub_le
        . apply MeasureTheory.AEStronglyMeasurable.of_discrete
        . apply MeasureTheory.AEStronglyMeasurable.of_discrete
      _ ≤ ENNReal.ofReal ((2: ℝ) / ((n + 1): ℝ)) := by
        rw [mu_norm_one]
        have mu_single_norm := mu_norm_one  0
        simp [muConv] at mu_single_norm
        rw [mu_single_norm]
        field_simp
        norm_cast
        rw [Real.enorm_of_nonneg (by
          simp
          linarith
        )]
        rw [← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul]
        simp
        rw [mul_comm]
        field_simp
        simp
        positivity
  . exact mu_finsupp


end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_LaplaceLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The Laplacian as a linear map on `L²`

`Laplace_linear`, the normalised functions `F_n`, and the limit `F_n_conv_mu_lim`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

set_option maxHeartbeats 60000 in
@[expose]
noncomputable def nontrivial_harmonic_common (k: ℕ) (seq: ℕ → ℕ) (h_seq: Filter.Tendsto seq Filter.atTop Filter.atTop) (F: G → ℝ) (H_n: ℕ → G → ℝ) (h_conv_lipschitz: ∀ n, LipschitzWith k (Conv (H_n n) (f_n n)))
(tendsto_F: Filter.Tendsto ((fun n ↦ Conv (H_n (seq n)) (f_n (seq n)))) Filter.atTop (nhds F))
(H_n_norm: ∀ n: ℕ, MeasureTheory.eLpNorm (H_n n) (p := ⊤) MeasureTheory.volume = 1): LipschitzH := by

  let conv_h_n_cont (n: ℕ): C(G, ℝ) := {
    toFun := Conv (H_n (seq n)) (f_n (seq n)),
    continuous_toFun := by exact continuous_of_discreteTopology
  }

  let F_lipschitzh: LipschitzH := {
    toFun := (fun (g: G) => F g),
    lipschitz := by
      use k
      have closed_lipschitz := isClosed_setOf_lipschitzWith (α := G) (β := ℝ) k
      apply IsClosed.isSeqClosed at closed_lipschitz
      simp [IsSeqClosed] at closed_lipschitz
      have F_lipschitz := closed_lipschitz (p := F) (x := (fun n ↦ Conv (H_n (seq n)) (f_n (seq n)))) (by
        intro n
        apply h_conv_lipschitz
      ) tendsto_F
      exact F_lipschitz
    harmonic := by
      simp [Harmonic]
      intro g
      rw [tendsto_pi_nhds] at tendsto_F
      have lim_f_sum := tendsto_finset_sum (ι := S) (M := ℝ) (s := Finset.univ) (a := fun s => F (s.val * g)) (f := (fun (s: S) n ↦ Conv (H_n (seq n)) (f_n (seq n)) (s.val *g))) (x := Filter.atTop (α := ℕ)) ?_

      -- TODO - figure out why lean hangs without this
      have my_mul : ContinuousMul ℝ := instIsTopologicalRingReal.toContinuousMul
      have lim_f_mul_sum := Filter.Tendsto.const_mul ((#S) : ℝ)⁻¹ lim_f_sum
      .
        have lim_f_g := tendsto_F g
        have lim_f_g_sub := Filter.Tendsto.sub lim_f_g lim_f_mul_sum

        have laplace_conv_tendsto_zero: Filter.Tendsto (fun n => eLpNorm (Laplace_b (Conv (H_n (seq n)) (f_n (seq n)))) ⊤) Filter.atTop (nhds 0) := by
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => 0) (h := fun (n: ℕ) => ENNReal.ofReal ((2: ℝ) / ((seq n) + 1) : ℝ))
          . simp
          .
            rw [← ENNReal.tendsto_toReal_iff]
            conv =>
              arg 1
              intro n
              rw [ENNReal.toReal_ofReal (by
                norm_cast
                positivity
              )]
            conv =>
              arg 1
              intro n
              rhs
              equals ((((((seq n) + 1): ℕ)) : ℕ ) : ℝ) => simp
            conv =>
              arg 1
              equals (fun (n: ℕ) => (2 : ℝ) / (n) ) ∘ (fun n => (seq n) + 1) =>
                ext n
                simp
            apply Filter.Tendsto.comp
            .
              conv =>
                arg 1
                equals (fun (n: ℕ) => (2 : ℝ) / ((n) : ℕ)) =>
                  ext n
                  simp
              apply tendsto_const_div_atTop_nhds_zero_nat
            .
              apply Filter.Tendsto.comp
              . conv =>
                  arg 1
                  equals fun n => n + 1 =>
                    simp
                apply Filter.tendsto_add_atTop_nat

              . simp
                exact h_seq
            . simp
            . simp
          . rw [Pi.le_def]
            intro x
            simp
          . rw [Pi.le_def]
            intro n
            simp
            have bound_by_norm_one := conv_laplce_norm (seq n)
            have norm_le_two_div := f_n_sub_conv  (seq n)
            nth_rw 1 [eLpNorm] at bound_by_norm_one
            simp at bound_by_norm_one
            grw [bound_by_norm_one]
            have h_norm := H_n_norm (seq n)
            simp [eLpNorm, eLpNorm'] at h_norm
            rw [h_norm]
            simp
            simp_rw [Laplace_b]
            simp [eLpNorm] at norm_le_two_div
            exact norm_le_two_div

        rw [← ENNReal.tendsto_toReal_iff] at laplace_conv_tendsto_zero

        have laplace_real_tendsto_zero: Filter.Tendsto (fun n => |(Laplace_b (Conv (H_n (seq n)) (f_n (seq n))) (g))|) Filter.atTop (nhds 0)  := by
          apply squeeze_zero (g := fun n => (eLpNorm (Laplace_b (Conv (H_n (seq n)) (f_n (seq n)))) ⊤ volume).toReal)
          .
            intro n
            simp
          . intro n
            have ae_le := ENNReal.ae_le_essSup (fun x ↦ ‖Laplace_b (Conv (H_n (seq n)) (f_n (seq n))) x‖ₑ) (μ := volume)
            simp [volume] at ae_le
            rw [my_haar_eq_count] at ae_le
            rw [count_ae_everywhere] at ae_le
            specialize ae_le g
            simp [eLpNorm, eLpNorm']
            simp [eLpNormEssSup]
            rw [← ENNReal.toReal_le_toReal] at ae_le
            simp only [toReal_enorm, Real.norm_eq_abs, OrderTop.bddAbove] at ae_le
            simp [volume]
            rw [my_haar_eq_count]
            exact ae_le
            . simp
            .
              -- TODO - deduplicate this
              have bound_by_norm_one := conv_laplce_norm (seq n) H_n
              have norm_le_two_div := f_n_sub_conv (seq n)
              nth_rw 1 [eLpNorm] at bound_by_norm_one
              simp at bound_by_norm_one
              have h_norm := H_n_norm (seq n)
              simp [eLpNorm, eLpNorm'] at h_norm
              rw [h_norm] at bound_by_norm_one
              simp only [eLpNormEssSup] at bound_by_norm_one
              simp [volume] at bound_by_norm_one
              rw [my_haar_eq_count] at bound_by_norm_one
              rw [← lt_top_iff_ne_top]
              grw [bound_by_norm_one]
              simp_rw [Laplace_b]
              simp [volume] at norm_le_two_div
              rw [my_haar_eq_count] at norm_le_two_div
              grw [norm_le_two_div]
              apply ENNReal.ofReal_lt_top
          . apply laplace_conv_tendsto_zero

        simp_rw [Laplace_b] at laplace_real_tendsto_zero
        simp_rw [f_conv_mu] at laplace_real_tendsto_zero
        beta_reduce at laplace_real_tendsto_zero
        conv at laplace_real_tendsto_zero =>
          arg 1
          rw [← Function.comp_def]
        rw [← tendsto_zero_iff_abs_tendsto_zero] at laplace_real_tendsto_zero
        --simp_rw [Function.comp_def] at lim_f_g_sub
        conv at laplace_real_tendsto_zero =>
          arg 1
          intro n
          simp

        conv at lim_f_g_sub =>
          arg 1
          intro n
          rw [← Finset.sum_subtype (s := S) (f := fun s => Conv (H_n (seq n)) (f_n (seq n)) (s * g)) (h := by
            intro s
            simp
          )]
        have lim_eq := tendsto_nhds_unique laplace_real_tendsto_zero lim_f_g_sub
        rw [eq_comm] at lim_eq
        rw [sub_eq_zero] at lim_eq
        rw [lim_eq]
        norm_cast
        rw [← Finset.sum_subtype (s := S) (f := fun i => (F (i * g)))]
        simp
        . intro n
          -- TODO - deduplicate this. I'm sure there's lots of other versions of it scattered around this file
          rw [← lt_top_iff_ne_top]
          grw [conv_laplce_norm]
          rw [H_n_norm]
          simp
          simp_rw [Laplace_b]
          grw [MeasureTheory.eLpNorm_sub_le]
          rw [f_n_norm_one]
          simp_rw [f_conv_mu]
          simp_rw [← smul_eq_mul]
          rw [← Pi.smul_def]
          rw [MeasureTheory.eLpNorm_const_smul]
          conv =>
            lhs
            rhs
            rhs
            arg 1
            equals ∑ x ∈ S, (fun g => f_n (seq n) (x • g)) =>
              funext g
              simp


          grw [MeasureTheory.eLpNorm_sum_le]
          simp_rw [← Function.comp_def]
          conv =>
            lhs
            rhs
            rhs
            arg 2
            intro x
            rw [MeasureTheory.eLpNorm_comp_measurePreserving (ν := MeasureTheory.volume) (by
              apply MeasureTheory.AEStronglyMeasurable.of_discrete
            ) (by
            exact {
              measurable := by
                apply Measurable.of_discrete
              map_eq := by
                simp [MeasureTheory.volume]
            }
          )]
          simp_rw [f_n_norm_one]
          simp
          field_simp
          norm_cast
          rw [Real.enorm_eq_ofReal_abs]
          simp
          norm_cast
          apply ENNReal.mul_lt_top
          . simp
          . simp
          .
            intro s hs
            apply AEStronglyMeasurable.of_discrete
          . simp
          . apply AEStronglyMeasurable.of_discrete
          . apply AEStronglyMeasurable.of_discrete
          . simp


        . simp
      . intro s hs
        apply tendsto_F
  }
  exact F_lipschitzh


@[expose]
noncomputable def Laplace_linear: (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) →ₗ[ℝ] (MeasureTheory.Lp ℝ 2 (μ := volume (α := G))) := {
  toFun := Laplace
  map_add' := by
    intro x y
    simp [Laplace]
    simp [conv_mu_lp2]
    have coe_add := MeasureTheory.Lp.coeFn_add x y
    rw [ae_eq_everywhere] at coe_add
    norm_cast
    simp_rw [coe_add]
    conv =>
      pattern Conv _ _
      rw [conv_add_left (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      ) (by
        apply conv_exists_fin_supp
        right
        apply mu_finsupp
      )]

    rw [MeasureTheory.MemLp.toLp_add]
    . abel
    .
      have foo := MeasureTheory.Lp.memLp (conv_mu_lp2 x)
      simp [conv_mu_lp2] at foo
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at foo
      exact foo
    . have foo := MeasureTheory.Lp.memLp (conv_mu_lp2 y)
      simp [conv_mu_lp2] at foo
      rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)] at foo
      exact foo
  map_smul' := by
    intro c f
    simp [Laplace, conv_mu_lp2]
    have smul_ae := MeasureTheory.Lp.coeFn_smul c f
    rw [ae_eq_everywhere] at smul_ae
    simp_rw [smul_ae]
    simp_rw [conv_smul]
    rw [MeasureTheory.MemLp.toLp_const_smul]
    rw [smul_sub]
}


lemma finsupp_lp_top (f: G → ℝ) (hf: f.support.Finite) (p: ENNReal): MeasureTheory.MemLp f p (Measure.count) := by
  rw [← my_haar_eq_count]
  apply Continuous.memLp_of_hasCompactSupport
  . apply continuous_of_discreteTopology
  .
    simp [HasCompactSupport]
    rw [isCompact_iff_finite]
    simp [tsupport]
    exact hf


@[expose]
noncomputable def F_n (n : ℕ) := Real.sqrt ∘ (f_n  n)
@[expose]
noncomputable def F_n_lp2 (n : ℕ) := MeasureTheory.MemLp.toLp (F_n  n) (by
  simp [volume]
  rw [my_haar_eq_count]
  apply finsupp_lp_top
  simp [F_n]
  apply Set.Finite.subset (s := (f_n n).support)
  .
    unfold f_n
    apply f_n_fin_supp
  .
    apply Function.support_comp_subset
    simp
) (μ := volume (α := G)) (p := 2)


@[expose]
instance volume_mul_left_invariant: (volume (α := G)).IsMulLeftInvariant := by
  simp [volume]
  rw [my_haar_eq_count]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

omit hGS in
lemma abs_sub_le_abs_add (a b: ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b): |a - b| ≤ |a + b| := by
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  .
    rw [le_abs]
    grind
  . rw [le_abs]
    grind

lemma norm_sub_squared_le (a b : ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b): (a - b)^2 ≤ |a^2 - b^2| := by
  conv =>
    lhs
    rw [← sq_abs]
    rw [pow_two]

  rw [sq_sub_sq]
  rw [abs_mul]
  nth_rw 2 [mul_comm]
  -- TODO - why doesn't grw work here?
  apply mul_le_mul
  . simp
  . apply abs_sub_le_abs_add a b ha hb
  . simp
  . simp


@[expose]
def f_n_conv_delta_tendsto: Prop :=  ∀ s: S, Filter.Tendsto (fun n: ℕ => MeasureTheory.eLpNorm (f_n n - (Conv (f_n n) (delta s.val))) 1 MeasureTheory.volume) Filter.atTop (nhds 0)


lemma f_conv_delta_helper (f: G → ℝ) (s: G): (Conv  f (delta s)) = fun g => f (s⁻¹ * g) := by
  funext g
  exact f_conv_delta f g s


-- Lemma 3.16 in Vikman

-- The case split statement in Vikman

lemma F_n_conv_mu_lim (f_n_limit: f_n_conv_delta_tendsto):
    Filter.Tendsto (fun n => ‖(F_n_lp2 n) - conv_mu_lp2 (F_n_lp2 n)‖ₑ) Filter.atTop (nhds 0) := by

  have f_n_sub_norm: ∀ s ∈ S, ∀ (i : ℕ), ∑' (g : G), ‖f_n i g - f_n i (s * g)‖ₑ ≠ ⊤ := by
    intro s hs n
    have foo := f_n_norm_one n
    rw [← lt_top_iff_ne_top]
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)] at foo
    rw [lintegral_g_eq_add] at foo
    simp at foo
    grw [ENNReal.tsum_le_tsum (g := fun g => ‖f_n n g‖ₑ + ‖(f_n n (s * g))‖ₑ)]
    .
      rw [ENNReal.tsum_add]
      rw [ENNReal.add_lt_top]
      . refine ⟨?_, ?_⟩
        . simp [foo]
        .
          grw [ENNReal.tsum_comp_le_tsum_of_injective (g := fun a =>  ‖f_n n a‖ₑ)]
          .
            simp [foo]
          . intro a b hab
            simpa using hab
    .
      intro a
      grw [enorm_sub_le]

  rw [← ENNReal.tendsto_toReal_iff]
  .
    have S_ne: (#S : ℝ) ≠ 0 := by
      simp
      have foo := hGS.hS
      simp at foo
      grind

    simp_rw [MeasureTheory.Lp.enorm_def]
    simp_rw [conv_mu_lp2, f_conv_mu]
    simp_rw [ae_eq_everywhere.mp (MeasureTheory.Lp.coeFn_sub _ _)]
    simp_rw [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
    conv =>
      arg 1
      intro n
      arg 1
      arg 1
      lhs
      equals (1 / (#S : ℝ)) • ∑ s ∈ S, ↑↑(F_n_lp2 n) =>
        simp
        conv =>
          rhs
          equals ((#S : ℝ))⁻¹ • (#S : ℝ) • (F_n_lp2 n).val.cast =>
            norm_cast
            simp
        simp [S_ne]

    conv =>
      arg 1
      intro n
      arg 1
      arg 1
      rhs
      equals (1 / ↑(#S : ℝ)) • ∑ s ∈ S, (fun g => (F_n_lp2 n) (s * g)) =>
        ext a
        simp

    simp_rw [← smul_sub]
    simp_rw [← Finset.sum_sub_distrib]
    rw [ENNReal.toReal_zero]


    apply squeeze_zero (g := fun n => (1 / ↑(#S : ℝ)) • ∑ x ∈ S, (eLpNorm ((F_n_lp2 n).val.cast - (fun (g: G) => (F_n_lp2 n) (x * g))) 2 volume).toReal)
    . simp
    .
      intro n
      rw [eLpNorm_const_smul]
      grw [eLpNorm_sum_le]
      .
        simp
        rw [ENNReal.toReal_sum]
        intro s hs
        rw [← lt_top_iff_ne_top]
        grw [eLpNorm_sub_le]
        .
          rw [ENNReal.add_lt_top]
          . refine ⟨?_, ?_⟩
            . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
            .
              simp_rw [← Function.comp_def]
              rw [MeasureTheory.eLpNorm_comp_measurePreserving]
              . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
              . apply AEStronglyMeasurable.of_discrete
              . exact measurePreserving_mul_left volume s
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . simp
      .
        apply ENNReal.mul_ne_top (by simp)
        rw [ENNReal.sum_ne_top]
        -- TODO - deduplicate this
        intro s hs
        rw [← lt_top_iff_ne_top]
        grw [eLpNorm_sub_le]
        .
          rw [ENNReal.add_lt_top]
          . refine ⟨?_, ?_⟩
            . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
            .
              simp_rw [← Function.comp_def]
              rw [MeasureTheory.eLpNorm_comp_measurePreserving]
              . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
              . apply AEStronglyMeasurable.of_discrete
              . exact measurePreserving_mul_left volume s
        . apply AEStronglyMeasurable.of_discrete
        . apply AEStronglyMeasurable.of_discrete
        . simp
      . intro s hs
        apply AEStronglyMeasurable.of_discrete
      . simp
    .
      conv =>
        rhs
        equals nhds ((1 / ↑(#S : ℝ)) • 0) =>
          simp

      apply Filter.Tendsto.const_smul
      conv =>
        rhs
        equals nhds (∑ x_1 ∈ S⁻¹, (0: ℝ)) =>
          simp
      conv =>
        arg 1
        intro x
        arg 1
        equals S⁻¹ =>
          apply S_eq_Sinv
      apply tendsto_finset_sum
      intro s hs
      conv =>
        arg 1
        intro n
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)]
        rw [lintegral_g_eq_add]

      simp
      apply squeeze_zero (g := (fun n ↦ ((∑' (g : G), ‖(f_n n) g - (f_n n) (s * g)‖ₑ) ^ (2 : ℝ)⁻¹).toReal))
      . simp
      .
        intro n
        rw [ENNReal.toReal_le_toReal]
        .
          apply ENNReal.rpow_le_rpow
          .
            apply ENNReal.tsum_le_tsum
            intro g
            rw [Real.enorm_eq_ofReal_abs]
            rw [Real.enorm_eq_ofReal_abs]
            rw [← ENNReal.ofReal_pow]
            .
              apply ENNReal.ofReal_le_ofReal
              simp [F_n_lp2]
              simp [ae_eq_everywhere.mp (MeasureTheory.MemLp.coeFn_toLp _)]
              simp [F_n]
              conv =>
                rhs
                arg 1
                equals (Real.sqrt (f_n n g))^2 - (Real.sqrt (f_n n (s * g)))^2 =>
                  rw [Real.sq_sqrt]
                  .
                    rw [Real.sq_sqrt]
                    . apply f_n_nonneg
                  . apply f_n_nonneg

              apply norm_sub_squared_le
              . simp
              . simp
            . simp
          . simp
        .
          rw [← lt_top_iff_ne_top]
          have norm_sub_lt: eLpNorm (((F_n_lp2 n).val.cast) - ((F_n_lp2 n) ∘ fun a ↦ s * a)) 2 volume < ⊤ := by
            grw [eLpNorm_sub_le]
            rw [ENNReal.add_lt_top]
            refine ⟨?_, ?_⟩
            . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
            .
              rw [MeasureTheory.eLpNorm_comp_measurePreserving]
              . exact Lp.eLpNorm_lt_top (F_n_lp2 n)
              . apply AEStronglyMeasurable.of_discrete
              . exact measurePreserving_mul_left volume s
            . apply AEStronglyMeasurable.of_discrete
            . apply AEStronglyMeasurable.of_discrete
            . simp
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)] at norm_sub_lt
          rw [lintegral_g_eq_add] at norm_sub_lt
          simp at norm_sub_lt
          exact norm_sub_lt
        .
          apply ENNReal.rpow_ne_top_of_nonneg
          . simp
          . apply f_n_sub_norm s (by rw [S_eq_Sinv]; simp [hs])
      .
        unfold f_n_conv_delta_tendsto at f_n_limit
        simp at hs
        specialize f_n_limit ⟨s⁻¹, hs⟩
        conv at f_n_limit =>
          arg 1
          intro n
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by simp) (by simp)]
          rw [lintegral_g_eq_add]

        simp_rw [f_conv_delta_helper] at f_n_limit
        simp at f_n_limit
        conv =>
          rhs
          equals nhds (0 ^ (2 : ℝ)⁻¹) =>
            simp
        simp_rw [← ENNReal.toReal_rpow]
        apply Filter.Tendsto.rpow_const
        .
          rw [← ENNReal.tendsto_toReal_iff] at f_n_limit
          . exact f_n_limit
          .
            apply f_n_sub_norm s (by rw [S_eq_Sinv]; simp [hs])
          . simp
        . simp
  . intro n
    rw [MeasureTheory.Lp.enorm_def]
    apply MeasureTheory.Lp.eLpNorm_ne_top
  . simp

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.Harmonic_SelfAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Self-adjointness and the spectrum of the Laplacian

`laplace_self_adjoint`, `laplace_positive_semidefinite`, and that `0` lies in the spectrum of
`Δ`.
-/


set_option linter.style.cdot false
set_option linter.style.whitespace false
attribute [local implicit_reducible] Additive

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

variable {V: Submodule ℝ LipschitzH} [V_finite: FiniteDimensional ℝ V] [Nontrivial V]

open scoped Finset
open scoped Pointwise
open scoped Convolution
open MeasureTheory

open scoped RealInnerProductSpace


lemma F_n_norm_eq_one: ∀ n, MeasureTheory.eLpNorm (F_n n) 2 MeasureTheory.volume (α := G) = 1 := by
  simp [eLpNorm, eLpNorm', lintegral_g_eq_add]
  simp [F_n, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow]

  intro n
  simp [f_n_nonneg]
  have norm_one := f_n_norm_one (n)
  simp [eLpNorm, eLpNorm', lintegral_g_eq_add] at norm_one
  simp_rw [Real.enorm_eq_ofReal_abs] at norm_one
  simp [f_n_nonneg, abs_of_nonneg] at norm_one
  simp [norm_one]


open scoped RealInnerProductSpace

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.MatrixSubsum_Subsums
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subset sums of matrix powers

The `DerivedSets` machinery and the estimate `subsums_unique`: distinct subsets of `[a,b)` give
distinct sums of `Aᵏ • v` when `A` has an eigenvalue of norm `≥ 3`.
-/


open scoped Finset
open scoped Pointwise

structure DerivedSets {R: Type*} [NormedCommRing R] {n: ℕ} (A: Matrix (Fin n) (Fin n) R) (v : (Fin n) → R) (p q : Finset ℕ) where
  h_prime: (p \ q).sum (fun k => A^k • v) = (q \ p).sum (fun k => A^k • v)
  supp_disj: Disjoint (p \ q) (q \ p)
end

section
-- module Solutions.OAIQ093_PR.Unitary_Basic
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subgroups of the unitary group

Properness and compactness of the unitary group, the transfer of polynomial growth along a
group isomorphism, and the distance estimate `small_dist_matrix`.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


@[expose]
def G' (n : ℕ) (ε : ℝ) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) : Subgroup G :=
  Subgroup.closure (Metric.ball (1 : G) ε)


-- Lemma 3.31 (Volume Packing)
end

section
-- module Solutions.OAIQ093_PR.Unitary_Packing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Volume packing in the unitary group

`volume_packing`, bounding how many almost-orthogonal translates fit in a ball, together with
the auxiliary inner product `FreshInnerProduct`.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


@[expose]
def FreshInnerProduct (V : Type*) := V


attribute [-simp] MeasureTheory.Measure.inv_eq_self

attribute [local implicit_reducible] FreshInnerProduct
end

section
-- module Solutions.OAIQ093_PR.FormalConjecturesCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cross-check of `main_gromov_theorem` against the `formal-conjectures` statement

The definitions `CayleyBall`, `GrowthFunction` and `HasPolynomialGrowth` below are copied
verbatim from the `formal-conjectures` repository (Apache-2.0):

* <https://github.com/google-deepmind/formal-conjectures>,
  `FormalConjecturesForMathlib/Algebra/Group/GrowthFunction.lean`
* the theorem being checked against is `GromovPolynomialGrowth.GromovPolynomialGrowthTheorem` in
  `FormalConjectures/Wikipedia/GromovPolynomialGrowth.lean`.

They are reproduced here rather than imported because that repository pins a different Lean
toolchain and Mathlib revision than this development.

The reference statement is an `Iff`:
```
theorem GromovPolynomialGrowthTheorem [Group.FG G] :
    HasPolynomialGrowth G ↔ Group.IsVirtuallyNilpotent G
```
This development proves the forward (hard) direction, `gromov_forward` below.  The converse
(Bass-Guivarc'h: a virtually nilpotent group has polynomial growth) is *not* proved here, so this
file does not discharge the reference `sorry` on its own.

The two statements measure growth differently -- balls `CayleyBall S n` of words of length `≤ n`
in `S ∪ S⁻¹` there, versus `S ^ n` for a symmetric `S ∋ 1` here -- so the bridge is
`coe_normGen_pow`, which says the two agree once the generating set is normalized.
-/


set_option linter.style.longLine false

namespace FormalConjecturesCheck

open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### Definitions copied from `formal-conjectures` -/

/-- The `CayleyBall` is the ball of radius `n` in the Cayley graph of a group `G` with generating
set `S`. -/
@[expose]
def CayleyBall (S : Set G) (n : ℕ) : Set G :=
  {g : G | ∃ (l : List G), l.length ≤ n ∧ (∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S) ∧ l.prod = g}

/-- The `GrowthFunction` of a group `G` with respect to a set `S` counts the number of group
elements that can be reached by words of length at most `n` in `S`. -/
@[expose]
noncomputable def GrowthFunction (S : Set G) (n : ℕ) : ℕ :=
  (CayleyBall S n).ncard

/-- A group has polynomial growth if there exists a finite generating set whose growth function is
bounded above by a polynomial. -/
@[expose]
def HasPolynomialGrowth (G : Type*) [Group G] : Prop :=
  ∃ (S : Set G), Set.Finite S ∧ Subgroup.closure S = ⊤ ∧
    ∃ (C : ℝ) (d : ℕ), C > 0 ∧
    ∀ n > 0, (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d

/-! ### Normalizing the generating set -/

variable [DecidableEq G]

/-- `S ∪ S⁻¹ ∪ {1}` as a `Finset`: the symmetric, `1`-containing generating set that
`Generates` requires. -/
@[expose]
noncomputable def normGen (S : Set G) (hS : S.Finite) : Finset G :=
  insert 1 (hS.toFinset ∪ hS.toFinset⁻¹)

/-! ### The forward direction of the reference statement -/

end FormalConjecturesCheck
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousWordCoefficients
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite right-nested coefficients of homogeneous primitive words -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {n d : ℕ}

def wordOfFn (w : Fin d → Fin n) : FreeMonoid (Fin n) :=
  FreeMonoid.ofList (List.ofFn w)

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end


