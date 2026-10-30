-- Prove2me | Definitions.Def_OAIQ096A000
-- name    : OAIQ096A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:28:57.039839+00:00
-- url     : https://prove2.me/theorems/baf32840-6c8c-4d64-90a7-31a5c9d5bf4f
-- title:
--   Definitions bundle OAIQ096A000 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 336 declarations of OpenAI's Lean: 55 definitions, 1 inductive type or structure, 8 instances and 272 theorems. The definitions and types are `CS`, `CS.deriv`, `CS.neg`, `CS.scale`, `CS.smul`, `Erdos970.Bf`, `Erdos970.Cf`, `Erdos970.Err`, `Erdos970.H_auxiliary`, `Erdos970.I`, `Erdos970.If_ext`, `Erdos970.If_taxicab`, `Erdos970.Lf`, `Erdos970.S_horiz`, `Erdos970.S_max`, `Erdos970.S_vert`, `Erdos970.ballDR`, `Erdos970.f_M`, `Erdos970.zerosetKfR`, `LinearMap.extendOfIsometry`, `MeasureTheory.Lp.extendByZeroFun`, `MeasureTheory.Lp.extendByZeroₗ`, `MeasureTheory.Lp.extendByZeroₗᵢ`, `OAI.CubicFirstMoment.AngularGammaQuotientStripBound`, `OAI.CubicFirstMoment.EisensteinArithmeticFunction`, `OAI.CubicFirstMoment.EisensteinIdealExponent`, `OAI.CubicFirstMoment.EisensteinIdealPrime`, `OAI.CubicFirstMoment.angularConductorFactor`, `OAI.CubicFirstMoment.angularGammaFEQuotient`, `OAI.CubicFirstMoment.angularKummerConductorFactor`, `OAI.CubicFirstMoment.conjugate`, `OAI.CubicFirstMoment.coordinatesEquiv`, `OAI.CubicFirstMoment.coordinatesMap`, `OAI.CubicFirstMoment.cubicResidueChar`, `OAI.CubicFirstMoment.cubicResidueCharE`, `OAI.CubicFirstMoment.cubicSymbol`, `OAI.CubicFirstMoment.heckeCompleted`, `OAI.CubicFirstMoment.integerBasis`, `OAI.CubicFirstMoment.latticeQuotient`, `OAI.CubicFirstMoment.latticeRemainder` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_Conjugation`, `CubicGram_Coordinates`, `CubicGram_EuclideanDomain`, `CubicGram_GaussCharacters`, `CubicGram_IntegerBasis`, `CubicGram_Jacobi`, `CubicGram_LatticeCounts`, `CubicGram_MixedPoisson`, `CubicGram_PrimaryNormalization`, `CubicGram_Reciprocity`, `CubicGram_ReciprocityKernel`, `CubicGram_ResidueCharacters`, `CubicGram_SquarefreeGauss`, `CubicMoment_Angular_AngularAlgebra`, `CubicMoment_Angular_AngularDualContour`, `CubicMoment_Estimates_DispersionAlgebra`, `CubicMoment_Estimates_FixedAngularHecke`, `CubicMoment_Estimates_HeckeFunctionalEquation`, `CubicMoment_Estimates_IdealEulerExclusion`, `CubicMoment_Estimates_MixedResidueCharacters`, `CubicMoment_Estimates_PublishedAngularKummerPrime`, `CubicMoment_Estimates_PublishedHecke`, `CubicMoment_Estimates_ShortMoebius`, `CubicMoment_Estimates_ShortMoebiusFinite`, `Erdos970_PNT1_ComplexAnalysis`, `Erdos970_PNT2_LogDerivative`, `Fourier`, `MeasureTheory_Function_LpSpace_Restrict`, `Sobolev`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A004`, `OAIQ096A005` and `OAIQ096A006`; the statements `OAI_CubicFirstMoment_all_frequency_outer_sieve` and `OAI.CubicFirstMoment.bounded_cubic_moment`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment

section
-- module Solutions.OAIQ096_CM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
section X
variable {𝕜 𝕜₂ E Eₗ F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup Eₗ] [NormedSpace 𝕜 Eₗ] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F] [CompleteSpace F]

/-- d13f23b's `LinearMap.extendOfIsometry`: a semilinear map into a complete space that agrees in norm
with a dense-range map `e` extends along `e` to a semilinear isometry. -/
noncomputable def _root_.LinearMap.extendOfIsometry (f : E →ₛₗ[σ] F) {e : E →ₗ[𝕜] Eₗ}
    (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) : Eₗ →ₛₗᵢ[σ] F :=
  { toLinearMap := (f.extendOfNorm e).toLinearMap
    norm_map' := by
      intro x
      refine h_dense.induction_on x (isClosed_eq (by fun_prop) continuous_norm) ?_
      intro y
      have := LinearMap.extendOfNorm_eq (f := f) (e := e) h_dense ⟨1, by simp [h_norm]⟩ y
      simp only [ContinuousLinearMap.coe_coe, this, h_norm] }

omit [RingHomIsometric σ] in
theorem _root_.LinearMap.extendOfIsometry_eq (f : E →ₛₗ[σ] F) {e : E →ₗ[𝕜] Eₗ}
    (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) (x : E) :
    f.extendOfIsometry h_dense h_norm (e x) = f x :=
  LinearMap.extendOfNorm_eq (f := f) (e := e) h_dense ⟨1, by simp [h_norm]⟩ x
end X
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral coordinates and finite norm cutoffs in the Eisenstein subring. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
lemma omega_eq : omega = (-1 / 2 : ℂ) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I / 3 =
      ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [omega, harg, Complex.exp_mul_I]
  have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hcos, hsin]
  push_cast
  ring

@[simp] lemma omega_re : omega.re = -1 / 2 := by rw [omega_eq]; simp
@[simp] lemma omega_im : omega.im = Real.sqrt 3 / 2 := by rw [omega_eq]; simp

lemma omega_quadratic : omega ^ 2 + omega + 1 = 0 := by
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im]
  · nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · ring

lemma exists_coordinates (z : Eisenstein) : ∃ a b : ℤ, (z : ℂ) = a + b * omega := by
  refine Algebra.adjoin_induction (p := fun z _ => ∃ a b : ℤ, z = a + b * omega)
    ?_ ?_ ?_ ?_ z.property
  · intro x hx
    obtain rfl : x = omega := Set.mem_singleton_iff.mp hx
    exact ⟨0, 1, by simp⟩
  · intro a
    exact ⟨a, 0, by simp⟩
  · rintro x y _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    refine ⟨a+c,b+d,?_⟩
    push_cast
    ring
  · rintro x y _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    refine ⟨a*c-b*d, a*d+b*c-b*d, ?_⟩
    have h : omega ^ 2 = -omega - 1 := by linear_combination omega_quadratic
    push_cast
    ring_nf
    rw [h]
    ring

lemma coordinates_norm (a b : ℤ) :
    Complex.normSq ((a : ℂ) + b * omega) = ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im, omega_re, omega_im]
  push_cast
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma coordinates_unique {a b c d : ℤ}
    (h : (a : ℂ) + b * omega = (c : ℂ) + d * omega) : a = c ∧ b = d := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, omega_im, omega_re, zero_mul, add_zero, zero_add] at him
  have hs : (Real.sqrt 3 / 2 : ℝ) ≠ 0 := by positivity
  have hb : b = d := by
    exact_mod_cast mul_right_cancel₀ hs him
  subst d
  have ha : (a : ℂ) = c := add_right_cancel h
  exact ⟨by exact_mod_cast ha, rfl⟩

lemma norm_nonneg (z : Eisenstein) : 0 ≤ norm z := Complex.normSq_nonneg _

lemma normNat_cast (z : Eisenstein) : (normNat z : ℝ) = norm z := by
  obtain ⟨a,b,hz⟩ := exists_coordinates z
  have hn : norm z = ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) := by
    rw [norm, hz, coordinates_norm]
  have hm : 0 ≤ a ^ 2 - a * b + b ^ 2 := by exact_mod_cast hn ▸ norm_nonneg z
  have hn' : norm z = ((a ^ 2 - a * b + b ^ 2).toNat : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm, hn]
  rw [normNat, hn', Nat.floor_natCast]

def ofCoords (a b : ℤ) : Eisenstein := a + b * omegaE

@[simp] lemma ofCoords_coe (a b : ℤ) : (ofCoords a b : ℂ) = a + b * omega := rfl

lemma ofCoords_surjective : Function.Surjective (fun p : ℤ × ℤ => ofCoords p.1 p.2) := by
  intro z
  obtain ⟨a,b,h⟩ := exists_coordinates z
  exact ⟨(a,b), Subtype.ext h.symm⟩

lemma finite_norm_le (X : ℝ) : Set.Finite {z : Eisenstein | norm z ≤ X} := by
  let C : ℤ := ⌈2 * X + 1⌉
  have hC : 2 * X + 1 ≤ (C : ℝ) := Int.le_ceil _
  apply ((Set.finite_Icc (-C) C).prod (Set.finite_Icc (-C) C)).image
    (fun p : ℤ × ℤ => ofCoords p.1 p.2) |>.subset
  intro z hz
  obtain ⟨a,b,hz'⟩ := exists_coordinates z
  have hn : (a : ℝ)^2 - a*b + b^2 ≤ X := by
    have hh : norm z = ((a ^ 2 - a*b + b^2 : ℤ) : ℝ) := by
      rw [norm, hz', coordinates_norm]
    change norm z ≤ X at hz
    rw [hh] at hz
    exact_mod_cast hz
  have ha : -(C : ℝ) ≤ (a : ℝ) ∧ (a : ℝ) ≤ C := by
    constructor <;> nlinarith [sq_nonneg ((a : ℝ) - b), sq_nonneg (b : ℝ),
      sq_nonneg ((a : ℝ) - 1), sq_nonneg ((a : ℝ) + 1)]
  have hb : -(C : ℝ) ≤ (b : ℝ) ∧ (b : ℝ) ≤ C := by
    constructor <;> nlinarith [sq_nonneg ((a : ℝ) - b), sq_nonneg (a : ℝ),
      sq_nonneg ((b : ℝ) - 1), sq_nonneg ((b : ℝ) + 1)]
  refine ⟨(a,b), ?_, Subtype.ext hz'.symm⟩
  constructor
  · exact ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
  · exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩

def primeCutoff (X : ℝ) : Finset Eisenstein :=
  ((finite_norm_le X).subset
    (show {p | primaryPrime p ∧ norm p ≤ X} ⊆ {p | norm p ≤ X} from
      fun _ h => h.2)).toFinset

@[simp] lemma mem_primeCutoff {p : Eisenstein} {X : ℝ} :
    p ∈ primeCutoff X ↔ primaryPrime p ∧ norm p ≤ X := Set.Finite.mem_toFinset _

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_IntegerBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral basis, multiplication norm and finite residue quotients. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
def coordinatesMap : (Fin 2 → ℤ) →ₗ[ℤ] Eisenstein where
  toFun v := ofCoords (v 0) (v 1)
  map_add' v w := by simp [ofCoords, add_mul]; ring
  map_smul' n v := by simp [ofCoords]; ring

lemma coordinatesMap_bijective : Function.Bijective coordinatesMap := by
  constructor
  · intro v w h
    have hh := coordinates_unique (congrArg (fun z : Eisenstein => (z : ℂ)) h)
    funext i
    fin_cases i
    · exact hh.1
    · exact hh.2
  · intro z
    obtain ⟨a,b,h⟩ := exists_coordinates z
    exact ⟨![a,b], Subtype.ext h.symm⟩

def coordinatesEquiv : (Fin 2 → ℤ) ≃ₗ[ℤ] Eisenstein :=
  LinearEquiv.ofBijective coordinatesMap coordinatesMap_bijective

def integerBasis : Basis (Fin 2) ℤ Eisenstein :=
  (Pi.basisFun ℤ (Fin 2)).map coordinatesEquiv

instance instFreeIntSubtypeComplexMemSubalgebraEisenstein : Module.Free ℤ Eisenstein := Module.Free.of_basis integerBasis
instance instFiniteIntSubtypeComplexMemSubalgebraEisenstein : Module.Finite ℤ Eisenstein := Module.Finite.of_basis integerBasis

@[simp] lemma integerBasis_zero : integerBasis 0 = 1 := by
  simp [integerBasis, coordinatesEquiv, coordinatesMap, ofCoords, Pi.basisFun_apply]

@[simp] lemma integerBasis_one : integerBasis 1 = omegaE := by
  simp [integerBasis, coordinatesEquiv, coordinatesMap, ofCoords, Pi.basisFun_apply]

lemma integerBasis_repr_ofCoords (a b : ℤ) :
    integerBasis.repr (ofCoords a b) = Finsupp.equivFunOnFinite.symm ![a,b] := by
  apply Finsupp.equivFunOnFinite.injective
  change coordinatesEquiv.symm (ofCoords a b) = ![a,b]
  apply coordinatesEquiv.injective
  simp only [LinearEquiv.apply_symm_apply]
  rfl

lemma ofCoords_mul (a b c d : ℤ) :
    ofCoords a b * ofCoords c d = ofCoords (a*c-b*d) (a*d+b*c-b*d) := by
  apply Subtype.ext
  change ((a : ℂ) + b * omega) * (c + d * omega) = _
  rw [ofCoords_coe]
  have h : omega^2 = -omega - 1 := by linear_combination omega_quadratic
  push_cast
  ring_nf
  rw [h]
  ring

lemma ofCoords_mul_omega (a b : ℤ) : ofCoords a b * omegaE = ofCoords (-b) (a-b) := by
  rw [show omegaE = ofCoords 0 1 by simp [ofCoords], ofCoords_mul]
  simp

lemma leftMulMatrix_ofCoords (a b : ℤ) :
    Algebra.leftMulMatrix integerBasis (ofCoords a b) = !![a, -b; b, a-b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.leftMulMatrix_eq_repr_mul, ofCoords_mul_omega, integerBasis_repr_ofCoords]

lemma algebra_norm_ofCoords (a b : ℤ) :
    Algebra.norm ℤ (ofCoords a b) = a^2 - a*b + b^2 := by
  rw [Algebra.norm_eq_matrix_det integerBasis, leftMulMatrix_ofCoords, Matrix.det_fin_two]
  simp
  ring

lemma algebra_norm_cast (z : Eisenstein) : (Algebra.norm ℤ z : ℝ) = norm z := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective z
  rw [algebra_norm_ofCoords, norm, ofCoords_coe, coordinates_norm]

lemma residues_card {z : Eisenstein} (hz : z ≠ 0) : Nat.card (Residues z) = normNat z := by
  have hdet := Submodule.natAbs_det_basis_change integerBasis
    ((modulus z).restrictScalars ℤ) (Ideal.basisSpanSingleton integerBasis hz)
  have hh : integerBasis.det (fun i =>
      ((Ideal.basisSpanSingleton integerBasis hz i : modulus z) : Eisenstein)) =
      Algebra.norm ℤ z := by
    rw [Algebra.norm_eq_matrix_det integerBasis, Basis.det_apply]
    congr 1
    ext i j
    simp [Basis.toMatrix_apply, Ideal.basisSpanSingleton_apply,
      Algebra.leftMulMatrix_eq_repr_mul]
  change (integerBasis.det (fun i =>
    ((Ideal.basisSpanSingleton integerBasis hz i : modulus z) : Eisenstein))).natAbs =
    Nat.card (Residues z) at hdet
  rw [hh] at hdet
  have hn : 0 ≤ Algebra.norm ℤ z := by
    exact_mod_cast (algebra_norm_cast z).symm ▸ norm_nonneg z
  rw [← hdet]
  apply Nat.cast_injective (R := ℝ)
  rw [normNat_cast, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hn, algebra_norm_cast]

lemma norm_eq_zero_iff {z : Eisenstein} : norm z = 0 ↔ z = 0 := by
  rw [norm, Complex.normSq_eq_zero]
  constructor
  · exact fun h => Subtype.ext h
  · rintro rfl
    rfl

lemma normNat_ne_zero {z : Eisenstein} (hz : z ≠ 0) : normNat z ≠ 0 := by
  intro h
  apply hz
  apply norm_eq_zero_iff.mp
  rw [← normNat_cast, h, Nat.cast_zero]

lemma finite_residues {z : Eisenstein} (hz : z ≠ 0) : Finite (Residues z) :=
  Nat.finite_of_card_ne_zero (by rw [residues_card hz]; exact normNat_ne_zero hz)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_ResidueCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive cube roots, Euler residue characters and additive trace phases. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
lemma omega_cube : omega ^ 3 = 1 := by
  linear_combination (omega - 1) * omega_quadratic

lemma omegaE_quadratic : omegaE ^ 2 + omegaE + 1 = 0 := by
  apply Subtype.ext
  exact omega_quadratic

lemma omegaE_cube : omegaE ^ 3 = 1 := by
  apply Subtype.ext
  exact omega_cube

lemma omegaE_difference_product : (omegaE - 1) * (omegaE ^ 2 - 1) = 3 := by
  linear_combination (omegaE - 2) * omegaE_quadratic

lemma primaryPrime_not_dvd_three {p : Eisenstein} (hp : primaryPrime p) :
    ¬ p ∣ (3 : Eisenstein) := by
  intro h
  have hh : p ∣ p - 1 := dvd_trans h hp.1
  have h1 : p ∣ 1 := by simpa using dvd_sub (dvd_refl p) hh
  exact hp.2.not_isUnit (isUnit_of_dvd_one h1)

lemma residue_omega_primitive {p : Eisenstein} (hp : primaryPrime p) :
    IsPrimitiveRoot (Ideal.Quotient.mk (modulus p) omegaE) 3 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  apply isPrimitiveRoot_of_mem_nthRootsFinset (by norm_num : Nat.Prime 3)
  · rw [Polynomial.mem_nthRootsFinset (by norm_num : 0 < 3)]
    rw [← map_pow, omegaE_cube, map_one]
  · intro heq
    have hd : p ∣ omegaE - 1 := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      change Ideal.Quotient.mk (modulus p) (omegaE - 1) = 0
      rw [map_sub, map_one, heq, sub_self]
    apply primaryPrime_not_dvd_three hp
    rw [← omegaE_difference_product]
    exact dvd_mul_of_dvd_left hd _

lemma primaryPrime_norm_sub_one_dvd_three {p : Eisenstein} (hp : primaryPrime p) :
    3 ∣ normNat p - 1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have hω := residue_omega_primitive hp
  apply hω.dvd_of_pow_eq_one
  rw [← residues_card hp.2.ne_zero, Nat.card_eq_fintype_card]
  apply FiniteField.pow_card_sub_one_eq_one
  exact hω.isUnit (by norm_num : 3 ≠ 0) |>.ne_zero

lemma cubicSymbol_euler_exists_unique {p v : Eisenstein} (hp : primaryPrime p)
    (hv : IsUnit (Ideal.Quotient.mk (modulus p) v)) :
    ∃! j : Fin 3,
      Ideal.Quotient.mk (modulus p) (v ^ ((normNat p - 1) / 3)) =
        Ideal.Quotient.mk (modulus p) (omegaE ^ (j : ℕ)) := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have heuler : (Ideal.Quotient.mk (modulus p) v ^ ((normNat p - 1) / 3)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel (primaryPrime_norm_sub_one_dvd_three hp)]
    rw [← residues_card hp.2.ne_zero, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ hv.ne_zero
  obtain ⟨j,hj,heq⟩ := (residue_omega_primitive hp).eq_pow_of_pow_eq_one heuler
  refine ⟨⟨j,hj⟩, ?_, ?_⟩
  · simpa only [map_pow] using heq.symm
  · intro k hk
    apply Fin.ext
    apply (residue_omega_primitive hp).pow_inj k.isLt hj
    simpa only [map_pow] using hk.symm.trans (by simpa only [map_pow] using heq.symm)

lemma residueRepresentative_spec (p : Eisenstein) (v : Residues p) :
    Ideal.Quotient.mk (modulus p) (residueRepresentative p v) = v :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective v)

lemma cubicSymbolAtPrime_congr {p v w : Eisenstein}
    (h : Ideal.Quotient.mk (modulus p) v = Ideal.Quotient.mk (modulus p) w) :
    cubicSymbolAtPrime p v = cubicSymbolAtPrime p w := by
  simp only [cubicSymbolAtPrime, map_pow, h]

lemma trace_ofCoords (a b : ℤ) :
    (ofCoords a b : ℂ) + star (ofCoords a b : ℂ) = (2*a-b : ℤ) := by
  apply Complex.ext
  · simp [ofCoords_coe, Complex.add_re, Complex.mul_re, omega_re]
    ring
  · simp

lemma trace_integral (z : Eisenstein) : ∃ n : ℤ, (z : ℂ) + star (z : ℂ) = n := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective z
  exact ⟨2*a-b, trace_ofCoords a b⟩

lemma additivePhase_add_multiple {p : Eisenstein} (hp : p ≠ 0) (v w : Eisenstein) :
    additivePhase p (v + p*w) = additivePhase p v := by
  have hp' : (p : ℂ) ≠ 0 := fun h => hp (Subtype.ext h)
  obtain ⟨n,hn⟩ := trace_integral w
  have hdiv : ((v + p*w : Eisenstein) : ℂ) / (p : ℂ) =
      (v : ℂ) / (p : ℂ) + (w : ℂ) := by
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, add_div]
    rw [mul_div_cancel_left₀ _ hp']
  unfold additivePhase
  dsimp only
  rw [hdiv, star_add]
  have harg : 2 * (Real.pi : ℂ) * Complex.I *
      ((v : ℂ) / (p : ℂ) + (w : ℂ) +
        (star ((v : ℂ) / (p : ℂ)) + star (w : ℂ))) =
      2 * (Real.pi : ℂ) * Complex.I *
        ((v : ℂ) / (p : ℂ) + star ((v : ℂ) / (p : ℂ))) +
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [← hn]
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma additivePhase_congr {p v w : Eisenstein} (hp : p ≠ 0)
    (h : Ideal.Quotient.mk (modulus p) v = Ideal.Quotient.mk (modulus p) w) :
    additivePhase p v = additivePhase p w := by
  have hd : p ∣ v-w := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    change Ideal.Quotient.mk (modulus p) (v-w) = 0
    rw [map_sub, h, sub_self]
  obtain ⟨t,ht⟩ := hd
  have hv : v = w + p*t := by linear_combination ht
  rw [hv, additivePhase_add_multiple hp]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GaussCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicative and additive characters and normalized prime Gauss sums. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
lemma cube_pow_mod {M : Type*} [Monoid M] {x : M} (hx : x^3 = 1) (n : ℕ) :
    x ^ (n % 3) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3]
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

lemma cubicSymbol_euler_value {p v : Eisenstein} (hp : primaryPrime p)
    (hv : IsUnit (Ideal.Quotient.mk (modulus p) v)) (j : Fin 3)
    (hj : Ideal.Quotient.mk (modulus p) (v ^ ((normNat p - 1) / 3)) =
      Ideal.Quotient.mk (modulus p) (omegaE ^ (j : ℕ))) :
    cubicSymbolAtPrime p v = omega ^ (j : ℕ) := by
  have he := (cubicSymbol_euler_exists_unique hp hv).exists
  rw [cubicSymbolAtPrime, ite_eq_left hv, dite_eq_left he]
  have hh := (cubicSymbol_euler_exists_unique hp hv).unique (Classical.choose_spec he) hj
  exact congrArg (fun k : Fin 3 => omega ^ (k : ℕ)) hh

lemma cubicSymbolAtPrime_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicSymbolAtPrime p 1 = 1 := by
  have he : Ideal.Quotient.mk (modulus p) ((1 : Eisenstein) ^ ((normNat p - 1) / 3)) =
      Ideal.Quotient.mk (modulus p) (omegaE ^ (0 : ℕ)) := by simp
  simpa using cubicSymbol_euler_value hp (by simp) 0 he

lemma cubicSymbolAtPrime_mul {p : Eisenstein} (hp : primaryPrime p) (v w : Eisenstein) :
    cubicSymbolAtPrime p (v*w) = cubicSymbolAtPrime p v * cubicSymbolAtPrime p w := by
  by_cases hv : IsUnit (Ideal.Quotient.mk (modulus p) v)
  · by_cases hw : IsUnit (Ideal.Quotient.mk (modulus p) w)
    · obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv
      obtain ⟨k,hk,_⟩ := cubicSymbol_euler_exists_unique hp hw
      have hjv := cubicSymbol_euler_value hp hv j hj
      have hkw := cubicSymbol_euler_value hp hw k hk
      let ℓ : Fin 3 := ⟨((j : ℕ) + (k : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩
      have hω : (Ideal.Quotient.mk (modulus p) omegaE) ^ 3 = 1 := by
        rw [← map_pow, omegaE_cube, map_one]
      have he : Ideal.Quotient.mk (modulus p) ((v*w) ^ ((normNat p - 1) / 3)) =
          Ideal.Quotient.mk (modulus p) (omegaE ^ (ℓ : ℕ)) := by
        simp only [map_pow] at hj hk ⊢
        rw [map_mul, mul_pow, hj, hk, ← pow_add]
        exact (cube_pow_mod hω _).symm
      have hvw : IsUnit (Ideal.Quotient.mk (modulus p) (v*w)) := by
        rw [map_mul]
        exact hv.mul hw
      rw [cubicSymbol_euler_value hp hvw ℓ he, hjv, hkw, ← pow_add]
      exact cube_pow_mod omega_cube _
    · have hvw : ¬ IsUnit (Ideal.Quotient.mk (modulus p) (v*w)) := by
        rw [map_mul, (Commute.all _ _).isUnit_mul_iff]
        tauto
      simp only [cubicSymbolAtPrime, hvw, hw, ite_false, if_false, mul_zero]
  · have hvw : ¬ IsUnit (Ideal.Quotient.mk (modulus p) (v*w)) := by
      rw [map_mul, (Commute.all _ _).isUnit_mul_iff]
      tauto
    simp only [cubicSymbolAtPrime, hvw, hv, ite_false, if_false, zero_mul]

def cubicResidueChar (p : Eisenstein) (hp : primaryPrime p) : MulChar (Residues p) ℂ where
  toFun x := cubicSymbolAtPrime p (residueRepresentative p x)
  map_one' := by
    rw [cubicSymbolAtPrime_congr (show
      Ideal.Quotient.mk (modulus p) (residueRepresentative p 1) =
        Ideal.Quotient.mk (modulus p) 1 by rw [residueRepresentative_spec, map_one])]
    exact cubicSymbolAtPrime_one hp
  map_mul' x y := by
    rw [cubicSymbolAtPrime_congr (show
      Ideal.Quotient.mk (modulus p) (residueRepresentative p (x*y)) =
        Ideal.Quotient.mk (modulus p) (residueRepresentative p x * residueRepresentative p y) by
          rw [map_mul, residueRepresentative_spec, residueRepresentative_spec,
            residueRepresentative_spec])]
    exact cubicSymbolAtPrime_mul hp _ _
  map_nonunit' x hx := by
    simp only [cubicSymbolAtPrime, residueRepresentative_spec, hx, ite_false, if_false]

@[simp] lemma cubicResidueChar_mk (p : Eisenstein) (hp : primaryPrime p) (v : Eisenstein) :
    cubicResidueChar p hp (Ideal.Quotient.mk (modulus p) v) = cubicSymbolAtPrime p v :=
  cubicSymbolAtPrime_congr (residueRepresentative_spec _ _)

lemma additivePhase_add (p v w : Eisenstein) :
    additivePhase p (v+w) = additivePhase p v * additivePhase p w := by
  unfold additivePhase
  dsimp only
  simp only [Subalgebra.coe_add, add_div, star_add]
  rw [show 2 * (Real.pi : ℂ) * Complex.I *
      ((v : ℂ)/(p : ℂ) + (w : ℂ)/(p : ℂ) +
        (star ((v : ℂ)/(p : ℂ)) + star ((w : ℂ)/(p : ℂ)))) =
      2 * (Real.pi : ℂ) * Complex.I * ((v : ℂ)/(p : ℂ) + star ((v : ℂ)/(p : ℂ))) +
      2 * (Real.pi : ℂ) * Complex.I * ((w : ℂ)/(p : ℂ) + star ((w : ℂ)/(p : ℂ))) by ring,
    Complex.exp_add]

@[simp] lemma additivePhase_zero (p : Eisenstein) : additivePhase p 0 = 1 := by
  simp [additivePhase]

def residueAddChar (p : Eisenstein) (hp : p ≠ 0) : AddChar (Residues p) ℂ where
  toFun x := additivePhase p (residueRepresentative p x)
  map_zero_eq_one' := by
    rw [additivePhase_congr hp (show
      Ideal.Quotient.mk (modulus p) (residueRepresentative p 0) =
        Ideal.Quotient.mk (modulus p) 0 by rw [residueRepresentative_spec, map_zero])]
    exact additivePhase_zero p
  map_add_eq_mul' x y := by
    rw [additivePhase_congr hp (show
      Ideal.Quotient.mk (modulus p) (residueRepresentative p (x+y)) =
        Ideal.Quotient.mk (modulus p) (residueRepresentative p x + residueRepresentative p y) by
          rw [map_add, residueRepresentative_spec, residueRepresentative_spec,
            residueRepresentative_spec])]
    exact additivePhase_add _ _ _

@[simp] lemma residueAddChar_mk (p : Eisenstein) (hp : p ≠ 0) (v : Eisenstein) :
    residueAddChar p hp (Ideal.Quotient.mk (modulus p) v) = additivePhase p v :=
  additivePhase_congr hp (residueRepresentative_spec _ _)

lemma gaussAtPrime_eq_gaussSum {p : Eisenstein} (hp : primaryPrime p) [Fintype (Residues p)] :
    gaussAtPrime p = (Real.sqrt (norm p) : ℂ)⁻¹ *
      gaussSum (cubicResidueChar p hp) (residueAddChar p hp.2.ne_zero) := by
  simp only [gaussAtPrime, gaussSum, tsum_fintype]
  rfl

lemma omega_primitive : IsPrimitiveRoot omega 3 := by
  apply isPrimitiveRoot_of_mem_nthRootsFinset (by norm_num : Nat.Prime 3)
  · rw [Polynomial.mem_nthRootsFinset (by norm_num : 0 < 3)]
    exact omega_cube
  · intro h
    have hh := congrArg Complex.re h
    simp only [omega_re, Complex.one_re] at hh
    norm_num at hh

lemma cubicResidueChar_ne_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicResidueChar p hp ≠ 1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  intro htriv
  have hpow (u : (Residues p)ˣ) : u ^ ((normNat p - 1) / 3) = 1 := by
    let v := residueRepresentative p (u : Residues p)
    have hv : IsUnit (Ideal.Quotient.mk (modulus p) v) := by
      rw [show Ideal.Quotient.mk (modulus p) v = u from residueRepresentative_spec _ _]
      exact u.isUnit
    obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv
    have hc : omega ^ (j : ℕ) = 1 := by
      rw [← cubicSymbol_euler_value hp hv j hj]
      change cubicResidueChar p hp u = 1
      rw [htriv, MulChar.one_apply u.isUnit]
    have hj0 : (j : ℕ) = 0 := omega_primitive.pow_inj j.isLt (by norm_num) (by simpa using hc)
    apply Units.ext
    simpa [map_pow, v, residueRepresentative_spec, hj0] using hj
  obtain ⟨u,hu⟩ := IsCyclic.exists_generator (α := (Residues p)ˣ)
  have horder := orderOf_eq_card_of_forall_mem_zpowers hu
  rw [Nat.card_units, residues_card hp.2.ne_zero] at horder
  have hdvd := orderOf_dvd_of_pow_eq_one (hpow u)
  rw [horder] at hdvd
  have hq : 1 < normNat p := by
    rw [← residues_card hp.2.ne_zero, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hpos : 0 < (normNat p - 1) / 3 := by
    exact Nat.div_pos (Nat.le_of_dvd (by omega) (primaryPrime_norm_sub_one_dvd_three hp))
      (by norm_num)
  have hle := Nat.le_of_dvd hpos hdvd
  have hlt : (normNat p - 1) / 3 < normNat p - 1 :=
    Nat.div_lt_self (by omega) (by norm_num)
  omega

lemma omega_star : star omega = -1 - omega := by
  apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
  norm_num

lemma trace_pair_lattice {z : ℂ} {n k : ℤ}
    (h₁ : z + star z = n) (h₂ : omega*z + star (omega*z) = k) :
    3*z = ((n-k : ℤ) : ℂ) + ((-n-2*k : ℤ) : ℂ)*omega := by
  push_cast
  rw [star_mul, omega_star] at h₂
  linear_combination (1-omega)*h₁ - (1+2*omega)*h₂ + 2*(z-star z)*omega_quadratic

lemma additivePhase_eq_one_iff {p v : Eisenstein} :
    additivePhase p v = 1 ↔ ∃ n : ℤ,
      (v : ℂ)/(p : ℂ) + star ((v : ℂ)/(p : ℂ)) = n := by
  unfold additivePhase
  dsimp only
  rw [Complex.exp_eq_one_iff]
  apply exists_congr
  intro n
  rw [mul_comm (n : ℂ)]
  constructor
  · exact mul_left_cancel₀ Complex.two_pi_I_ne_zero
  · intro h
    rw [h]

lemma residueAddChar_ne_one {p : Eisenstein} (hp : primaryPrime p) :
    residueAddChar p hp.2.ne_zero ≠ 1 := by
  intro htriv
  have hall (v : Eisenstein) : additivePhase p v = 1 := by
    rw [← residueAddChar_mk p hp.2.ne_zero, htriv, AddChar.one_apply]
  obtain ⟨n,hn⟩ := additivePhase_eq_one_iff.mp (hall 1)
  obtain ⟨k,hk⟩ := additivePhase_eq_one_iff.mp (hall omegaE)
  simp only [Subalgebra.coe_one, omegaE] at hn hk
  have ht := trace_pair_lattice hn (show omega * ((1 : ℂ)/(p : ℂ)) +
      star (omega * ((1 : ℂ)/(p : ℂ))) = k by simpa [div_eq_mul_inv] using hk)
  apply primaryPrime_not_dvd_three hp
  refine ⟨ofCoords (n-k) (-n-2*k), ?_⟩
  apply Subtype.ext
  change (3 : ℂ) = (p : ℂ) * (ofCoords (n-k) (-n-2*k) : ℂ)
  rw [ofCoords_coe, ← ht]
  have hp' : (p : ℂ) ≠ 0 := fun h => hp.2.ne_zero (Subtype.ext h)
  field_simp

lemma norm_gaussAtPrime {p : Eisenstein} (hp : primaryPrime p) :
    ‖gaussAtPrime p‖ = 1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let g := gaussSum (cubicResidueChar p hp) (residueAddChar p hp.2.ne_zero)
  have hprod := gaussSum_mul_gaussSum_eq_card (cubicResidueChar_ne_one hp)
    (AddChar.IsPrimitive.of_ne_one (residueAddChar_ne_one hp))
  rw [← star_gaussSum_eq] at hprod
  have hnormSq : (Complex.normSq g : ℂ) = (normNat p : ℂ) := by
    rw [← Complex.mul_conj]
    change g * star g = _
    rw [← residues_card hp.2.ne_zero, Nat.card_eq_fintype_card]
    exact hprod
  have hnormSq' : Complex.normSq g = norm p := by
    have hreal := congrArg Complex.re hnormSq
    simpa [normNat_cast] using hreal
  have hnorm : ‖g‖ = Real.sqrt (norm p) := by
    rw [Complex.norm_def, hnormSq']
  have hp' : (p : ℂ) ≠ 0 := fun h => hp.2.ne_zero (Subtype.ext h)
  have hpos : 0 < norm p := Complex.normSq_pos.mpr hp'
  rw [gaussAtPrime_eq_gaussSum hp, norm_mul, norm_inv]
  change ‖(Real.sqrt (norm p) : ℂ)‖⁻¹ * ‖g‖ = 1
  rw [hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hpos).ne'

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Conjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein conjugation, characters and Gauss-sum symmetry. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
lemma star_omega_linear : star omega = -omega - 1 := by
  apply Complex.ext <;> simp [omega_re, omega_im]; ring

lemma star_omega : star omega = omega^2 := by
  rw [star_omega_linear]
  linear_combination -omega_quadratic

lemma star_mem_eisenstein (z : Eisenstein) : star (z : ℂ) ∈ eisensteinRing := by
  obtain ⟨a,b,h⟩ := exists_coordinates z
  have hstar : star (z : ℂ) = (ofCoords (a-b) (-b) : ℂ) := by
    rw [h]
    simp only [star_add, star_mul, star_intCast, star_omega_linear, ofCoords_coe]
    push_cast
    ring
  rw [hstar]
  exact (ofCoords (a-b) (-b)).property

def conjugate : Eisenstein ≃+* Eisenstein where
  toFun z := ⟨star (z : ℂ), star_mem_eisenstein z⟩
  invFun z := ⟨star (z : ℂ), star_mem_eisenstein z⟩
  left_inv z := Subtype.ext (star_star _)
  right_inv z := Subtype.ext (star_star _)
  map_mul' z w := Subtype.ext (by simp)
  map_add' z w := Subtype.ext (by simp)

@[simp] lemma conjugate_coe (z : Eisenstein) : (conjugate z : ℂ) = star (z : ℂ) := rfl

@[simp] lemma conjugate_conjugate (z : Eisenstein) : conjugate (conjugate z) = z :=
  Subtype.ext (star_star _)

@[simp] lemma conjugate_omegaE : conjugate omegaE = omegaE^2 := Subtype.ext star_omega

@[simp] lemma norm_conjugate (z : Eisenstein) : norm (conjugate z) = norm z :=
  Complex.normSq_conj _

@[simp] lemma normNat_conjugate (z : Eisenstein) : normNat (conjugate z) = normNat z := by
  simp only [normNat, norm_conjugate]

lemma primary_conjugate {z : Eisenstein} (hz : primary z) : primary (conjugate z) := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨conjugate w, ?_⟩
  simpa only [map_sub, map_one, map_mul, map_ofNat] using congrArg conjugate hw

lemma primaryPrime_conjugate {p : Eisenstein} (hp : primaryPrime p) :
    primaryPrime (conjugate p) :=
  ⟨primary_conjugate hp.1, (MulEquiv.prime_iff conjugate).mpr hp.2⟩

def residueConjugate (p : Eisenstein) : Residues p ≃+* Residues (conjugate p) :=
  Ideal.quotientEquiv (modulus p) (modulus (conjugate p)) conjugate (by
    simp [modulus, Ideal.map_span])

@[simp] lemma residueConjugate_mk (p v : Eisenstein) :
    residueConjugate p (Ideal.Quotient.mk (modulus p) v) =
      Ideal.Quotient.mk (modulus (conjugate p)) (conjugate v) := rfl

lemma isUnit_residue_conjugate {p v : Eisenstein} :
    IsUnit (Ideal.Quotient.mk (modulus (conjugate p)) (conjugate v)) ↔
      IsUnit (Ideal.Quotient.mk (modulus p) v) := by
  constructor
  · intro h
    change IsUnit (residueConjugate p (Ideal.Quotient.mk (modulus p) v)) at h
    have hh := h.map (residueConjugate p).symm
    rw [(residueConjugate p).symm_apply_apply] at hh
    exact hh
  · intro h
    exact h.map (residueConjugate p)

lemma cubicSymbolAtPrime_conjugate {p : Eisenstein} (hp : primaryPrime p) (v : Eisenstein) :
    cubicSymbolAtPrime (conjugate p) (conjugate v) = star (cubicSymbolAtPrime p v) := by
  by_cases hv : IsUnit (Ideal.Quotient.mk (modulus p) v)
  · have hv' := isUnit_residue_conjugate.mpr hv
    obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv
    let k : Fin 3 := ⟨(2*(j:ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩
    have hk : Ideal.Quotient.mk (modulus (conjugate p))
          ((conjugate v)^((normNat (conjugate p)-1)/3)) =
        Ideal.Quotient.mk (modulus (conjugate p)) (omegaE^(k:ℕ)) := by
      have heq := congrArg (residueConjugate p) hj
      simpa only [residueConjugate_mk, map_pow, conjugate_omegaE,
        normNat_conjugate, k, cube_pow_mod omegaE_cube, pow_mul] using heq
    rw [cubicSymbol_euler_value (primaryPrime_conjugate hp) hv' k hk,
      cubicSymbol_euler_value hp hv j hj, star_pow, star_omega]
    exact (cube_pow_mod omega_cube (2*(j:ℕ))).trans (pow_mul omega 2 (j:ℕ))
  · have hv' : ¬IsUnit (Ideal.Quotient.mk (modulus (conjugate p)) (conjugate v)) :=
      mt isUnit_residue_conjugate.mp hv
    simp only [cubicSymbolAtPrime, ite_eq_right hv, ite_eq_right hv', star_zero]

lemma cubicSymbolAtPrime_unit_cube {p v : Eisenstein} (hp : primaryPrime p)
    (hv : IsUnit (Ideal.Quotient.mk (modulus p) v)) :
    cubicSymbolAtPrime p v ^ 3 = 1 := by
  obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv
  rw [cubicSymbol_euler_value hp hv j hj, ← pow_mul, Nat.mul_comm, pow_mul,
    omega_cube, one_pow]

lemma cubicSymbolAtPrime_neg_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicSymbolAtPrime p (-1) = 1 := by
  have h2 : cubicSymbolAtPrime p (-1) ^ 2 = 1 := by
    rw [pow_two, ← cubicSymbolAtPrime_mul hp, neg_mul_neg, one_mul,
      cubicSymbolAtPrime_one hp]
  have h3 := cubicSymbolAtPrime_unit_cube hp
    (show IsUnit (Ideal.Quotient.mk (modulus p) (-1)) from by
      simpa only [map_neg, map_one] using (isUnit_one : IsUnit (1 : Residues p)).neg)
  rw [pow_succ, h2, one_mul] at h3
  exact h3

lemma cubicSymbolAtPrime_neg {p : Eisenstein} (hp : primaryPrime p) (v : Eisenstein) :
    cubicSymbolAtPrime p (-v) = cubicSymbolAtPrime p v := by
  rw [← neg_one_mul v, cubicSymbolAtPrime_mul hp, cubicSymbolAtPrime_neg_one hp,
    one_mul]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_EuclideanDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nearest-lattice division and the Eisenstein Euclidean domain. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
@[simp] lemma normNat_mul (x y : Eisenstein) : normNat (x*y) = normNat x * normNat y := by
  apply Nat.cast_injective (R := ℝ)
  simp only [Nat.cast_mul, normNat_cast]
  exact Complex.normSq_mul _ _

@[simp] lemma normNat_one : normNat 1 = 1 := by
  apply Nat.cast_injective (R := ℝ)
  simp only [normNat_cast, Nat.cast_one]
  exact Complex.normSq_one

@[simp] lemma normNat_zero : normNat 0 = 0 := by
  apply Nat.cast_injective (R := ℝ)
  simp only [normNat_cast, Nat.cast_zero]
  exact Complex.normSq_zero

lemma real_coordinates_norm (a b : ℝ) :
    Complex.normSq ((a : ℂ) + (b : ℂ)*omega) = a^2-a*b+b^2 := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, omega_re, omega_im]
  ring_nf
  norm_num [Real.sq_sqrt]
  ring

def nearestEisenstein (z : ℂ) : Eisenstein :=
  ofCoords (round (z.re + z.im / Real.sqrt 3)) (round (2*z.im / Real.sqrt 3))

lemma complex_coordinates (z : ℂ) :
    z = ((z.re + z.im / Real.sqrt 3 : ℝ) : ℂ) +
      ((2*z.im / Real.sqrt 3 : ℝ) : ℂ)*omega := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, omega_re, zero_mul, sub_zero]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, omega_im, zero_mul, add_zero, zero_add]
    field_simp

lemma nearestEisenstein_normSq_lt (z : ℂ) :
    Complex.normSq (z - (nearestEisenstein z : ℂ)) < 1 := by
  let a : ℝ := z.re + z.im / Real.sqrt 3
  let b : ℝ := 2*z.im / Real.sqrt 3
  have hdist : z - (nearestEisenstein z : ℂ) =
      ((a - round a : ℝ) : ℂ) + ((b - round b : ℝ) : ℂ)*omega := by
    conv_lhs => lhs; rw [complex_coordinates z]
    simp only [nearestEisenstein, ofCoords_coe]
    dsimp only [a, b]
    push_cast
    ring
  have ha : (a - round a)^2 ≤ (1/2 : ℝ)^2 :=
    sq_le_sq.mpr (by simpa using (abs_sub_round a))
  have hb : (b - round b)^2 ≤ (1/2 : ℝ)^2 :=
    sq_le_sq.mpr (by simpa using (abs_sub_round b))
  rw [hdist, real_coordinates_norm]
  nlinarith [sq_nonneg (a-round a + (b-round b))]

@[simp] lemma nearestEisenstein_zero : nearestEisenstein 0 = 0 := by
  simp [nearestEisenstein, ofCoords]

def latticeQuotient (x y : Eisenstein) : Eisenstein :=
  nearestEisenstein ((x : ℂ)/(y : ℂ))

def latticeRemainder (x y : Eisenstein) : Eisenstein := x-y*latticeQuotient x y

lemma normNat_latticeRemainder_lt (x : Eisenstein) {y : Eisenstein} (hy : y ≠ 0) :
    normNat (latticeRemainder x y) < normNat y := by
  have hy' : (y : ℂ) ≠ 0 := fun h => hy (Subtype.ext h)
  have hrepr : (latticeRemainder x y : ℂ) = (y : ℂ) *
      ((x : ℂ)/(y : ℂ) - (nearestEisenstein ((x : ℂ)/(y : ℂ)) : ℂ)) := by
    simp only [latticeRemainder, latticeQuotient, Subalgebra.coe_sub, Subalgebra.coe_mul,
      mul_sub, mul_div_cancel₀ _ hy']
  have hnorm : norm (latticeRemainder x y) < norm y := by
    rw [norm, hrepr, Complex.normSq_mul]
    exact mul_lt_of_lt_one_right (Complex.normSq_pos.mpr hy') (nearestEisenstein_normSq_lt _)
  rwa [← normNat_cast, ← normNat_cast, Nat.cast_lt] at hnorm

instance eisensteinEuclideanDomain : EuclideanDomain Eisenstein where
  quotient := latticeQuotient
  quotient_zero x := by simp [latticeQuotient]
  remainder := latticeRemainder
  quotient_mul_add_remainder_eq x y := by simp [latticeRemainder]
  r x y := normNat x < normNat y
  r_wellFounded := (measure normNat).wf
  remainder_lt := normNat_latticeRemainder_lt
  mul_left_not_lt x y hy := by
    change ¬ normNat (x*y) < normNat x
    rw [normNat_mul, not_lt]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (normNat_ne_zero hy))

open UniqueFactorizationMonoid

instance eisensteinNormalization : StrongNormalizationMonoid Eisenstein :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

def normNatHom : Eisenstein →* ℕ where
  toFun := normNat
  map_one' := normNat_one
  map_mul' := normNat_mul

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique primary associates and canonical prime factorization. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
lemma normNat_of_isUnit {u : Eisenstein} (hu : IsUnit u) : normNat u = 1 :=
  Nat.isUnit_iff.mp (hu.map normNatHom)

lemma norm_of_isUnit {u : Eisenstein} (hu : IsUnit u) : norm u = 1 := by
  rw [← normNat_cast, normNat_of_isUnit hu, Nat.cast_one]

lemma primary_iff_residue_one (z : Eisenstein) :
    primary z ↔ Ideal.Quotient.mk (modulus 3) z = 1 := by
  rw [primary, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk (modulus 3) (z-1) = 0 ↔ _
  rw [map_sub, map_one, sub_eq_zero]

lemma primary_mul {a b : Eisenstein} (ha : primary a) (hb : primary b) : primary (a*b) := by
  rw [primary_iff_residue_one, map_mul, (primary_iff_residue_one a).mp ha,
    (primary_iff_residue_one b).mp hb, one_mul]

lemma primary_unit_eq_one {u : Eisenstein} (hu : IsUnit u) (hprimary : primary u) : u = 1 := by
  have hnu : ‖(u : ℂ)‖ = 1 := by
    have hnorm := norm_of_isUnit hu
    rw [norm, Complex.normSq_eq_norm_sq] at hnorm
    nlinarith [_root_.norm_nonneg (u : ℂ)]
  have hsub : ‖(u : ℂ) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖(u : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnu, norm_one]; norm_num
  obtain ⟨w, hw⟩ := hprimary
  have hnorm : norm (u-1) = 9 * norm w := by
    rw [hw, norm, Subalgebra.coe_mul, Complex.normSq_mul]
    change Complex.normSq (3 : ℂ) * norm w = 9 * norm w
    norm_num [Complex.normSq_apply]
  have hwlt : (normNat w : ℝ) < 1 := by
    rw [normNat_cast]
    rw [norm, Subalgebra.coe_sub, Subalgebra.coe_one, Complex.normSq_eq_norm_sq] at hnorm
    nlinarith [_root_.norm_nonneg ((u : ℂ)-1)]
  have hwzero : normNat w = 0 := by
    have hnat : normNat w < 1 := by exact_mod_cast hwlt
    omega
  have hw' : w = 0 := by
    by_contra h
    exact normNat_ne_zero h hwzero
  rw [hw', mul_zero, sub_eq_zero] at hw
  exact hw

lemma primary_associated_eq {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : Associated a b) : a = b := by
  obtain ⟨u, hu⟩ := hab
  have hm := congrArg (Ideal.Quotient.mk (modulus 3)) hu
  rw [map_mul, (primary_iff_residue_one a).mp ha,
    (primary_iff_residue_one b).mp hb, one_mul] at hm
  have huone := primary_unit_eq_one u.isUnit ((primary_iff_residue_one u).mpr hm)
  simpa only [huone, mul_one] using hu

lemma residue_three_eq_zero : Ideal.Quotient.mk (modulus (3 : Eisenstein)) 3 = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

lemma residue_ofCoords_mod_three (a b : ℤ) :
    Ideal.Quotient.mk (modulus (3 : Eisenstein)) (ofCoords a b) =
      Ideal.Quotient.mk (modulus (3 : Eisenstein)) (ofCoords (a%3) (b%3)) := by
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨ofCoords (a/3) (b/3), ?_⟩
  have ha := Int.emod_add_mul_ediv a 3
  have hb := Int.emod_add_mul_ediv b 3
  have ha' : (a : Eisenstein) = (a%3 : ℤ) + 3*(a/3 : ℤ) := by exact_mod_cast ha.symm
  have hb' : (b : Eisenstein) = (b%3 : ℤ) + 3*(b/3 : ℤ) := by exact_mod_cast hb.symm
  dsimp only [ofCoords]
  rw [ha', hb']
  ring

lemma residue_three_nontrivial : Nontrivial (Residues (3 : Eisenstein)) := by
  let : Finite (Residues (3 : Eisenstein)) := finite_residues (by norm_num)
  apply Finite.one_lt_card_iff_nontrivial.mp
  rw [residues_card (by norm_num : (3 : Eisenstein) ≠ 0)]
  change 1 < ⌊Complex.normSq (3 : ℂ)⌋₊
  norm_num [Complex.normSq_apply]

lemma omegaE_isUnit : IsUnit omegaE := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨omegaE^2, by simpa only [← pow_succ'] using omegaE_cube⟩

lemma unit_lift_mod_three {z : Eisenstein}
    (hz : IsUnit (Ideal.Quotient.mk (modulus 3) z)) :
    ∃ u : Eisenstein, IsUnit u ∧ primary (z*u) := by
  let := residue_three_nontrivial
  obtain ⟨⟨a,b⟩, rfl⟩ := ofCoords_surjective z
  have ha : 0 ≤ a%3 ∧ a%3 < 3 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have hb : 0 ≤ b%3 ∧ b%3 < 3 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  let q := Ideal.Quotient.mk (modulus (3 : Eisenstein))
  have hreduce : q (ofCoords a b) = q (ofCoords (a%3) (b%3)) := residue_ofCoords_mod_three a b
  have hω : (q omegaE)^2 + q omegaE + 1 = 0 := by
    have he : omegaE^2 + omegaE + 1 = 0 := Subtype.ext omega_quadratic
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg q he
  have h3 : (3 : Residues (3 : Eisenstein)) = 0 := by
    simpa only [map_ofNat] using residue_three_eq_zero
  have hunit : IsUnit (q (ofCoords (a%3) (b%3))) := hreduce ▸ hz
  have hbad {v : Residues (3 : Eisenstein)} (hv : IsUnit v) (hsq : v^2 = 0) : False :=
    (hv.pow 2).ne_zero hsq
  have hprimary (u : Eisenstein) (heq : q (ofCoords (a%3) (b%3)) * q u = 1) :
      primary (ofCoords a b * u) := by
    rw [primary_iff_residue_one, map_mul]
    exact (congrArg (· * q u) hreduce).trans heq
  obtain ⟨ha0,ha3⟩ := ha
  obtain ⟨hb0,hb3⟩ := hb
  interval_cases hA : a%3 <;> interval_cases hB : b%3
  · simp [ofCoords] at hunit
  · refine ⟨omegaE^2, omegaE_isUnit.pow 2, hprimary _ ?_⟩
    simpa only [hA, hB, ofCoords, Int.cast_zero, Int.cast_one, zero_add, one_mul,
      map_pow, map_one, ← pow_succ'] using congrArg q omegaE_cube
  · refine ⟨-omegaE^2, (omegaE_isUnit.pow 2).neg, hprimary _ ?_⟩
    simp only [ofCoords, Int.cast_zero, Int.cast_ofNat, zero_add,
      map_mul, map_ofNat, map_neg, map_pow]
    have hc : (q omegaE)^3 = 1 := by simpa only [map_pow, map_one] using congrArg q omegaE_cube
    linear_combination -2*hc - h3
  · refine ⟨1, isUnit_one, hprimary _ ?_⟩
    simp [ofCoords]
  · refine ⟨-omegaE, omegaE_isUnit.neg, hprimary _ ?_⟩
    simp only [ofCoords, Int.cast_one, one_mul, map_add, map_one, map_neg]
    linear_combination -hω
  · apply (hbad hunit ?_).elim
    simp only [ofCoords, Int.cast_one, Int.cast_ofNat, map_add, map_mul, map_one, map_ofNat]
    linear_combination 4*hω - h3
  · refine ⟨-1, isUnit_one.neg, hprimary _ ?_⟩
    simp only [ofCoords, Int.cast_zero, Int.cast_ofNat, zero_mul, add_zero,
      map_ofNat, map_neg, map_one]
    linear_combination -h3
  · apply (hbad hunit ?_).elim
    simp only [ofCoords, Int.cast_one, Int.cast_ofNat, one_mul, map_add, map_ofNat]
    linear_combination hω + h3 * (q omegaE+1)
  · refine ⟨omegaE, omegaE_isUnit, hprimary _ ?_⟩
    simp only [ofCoords, Int.cast_ofNat, map_add, map_mul, map_ofNat]
    linear_combination 2*hω - h3

lemma unit_residue_of_dvd_primary {n d : Eisenstein} (hn : primary n) (hd : d ∣ n) :
    IsUnit (Ideal.Quotient.mk (modulus 3) d) := by
  apply isUnit_of_dvd_one
  rw [← (primary_iff_residue_one n).mp hn]
  exact map_dvd (Ideal.Quotient.mk (modulus 3)) hd

def primaryNormalize (z : Eisenstein) : Eisenstein :=
  if h : IsUnit (Ideal.Quotient.mk (modulus 3) z) then
    z * Classical.choose (unit_lift_mod_three h)
  else z

lemma primaryNormalize_associated (z : Eisenstein) : Associated z (primaryNormalize z) := by
  unfold primaryNormalize
  split_ifs with h
  · exact associated_mul_unit_right _ _ (Classical.choose_spec (unit_lift_mod_three h)).1
  · rfl

lemma primaryNormalize_primary {z : Eisenstein}
    (hz : IsUnit (Ideal.Quotient.mk (modulus 3) z)) : primary (primaryNormalize z) := by
  rw [primaryNormalize, dite_eq_left hz]
  exact (Classical.choose_spec (unit_lift_mod_three hz)).2

lemma prime_primaryNormalize {z : Eisenstein} (hz : Prime z) : Prime (primaryNormalize z) :=
  (primaryNormalize_associated z).prime_iff.mp hz

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Jacobi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubic Jacobi sums and the prime Gauss cube identity. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
lemma cubicResidueChar_cube {p : Eisenstein} (hp : primaryPrime p) :
    cubicResidueChar p hp ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply u.isUnit]
  apply cubicSymbolAtPrime_unit_cube hp
  rw [residueRepresentative_spec]
  exact u.isUnit

lemma cubicResidueChar_order {p : Eisenstein} (hp : primaryPrime p) :
    orderOf (cubicResidueChar p hp) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (cubicResidueChar_cube hp) (cubicResidueChar_ne_one hp)

lemma cubicResidueChar_mem (p : Eisenstein) (hp : primaryPrime p) (x : Residues p) :
    cubicResidueChar p hp x ∈ eisensteinRing := by
  change cubicSymbolAtPrime p (residueRepresentative p x) ∈ eisensteinRing
  unfold cubicSymbolAtPrime
  split_ifs <;> first
  | exact eisensteinRing.zero_mem
  | exact eisensteinRing.pow_mem (Algebra.subset_adjoin (Set.mem_singleton omega)) _

def cubicResidueCharE (p : Eisenstein) (hp : primaryPrime p) :
    MulChar (Residues p) Eisenstein where
  toFun x := ⟨cubicResidueChar p hp x, cubicResidueChar_mem p hp x⟩
  map_one' := Subtype.ext (map_one (cubicResidueChar p hp))
  map_mul' x y := Subtype.ext (map_mul (cubicResidueChar p hp) x y)
  map_nonunit' _ hx := Subtype.ext ((cubicResidueChar p hp).map_nonunit hx)

@[simp] lemma cubicResidueCharE_coe (p : Eisenstein) (hp : primaryPrime p) (x : Residues p) :
    (cubicResidueCharE p hp x : ℂ) = cubicResidueChar p hp x := rfl

lemma cubicResidueCharE_euler {p : Eisenstein} (hp : primaryPrime p) (x : Residues p) :
    Ideal.Quotient.mk (modulus p) (cubicResidueCharE p hp x) =
      x ^ ((normNat p - 1) / 3) := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  by_cases hx : IsUnit x
  · have hv : IsUnit (Ideal.Quotient.mk (modulus p) (residueRepresentative p x)) := by
      rwa [residueRepresentative_spec]
    obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv
    have he : cubicResidueCharE p hp x = omegaE ^ (j : ℕ) := by
      apply Subtype.ext
      exact cubicSymbol_euler_value hp hv j hj
    rw [he]
    simpa only [map_pow, residueRepresentative_spec] using hj.symm
  · have hx0 : x = 0 := by simpa only [isUnit_iff_ne_zero, not_ne_iff] using hx
    have hq : 1 < normNat p := by
      rw [← residues_card hp.2.ne_zero, Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hk : (normNat p - 1) / 3 ≠ 0 := by
      have := Nat.div_pos
        (Nat.le_of_dvd (by omega) (primaryPrime_norm_sub_one_dvd_three hp))
        (by norm_num : 0 < 3)
      omega
    rw [(cubicResidueCharE p hp).map_nonunit hx, map_zero, hx0, zero_pow hk]

def primeJacobi (p : Eisenstein) (hp : primaryPrime p) : Eisenstein :=
  letI : Finite (Residues p) := finite_residues hp.2.ne_zero
  letI : Fintype (Residues p) := Fintype.ofFinite _
  jacobiSum (cubicResidueCharE p hp) (cubicResidueCharE p hp)

lemma primeJacobi_coe {p : Eisenstein} (hp : primaryPrime p) [Fintype (Residues p)] :
    (primeJacobi p hp : ℂ) = jacobiSum (cubicResidueChar p hp) (cubicResidueChar p hp) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  have hi : Fintype.ofFinite (Residues p) = ‹Fintype (Residues p)› := Subsingleton.elim _ _
  unfold primeJacobi
  rw [hi]
  unfold jacobiSum
  change (eisensteinRing.subtype : Eisenstein →+* ℂ) (∑ x, _) = _
  rw [map_sum]
  rfl

lemma primeJacobi_primary {p : Eisenstein} (hp : primaryPrime p) :
    primary (-primeJacobi p hp) := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have hn : 3 ∣ Fintype.card (Residues p) - 1 := by
    rw [← Nat.card_eq_fintype_card, residues_card hp.2.ne_zero]
    exact primaryPrime_norm_sub_one_dvd_three hp
  obtain ⟨z,hz,hJ⟩ := exists_jacobiSum_eq_neg_one_add (by norm_num : 2 < 3)
    (cubicResidueChar_cube hp) (cubicResidueChar_cube hp) hn omega_primitive
  change (3 : Eisenstein) ∣ -primeJacobi p hp - 1
  refine ⟨⟨z,hz⟩ * omegaE, ?_⟩
  apply Subtype.ext
  change -(primeJacobi p hp : ℂ) - 1 = 3 * (z * omega)
  rw [primeJacobi_coe hp, hJ]
  linear_combination -z * omega_quadratic

lemma primeJacobi_dvd {p : Eisenstein} (hp : primaryPrime p) :
    p ∣ primeJacobi p hp := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk (modulus p) (primeJacobi p hp) = 0
  unfold primeJacobi jacobiSum
  simp only [map_sum, map_mul, cubicResidueCharE_euler hp]
  let k := (normNat p - 1) / 3
  have hcard : Fintype.card (Residues p) = normNat p := by
    rw [← Nat.card_eq_fintype_card, residues_card hp.2.ne_zero]
  have hq : 1 < normNat p := hcard ▸ Fintype.one_lt_card
  have hk : 3*k = normNat p - 1 := Nat.mul_div_cancel' (primaryPrime_norm_sub_one_dvd_three hp)
  have hkpos : 0 < k := by omega
  have hexp (x : Residues p) : x^k * (1-x)^k =
      ∑ i ∈ Finset.range (k+1), ((-1 : Residues p)^(i+k) * (k.choose i)) * x^(k+(k-i)) := by
    rw [sub_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [one_pow, mul_one, pow_add]
    ring
  change (∑ x : Residues p, x^k * (1-x)^k) = 0
  simp_rw [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one, mul_zero]
  rw [hcard]
  omega

lemma gaussAtPrime_cube_jacobi {p : Eisenstein} (hp : primaryPrime p) :
    gaussAtPrime p ^ 3 = (Real.sqrt (norm p) : ℂ)⁻¹ * (primeJacobi p hp : ℂ) := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have hχ := cubicResidueChar_order hp
  have hg := gaussSum_pow_eq_prod_jacobiSum (by rw [hχ]; norm_num :
      2 ≤ orderOf (cubicResidueChar p hp))
    (AddChar.IsPrimitive.of_ne_one (residueAddChar_ne_one hp))
  rw [hχ] at hg
  have hminus : cubicResidueChar p hp (-1) = 1 := by
    have hm : Ideal.Quotient.mk (modulus p) (-1) = (-1 : Residues p) := by
      rw [map_neg, map_one]
    rw [← hm, cubicResidueChar_mk, cubicSymbolAtPrime_neg_one hp]
  norm_num [hminus, Finset.prod_Ico_succ_top, ← primeJacobi_coe hp] at hg
  have hs : 0 < Real.sqrt (norm p) := Real.sqrt_pos.mpr
    (lt_of_le_of_ne (norm_nonneg p) (Ne.symm ((norm_eq_zero_iff).not.mpr hp.2.ne_zero)))
  have hs2 : (Real.sqrt (norm p) : ℂ)^2 = (norm p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (norm_nonneg p)
  have hn : (Fintype.card (Residues p) : ℂ) = (norm p : ℂ) := by
    rw [← Nat.card_eq_fintype_card, residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  rw [gaussAtPrime_eq_gaussSum hp, mul_pow, hg, hn, ← hs2]
  have hs0 : (Real.sqrt (norm p) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp

lemma norm_primeJacobi {p : Eisenstein} (hp : primaryPrime p) :
    norm (primeJacobi p hp) = norm p := by
  have h := congrArg (fun z : ℂ => ‖z‖) (gaussAtPrime_cube_jacobi hp)
  rw [norm_pow, norm_gaussAtPrime hp, one_pow, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hs : 0 < Real.sqrt (norm p) := Real.sqrt_pos.mpr
    (lt_of_le_of_ne (norm_nonneg p) (Ne.symm ((norm_eq_zero_iff).not.mpr hp.2.ne_zero)))
  have hJ : ‖(primeJacobi p hp : ℂ)‖ = Real.sqrt (norm p) := by
    rw [← div_eq_inv_mul, eq_div_iff hs.ne'] at h
    simpa using h.symm
  change Complex.normSq _ = _
  rw [← Complex.sq_norm, hJ, Real.sq_sqrt (norm_nonneg p)]

lemma isUnit_of_norm_eq_one {z : Eisenstein} (hz : norm z = 1) : IsUnit z := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨conjugate z, ?_⟩
  apply Subtype.ext
  change (z : ℂ) * (starRingEnd ℂ) (z : ℂ) = 1
  rw [Complex.mul_conj]
  exact_mod_cast hz

lemma primeJacobi_eq_neg {p : Eisenstein} (hp : primaryPrime p) :
    primeJacobi p hp = -p := by
  obtain ⟨u, hu⟩ := primeJacobi_dvd hp
  have hn := norm_primeJacobi hp
  have hmul : norm (p*u) = norm p * norm u := map_mul Complex.normSq _ _
  rw [hu, hmul] at hn
  have hp0 : norm p ≠ 0 := (norm_eq_zero_iff).not.mpr hp.2.ne_zero
  have hnu : norm u = 1 := (mul_left_cancel₀ hp0 (by simpa using hn))
  have hunit := isUnit_of_norm_eq_one hnu
  have hassoc : Associated (-primeJacobi p hp) p := by
    rw [hu]
    rw [show -(p*u) = p * (-u) by ring]
    exact (associated_mul_unit_right p (-u) hunit.neg).symm
  have he := primary_associated_eq (primeJacobi_primary hp) hp.1 hassoc
  exact neg_eq_iff_eq_neg.mp he

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein lattice counts and arbitrarily small divisor losses. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma norm_mul_eq (a b : Eisenstein) : norm (a*b) = norm a * norm b :=
  Complex.normSq_mul _ _
@[simp] lemma norm_one_eq : norm (1 : Eisenstein) = 1 := Complex.normSq_one

def nonzeroNormBall (X : ℝ) : Finset Eisenstein :=
  (finite_norm_le X).toFinset.filter (· ≠ 0)
@[simp] lemma mem_nonzeroNormBall {z : Eisenstein} {X : ℝ} :
    z ∈ nonzeroNormBall X ↔ norm z ≤ X ∧ z ≠ 0 := by
  simp [nonzeroNormBall]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_ReciprocityKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-field Frobenius relations and distinct-character reciprocity. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable

noncomputable section
open scoped BigOperators
open AddChar MulChar
namespace CubicFirstMoment.ReciprocityKernel

lemma gaussSum_card_frobenius {F F' K : Type*}
    [Field F] [Fintype F] [Field F'] [Fintype F'] [Field K] [Algebra F' K]
    (χ : MulChar F F') (ψ : AddChar F K) :
    gaussSum (χ.ringHomComp (algebraMap F' K)) ψ ^ Fintype.card F' =
      gaussSum (χ.ringHomComp (algebraMap F' K)) (ψ.mulShift (Fintype.card F' : F)) := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F' (ringChar F')
  have he := Algebra.ringChar_eq F' K
  have : CharP K (ringChar F') := he.symm ▸ (inferInstance : CharP K (ringChar K))
  have : Fact (Nat.Prime (ringChar F')) := ⟨hp⟩
  have hsum : gaussSum (χ.ringHomComp (algebraMap F' K)) ψ ^ Fintype.card F' =
      ∑ x : F, ((algebraMap F' K) (χ x) * ψ x) ^ Fintype.card F' := by
    rw [hc, gaussSum, sum_pow_char_pow]
    rfl
  rw [hsum, gaussSum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_pow, ← map_pow, FiniteField.pow_card]
  congr 1
  rw [← AddChar.pow_apply, AddChar.pow_mulShift]

theorem cubic_jacobi_card_relation {F F' : Type*} [Field F] [Fintype F]
    [Field F'] [Fintype F'] (χ : MulChar F F')
    (hχ : χ ^ 3 = 1) (hχne : χ ≠ 1) (hminus : χ (-1) = 1)
    (hthree : 3 ∣ Fintype.card F' - 1)
    (hchar : ringChar F' ≠ ringChar F) :
    ((Fintype.card F : F') * jacobiSum χ χ) ^ ((Fintype.card F' - 1) / 3) *
      χ (Fintype.card F') = 1 := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  obtain ⟨n', hp', hc'⟩ := FiniteField.card F' (ringChar F')
  have : Fact (Nat.Prime (ringChar F)) := ⟨hp⟩
  have : Fact (Nat.Prime (ringChar F')) := ⟨hp'⟩
  have hunit : IsUnit (Fintype.card F' : F) := by
    rw [hc', Nat.cast_pow]
    apply IsUnit.pow
    apply (isUnit_iff_not_dvd_char F (ringChar F')).mpr
    exact (Nat.prime_dvd_prime_iff_eq hp' hp).not.mpr hchar
  have hN : (Fintype.card F : F') ≠ 0 := by
    rw [hc, Nat.cast_pow]
    apply pow_ne_zero
    apply IsUnit.ne_zero
    apply (isUnit_iff_not_dvd_char F' (ringChar F)).mpr
    exact (Nat.prime_dvd_prime_iff_eq hp hp').not.mpr hchar.symm
  let ψ := FiniteField.primitiveChar F F' hchar
  let K := CyclotomicField ψ.n F'
  let χ' := χ.ringHomComp (algebraMap F' K)
  have hχ' : χ' ^ 3 = 1 := by
    dsimp [χ']
    rw [ringHomComp_pow, hχ, ringHomComp_one]
  have hχ'ne : χ' ≠ 1 := (ringHomComp_ne_one_iff (RingHom.injective _)).mpr hχne
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf χ' = 3 := orderOf_eq_prime hχ' hχ'ne
  have hM : χ' (-1) = 1 := by
    change (algebraMap F' K) (χ (-1)) = 1
    rw [hminus, map_one]
  have hg := gaussSum_pow_eq_prod_jacobiSum (χ := χ') (ψ := ψ.char)
    (by rw [hord]; norm_num) ψ.prim
  rw [hord] at hg
  norm_num [hM, Finset.prod_Ico_succ_top] at hg
  have hNK : (Fintype.card F : K) ≠ 0 := by
    rw [← map_natCast (algebraMap F' K)]
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hN
  have hg0 := gaussSum_ne_zero_of_nontrivial hNK hχ'ne ψ.prim
  have hf := gaussSum_card_frobenius χ ψ.char
  change gaussSum χ' ψ.char ^ Fintype.card F' =
    gaussSum χ' (ψ.char.mulShift (Fintype.card F' : F)) at hf
  have hm := gaussSum_mulShift χ' ψ.char hunit.unit
  rw [hunit.unit_spec, ← hf] at hm
  have hsplit : Fintype.card F' = 3*((Fintype.card F' - 1)/3)+1 := by
    rw [Nat.mul_div_cancel' hthree, Nat.sub_add_cancel Fintype.card_pos]
  rw [hsplit, pow_add, pow_mul, pow_one, hg] at hm
  rw [← hsplit] at hm
  apply (algebraMap F' K).injective
  rw [map_one, map_mul, map_pow, map_mul, map_natCast, ← jacobiSum_ringHomComp]
  change ((Fintype.card F : K) * jacobiSum χ' χ') ^ ((Fintype.card F' - 1) / 3) *
    χ' (Fintype.card F') = 1
  apply mul_right_cancel₀ hg0
  calc
    _ = χ' (Fintype.card F') * (((Fintype.card F : K) * jacobiSum χ' χ') ^
        ((Fintype.card F' - 1) / 3) * gaussSum χ' ψ.char) := by ring
    _ = gaussSum χ' ψ.char := hm
    _ = 1 * gaussSum χ' ψ.char := (one_mul _).symm

end CubicFirstMoment.ReciprocityKernel

namespace CubicFirstMoment

lemma omegaE_primitive : IsPrimitiveRoot omegaE 3 :=
  IsPrimitiveRoot.of_map_of_injective (f := eisensteinRing.subtype) omega_primitive
    Subtype.val_injective

lemma cubeRoot_reduce_inj {r z w : Eisenstein} (hr : primaryPrime r)
    (hz : z^3 = 1) (hw : w^3 = 1)
    (he : Ideal.Quotient.mk (modulus r) z = Ideal.Quotient.mk (modulus r) w) : z = w := by
  obtain ⟨i,hi,hiz⟩ := omegaE_primitive.eq_pow_of_pow_eq_one hz
  obtain ⟨j,hj,hjw⟩ := omegaE_primitive.eq_pow_of_pow_eq_one hw
  rw [← hiz, ← hjw, map_pow, map_pow] at he
  have hij := (residue_omega_primitive hr).pow_inj hi hj he
  rw [← hiz, ← hjw, hij]

lemma cubicResidueCharE_cube {p : Eisenstein} (hp : primaryPrime p) :
    cubicResidueCharE p hp ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply u.isUnit]
  apply Subtype.ext
  change (cubicResidueChar p hp u)^3 = 1
  rw [← MulChar.pow_apply' _ (by norm_num), cubicResidueChar_cube hp,
    MulChar.one_apply u.isUnit]

lemma cubicResidueCharE_neg_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicResidueCharE p hp (-1) = 1 := by
  apply Subtype.ext
  change cubicResidueChar p hp (-1) = 1
  have hm : Ideal.Quotient.mk (modulus p) (-1) = (-1 : Residues p) := by
    rw [map_neg, map_one]
  rw [← hm, cubicResidueChar_mk, cubicSymbolAtPrime_neg_one hp]

lemma cubicResidueCharE_value_cube {p : Eisenstein} (hp : primaryPrime p)
    {x : Residues p} (hx : cubicResidueCharE p hp x ≠ 0) :
    (cubicResidueCharE p hp x)^3 = 1 := by
  have hu : IsUnit x := by
    by_contra hn
    exact hx ((cubicResidueCharE p hp).map_nonunit hn)
  rw [← MulChar.pow_apply' _ (by norm_num), cubicResidueCharE_cube hp,
    MulChar.one_apply hu]

lemma cubicResidueCharE_ringHomComp_ne_one {p r : Eisenstein}
    (hp : primaryPrime p) (hr : primaryPrime r) :
    (cubicResidueCharE p hp).ringHomComp (Ideal.Quotient.mk (modulus r)) ≠ 1 := by
  intro he
  apply cubicResidueChar_ne_one hp
  apply MulChar.ext
  intro u
  have hx : (cubicResidueCharE p hp u)^3 = 1 := by
    rw [← MulChar.pow_apply' _ (by norm_num), cubicResidueCharE_cube hp,
      MulChar.one_apply u.isUnit]
  have hq := congrArg (fun χ : MulChar (Residues p) (Residues r) => χ u) he
  rw [MulChar.ringHomComp_apply, MulChar.one_apply u.isUnit] at hq
  have hval := cubeRoot_reduce_inj hr hx (one_pow 3) (hq.trans (map_one _).symm)
  rw [MulChar.one_apply u.isUnit]
  exact congrArg (fun z : Eisenstein => (z : ℂ)) hval

lemma primeJacobi_eq_sumE {p : Eisenstein} (hp : primaryPrime p) [Fintype (Residues p)] :
    primeJacobi p hp = jacobiSum (cubicResidueCharE p hp) (cubicResidueCharE p hp) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  have hi : Fintype.ofFinite (Residues p) = ‹Fintype (Residues p)› := Subsingleton.elim _ _
  unfold primeJacobi
  rw [hi]

lemma normNat_cast_eq_mul_conjugate (p : Eisenstein) :
    (normNat p : Eisenstein) = p * conjugate p := by
  apply Subtype.ext
  change (normNat p : ℂ) = (p : ℂ) * (starRingEnd ℂ) (p : ℂ)
  rw [Complex.mul_conj]
  exact_mod_cast normNat_cast p

end CubicFirstMoment
end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composite residue characters, Chinese remainders and squarefree Gauss norms. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
def cubicSymbol (b v : Eisenstein) : ℂ :=
  ((normalizedFactors b).map (fun p => cubicSymbolAtPrime (primaryNormalize p) v)).prod

lemma primary_ne_zero {b : Eisenstein} (hb : primary b) : b ≠ 0 := by
  let := residue_three_nontrivial
  intro heq
  have h := unit_residue_of_dvd_primary hb (dvd_refl b)
  rw [heq, map_zero] at h
  exact not_isUnit_zero h

lemma primaryNormalize_normalize {p : Eisenstein} (hp : primary p) :
    primaryNormalize (normalize p) = p := by
  apply primary_associated_eq _ hp
    ((primaryNormalize_associated _).symm.trans (normalize_associated p))
  apply primaryNormalize_primary
  exact unit_residue_of_dvd_primary hp (normalize_associated p).dvd

lemma cubicSymbol_prime {p : Eisenstein} (hp : primaryPrime p) (v : Eisenstein) :
    cubicSymbol p v = cubicSymbolAtPrime p v := by
  simp only [cubicSymbol, normalizedFactors_irreducible hp.2.irreducible,
    Multiset.map_singleton, Multiset.prod_singleton, primaryNormalize_normalize hp.1]

lemma cubicSymbol_congr_prime_divisors {b v w : Eisenstein}
    (h : ∀ p ∈ normalizedFactors b, p ∣ v-w) : cubicSymbol b v = cubicSymbol b w := by
  unfold cubicSymbol
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro p hp
  apply cubicSymbolAtPrime_congr
  apply Ideal.Quotient.eq.mpr
  exact Ideal.mem_span_singleton.mpr
    ((primaryNormalize_associated p).dvd_iff_dvd_left.mp (h p hp))

lemma cubicSymbol_congr {b v w : Eisenstein}
    (h : Ideal.Quotient.mk (modulus b) v = Ideal.Quotient.mk (modulus b) w) :
    cubicSymbol b v = cubicSymbol b w := by
  apply cubicSymbol_congr_prime_divisors
  intro p hp
  exact dvd_trans (dvd_of_mem_normalizedFactors hp)
    (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h))

lemma cubicSymbol_mul_lower {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Eisenstein) : cubicSymbol (a*b) v = cubicSymbol a v * cubicSymbol b v := by
  simp only [cubicSymbol, normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]

lemma cubicSymbol_mul_upper {b : Eisenstein} (hb : primary b) (v w : Eisenstein) :
    cubicSymbol b (v*w) = cubicSymbol b v * cubicSymbol b w := by
  unfold cubicSymbol
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro p hp
  exact cubicSymbolAtPrime_mul ⟨primaryNormalize_primary
    (unit_residue_of_dvd_primary hb (dvd_of_mem_normalizedFactors hp)),
    prime_primaryNormalize (prime_of_normalized_factor p hp)⟩ v w

lemma residue_eq_of_dvd_sub {b v w : Eisenstein} (h : b ∣ v-w) :
    Ideal.Quotient.mk (modulus b) v = Ideal.Quotient.mk (modulus b) w :=
  Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

lemma residue_isUnit_of_isCoprime {b v : Eisenstein} (h : IsCoprime b v) :
    IsUnit (Ideal.Quotient.mk (modulus b) v) := by
  have hh := h.map (Ideal.Quotient.mk (modulus b))
  have hb : Ideal.Quotient.mk (modulus b) b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl b))
  rwa [hb, isCoprime_zero_left] at hh

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Reciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full cubic reciprocity and twisted multiplicativity of Gauss sums. -/

section

noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_of_mul {a b : Eisenstein} (ha : primary a) (hab : primary (a*b)) :
    primary b := by
  rw [primary_iff_residue_one] at ha hab ⊢
  rwa [map_mul, ha, one_mul] at hab

lemma primary_induction {P : Eisenstein → Prop} (h1 : P 1)
    (hmul : ∀ p b, primaryPrime p → primary b → P b → P (p*b))
    {b : Eisenstein} (hb : primary b) : P b := by
  have hall : ∀ n : ℕ, ∀ b : Eisenstein, normNat b = n → primary b → P b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hnorm hb
      by_cases hu : IsUnit b
      · simpa only [primary_unit_eq_one hu hb] using h1
      obtain ⟨q,hq,hqb⟩ := WfDvdMonoid.exists_irreducible_factor hu (primary_ne_zero hb)
      let p := primaryNormalize q
      have hp : primaryPrime p := ⟨primaryNormalize_primary
        (unit_residue_of_dvd_primary hb hqb), prime_primaryNormalize hq.prime⟩
      have hpb : p ∣ b := (primaryNormalize_associated q).dvd_iff_dvd_left.mp hqb
      obtain ⟨c,rfl⟩ := hpb
      have hc := primary_of_mul hp.1 hb
      apply hmul p c hp hc
      apply ih (normNat c) _ c rfl hc
      have hpN : 1 < normNat p := by
        have hp0 := normNat_ne_zero hp.2.ne_zero
        have hp1 : normNat p ≠ 1 := by
          intro heq
          apply hp.2.not_isUnit
          apply isUnit_of_norm_eq_one
          rw [← normNat_cast, heq, Nat.cast_one]
        omega
      have hc0 := normNat_ne_zero (primary_ne_zero hc)
      rw [← hnorm, normNat_mul]
      nlinarith [Nat.pos_of_ne_zero hc0]
  exact hall _ _ rfl hb

lemma cubicSymbol_one_lower (v : Eisenstein) : cubicSymbol 1 v = 1 := by
  simp [cubicSymbol]

lemma cubicSymbol_neg {b : Eisenstein} (hb : primary b) (v : Eisenstein) :
    cubicSymbol b (-v) = cubicSymbol b v := by
  revert v
  apply primary_induction (b := b) ?_ ?_ hb
  · intro v
    simp only [cubicSymbol_one_lower]
  · intro p b hp hb ih v
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb),
      cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb),
      cubicSymbol_prime hp, cubicSymbol_prime hp, cubicSymbolAtPrime_neg hp, ih v]

lemma cubicSymbol_conjugate {b : Eisenstein} (hb : primary b) (v : Eisenstein) :
    cubicSymbol (conjugate b) (conjugate v) = star (cubicSymbol b v) := by
  revert v
  apply primary_induction (b := b) ?_ ?_ hb
  · intro v
    simp only [map_one, cubicSymbol_one_lower, star_one]
  · intro p b hp hb ih v
    rw [map_mul, cubicSymbol_mul_lower (primaryPrime_conjugate hp).2.ne_zero
      (primary_ne_zero (primary_conjugate hb)),
      cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb),
      cubicSymbol_prime (primaryPrime_conjugate hp), cubicSymbol_prime hp,
      cubicSymbolAtPrime_conjugate hp, ih v, star_mul']

lemma reciprocity_of_prime_divisor_relation {p b : Eisenstein} (hp : primaryPrime p)
    (hb : primary b)
    (hrel : ∀ q, primaryPrime q → q ∣ b →
      cubicSymbolAtPrime q p = cubicSymbolAtPrime p q) :
    cubicSymbol b p = cubicSymbolAtPrime p b := by
  revert hrel
  apply primary_induction (b := b) ?_ ?_ hb
  · intro hrel
    rw [cubicSymbol_one_lower, cubicSymbolAtPrime_one hp]
  · intro q b hq hb ih hrel
    rw [cubicSymbol_mul_lower hq.2.ne_zero (primary_ne_zero hb),
      cubicSymbol_prime hq, cubicSymbolAtPrime_mul hp,
      hrel q hq (dvd_mul_right q b), ih]
    intro r hr hrb
    exact hrel r hr (dvd_mul_of_dvd_right hrb q)

lemma same_char_primary_primes {p r : Eisenstein} (hp : primaryPrime p)
    (hr : primaryPrime r) (hchar : ringChar (Residues r) = ringChar (Residues p)) :
    r = p ∨ r = conjugate p := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : (modulus r).IsPrime := (Ideal.span_singleton_prime hr.2.ne_zero).mpr hr.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Finite (Residues r) := finite_residues hr.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Fintype (Residues r) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let : Field (Residues r) := Fintype.fieldOfDomain _
  obtain ⟨n, hn, hcard⟩ := FiniteField.card (Residues p) (ringChar (Residues p))
  have hN : normNat p = ringChar (Residues r) ^ (n : ℕ) := by
    rw [← hchar, ← Nat.card_eq_fintype_card, residues_card hp.2.ne_zero] at hcard
    exact hcard
  have hdiv : r ∣ (normNat p : Eisenstein) := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_natCast, hN, Nat.cast_pow, CharP.cast_eq_zero, zero_pow n.ne_zero]
  rw [normNat_cast_eq_mul_conjugate] at hdiv
  rcases hr.2.dvd_or_dvd hdiv with hrp | hrp
  · exact Or.inl (primary_associated_eq hr.1 hp.1 (hr.2.associated_of_dvd hp.2 hrp))
  · exact Or.inr (primary_associated_eq hr.1 (primary_conjugate hp.1)
      (hr.2.associated_of_dvd (primaryPrime_conjugate hp).2 hrp))

lemma cubicSymbolAtPrime_eq_zero_of_dvd {p : Eisenstein} (hp : primaryPrime p)
    {v : Eisenstein} (hv : p ∣ v) : cubicSymbolAtPrime p v = 0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  have heq : Ideal.Quotient.mk (modulus p) v = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hv)
  rw [← cubicResidueChar_mk p hp, heq, MulChar.map_zero]

lemma cubicSymbol_eq_zero_of_not_isCoprime {b : Eisenstein} (hb : primary b)
    {v : Eisenstein} (hv : ¬IsCoprime b v) : cubicSymbol b v = 0 := by
  revert v
  apply primary_induction (b := b) ?_ ?_ hb
  · intro v hv
    exact (hv (isCoprime_one_left)).elim
  · intro p b hp hb ih v hv
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb), cubicSymbol_prime hp]
    by_cases h : IsCoprime p v
    · have h' : ¬IsCoprime b v := fun h' => hv (h.mul_left h')
      rw [ih h', mul_zero]
    · have hd : p ∣ v := by
        by_contra hd
        exact h (isRelPrime_iff_isCoprime.mp (hp.2.irreducible.isRelPrime_iff_not_dvd.mpr hd))
      rw [cubicSymbolAtPrime_eq_zero_of_dvd hp hd, zero_mul]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MixedPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primary mixed characters and squarefree coset Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def mixedSymbol (a b v : Eisenstein) : ℂ := cubicSymbol a v * star (cubicSymbol b v)

lemma mixedSymbol_congr {a b v w : Eisenstein}
    (h : Ideal.Quotient.mk (modulus (a*b)) v = Ideal.Quotient.mk (modulus (a*b)) w) :
    mixedSymbol a b v = mixedSymbol a b w := by
  have hd : a*b ∣ v-w := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  unfold mixedSymbol
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub
    (dvd_trans (dvd_mul_right a b) hd))]
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub
    (dvd_trans (dvd_mul_left b a) hd))]

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebra of fixed angular prime moments

The angular weight is the phase of a nonzero Eisenstein integer raised to
an integer power.  These elementary facts ensure that fixed angular
weights preserve absolute values and distribute through finite prime sums.
-/

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

@[simp] theorem theta_zero (a : Eisenstein) : theta 0 a = 1 := by
  simp [theta]

@[simp] theorem theta_one (ℓ : ℤ) : theta ℓ (1 : Eisenstein) = 1 := by
  simp [theta]

@[simp] theorem theta_mul (ℓ : ℤ) (a b : Eisenstein) :
    theta ℓ (a * b) = theta ℓ a * theta ℓ b := by
  simp only [theta, Subalgebra.coe_mul, norm_mul, Complex.ofReal_mul]
  rw [mul_div_mul_comm, mul_zpow]

@[simp] theorem norm_theta {a : Eisenstein} (ha : a ≠ 0) (ℓ : ℤ) :
    ‖theta ℓ a‖ = 1 := by
  have ha' : (a : ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
  simp [theta, norm_zpow, ha']

@[simp] theorem norm_theta_mul {a : Eisenstein} (ha : a ≠ 0) (ℓ : ℤ) (z : ℂ) :
    ‖theta ℓ a * z‖ = ‖z‖ := by
  rw [norm_mul, norm_theta ha, one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedHecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-order Hecke prime input

The finite-order Hecke prime-sum input specializes to independent prime
factors using the elementary character laws.

The input is the cubic-character consequence of Thorner--Zaman,
*A unified and improved Chebotarev density theorem*, Algebra & Number
Theory 13 (2019), Theorem 1.4, in the Siegel–Walfisz form for cubic Hecke characters.  Only finite-order characters occur in this input;
smooth weights and norm twists follow by partial summation.
-/

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CubicFirstMoment

/-- The primitive cubic characters occurring after cancelling common
factors of two squarefree conductors. -/
def mixedCubic (q₁ q₂ a : Eisenstein) : ℂ :=
  cubicSymbol q₁ a * star (cubicSymbol q₂ a)

theorem mixedCubic_mul {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (a b : Eisenstein) :
    mixedCubic q₁ q₂ (a * b) = mixedCubic q₁ q₂ a * mixedCubic q₁ q₂ b := by
  simp only [mixedCubic, cubicSymbol_mul_upper h₁, cubicSymbol_mul_upper h₂, star_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact corrected-dispersion identities

The polynomials below are those in `eq:dispersion-polynomials` of the
manuscript. The factorization is valid even with a common prime factor:
the already proved Gauss-sum multiplication law then makes the summand zero.
The norm estimates here do not assume the new dispersion bounds.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

/-- The norm twist at real Mellin height `u`. -/
def normTwist (u : ℝ) (a : Eisenstein) : ℂ :=
  Complex.exp ((u * Real.log (norm a) : ℝ) * Complex.I)

@[simp] theorem norm_normTwist (u : ℝ) (a : Eisenstein) : ‖normTwist u a‖ = 1 := by
  simp [normTwist, Complex.norm_exp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeFunctionalEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebra of the published primitive Hecke functional equation.
The completion uses A = sqrt(3 D)/(2 pi), where D is the ideal conductor
norm. See Watkins (2011), Section 3.6, and Rajan (1998), Section 1,
pp. 281--283 for the fixed infinity-type completion. The uncompleted and symmetry-line identities follow from that exact equation. -/

noncomputable section
namespace CubicFirstMoment

def heckeCompleted (A k : ℝ) (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  (A:ℂ)^s * Complex.Gamma (s+(k:ℂ)) * L s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The short Möbius identity on Eisenstein ideals

Nonzero Eisenstein ideals are represented by their finite prime-ideal
exponent vectors. Their arithmetic functions form the multivariate power
series ring: its multiplication is exactly finite Dirichlet convolution.
The norm below is the norm of the product of prime representatives, so
the support statements retain the actual multiplicative ideal norm.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

abbrev EisensteinIdealPrime := {p : Associates Eisenstein // Irreducible p}
abbrev EisensteinIdealExponent := EisensteinIdealPrime →₀ ℕ
abbrev EisensteinArithmeticFunction := MvPowerSeries EisensteinIdealPrime ℝ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDualContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained finite dual polynomials for fixed infinity type. The sole
Gamma strip input is the bounded-strip consequence of NIST DLMF 5.11.9;
there is no arithmetic moment or smooth-duality conclusion in that input. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def angularGammaFEQuotient (k : ℝ) (s : ℂ) : ℂ :=
  Complex.Gamma (1-s+(k:ℂ))/Complex.Gamma (s+(k:ℂ))

/-- The fixed-shift specialization of the uniform vertical Stirling
formula, DLMF 5.11.9. -/
def AngularGammaQuotientStripBound (k a : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ ∈ Icc a (1/2:ℝ), ∀ u : ℝ,
    ‖angularGammaFEQuotient k (σ+(u:ℂ)*Complex.I)‖ ≤ C*(1+|u|)^N


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedAngularHecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative fixed-angular Hecke prime estimates

The published input is the degree-two, nonexceptional specialization of
Kaneko--Thorner, *Highly uniform prime number theorems*, Ann. Inst. Fourier
75 (2025), Theorem 1.2, pp. 1904--1905 (restating Iwaniec--Kowalski,
Theorem 5.13), with the zero-free region and completion from Rajan (1998),
Proposition 1 and Section 1. The exponential conductor-dependent error
is retained. Arbitrary logarithmic savings are derived below; they are
not included among the published-input hypotheses.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CubicFirstMoment

/-- Upper bound for the degree-two analytic conductor: finite conductor
at most `9 N(q₁q₂)`, field discriminant `3`, and gamma shifts `k,k+1`. -/
def angularConductorFactor (ℓ : ℤ) : ℝ :=
  27 * (|(ℓ : ℝ)| / 2 + 3) * (|(ℓ : ℝ)| / 2 + 4)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite primary ideal polynomials and their actual Eisenstein-element
realizations. These sums omit the ramified prime above three. They are
not identified with the complete ideal series of `IdealMellinSeries`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Primary element sums omit every ideal divisible by the prime over three. -/
def primaryElementBall (Y : ℝ) : Finset Eisenstein :=
  (nonzeroNormBall Y).filter primary

@[simp] lemma mem_primaryElementBall {a : Eisenstein} {Y : ℝ} :
    a ∈ primaryElementBall Y ↔ primary a ∧ norm a ≤ Y := by
  simp only [primaryElementBall,Finset.mem_filter,mem_nonzeroNormBall]
  constructor
  · rintro ⟨⟨hN,_⟩,ha⟩
    exact ⟨ha,hN⟩
  · rintro ⟨ha,hN⟩
    exact ⟨⟨hN,primary_ne_zero ha⟩,ha⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler exclusions on the complete ideal lattice. The full norm
ball includes the ramified prime; excluding it is an explicit choice of
prime set, and every rescaling factor is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The squarefree product of a finite set of prime ideals. -/
def primeSetExponent (S : Finset EisensteinIdealPrime) : EisensteinIdealExponent :=
  ∑ p ∈ S, Finsupp.single p 1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedResidueCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mixed cubic residue characters and their finite Fourier transform. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mixedCubic_congr {a b v w : Eisenstein}
    (h : Ideal.Quotient.mk (modulus (a*b)) v = Ideal.Quotient.mk (modulus (a*b)) w) :
    mixedCubic a b v = mixedCubic a b w := mixedSymbol_congr h

lemma mixedCubic_eq_zero_of_nonunit {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (v : Eisenstein) (hv : ¬ IsUnit (Ideal.Quotient.mk (modulus (a*b)) v)) :
    mixedCubic a b v = 0 := by
  by_cases hav : IsCoprime a v
  · have hbv : ¬ IsCoprime b v := fun h => hv (residue_isUnit_of_isCoprime (hav.mul_left h))
    simp [mixedCubic,cubicSymbol_eq_zero_of_not_isCoprime hb hbv]
  · simp [mixedCubic,cubicSymbol_eq_zero_of_not_isCoprime ha hav]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAngularKummerPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-angular prime estimates for the literal ramified numerator

This is the nonexceptional degree-two specialization of Kaneko--Thorner,
*Highly uniform prime number theorems*, Ann. Inst. Fourier 75 (2025),
Theorem 1.2, pp.1904--1905 (Iwaniec--Kowalski, Theorem 5.13), with the
fixed-type zero-free region of Rajan (1998), Proposition 1 and Section 1.
The finite character is `cubicNumeratorChar` of modulus `9*v`; its
identification on primary elements is proved from
`CubicSupplementaryPeriodicity` in `CubicNumeratorCharacter`.

The analytic conductor majorant is
`3 * N(9*v) * (|ell|/2+3) * (|ell|/2+4)`:
`N(9*v)=81*N(v)`, so its constant is 243. The nonzero angular type
excludes a principal/exceptional-real character. The raw input below
retains the exponential conductor error and the prime-power deletion
term. Logarithmic and weighted estimates are deductions, not inputs.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def angularKummerConductorFactor (ℓ : ℤ) : ℝ :=
  9*angularConductorFactor ℓ


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.Erdos970_PNT1_ComplexAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


lemma lem_wReIm (w : ℂ) : w = w.re + Complex.I * w.im := by
  apply Complex.ext
  simp
  simp

def ballDR (R : ℝ) : Set ℂ := Metric.ball (0 : ℂ) R

noncomputable def f_M (R M : ℝ) (_hR : R > 0) (_hM : M > 0)
    (f : ℂ → ℂ)
    (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (_h_zero : f 0 = 0)
    (_h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
ℂ → ℂ := fun z ↦ (if z = 0 then (fderiv ℂ f 0) 1 else f z / z) / (2 * M - f z)

def I := Complex.I

open Complex MeasureTheory intervalIntegral
open scoped Interval

noncomputable def If_taxicab
    {r1 R R0: ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
    (Metric.closedBall (0 : ℂ) r1) → ℂ :=
  fun z =>
    (∫ t in (0 : ℝ)..z.1.re, f (t : ℂ))
    + Complex.I * (∫ τ in (0 : ℝ)..z.1.im, f ((z.1.re : ℂ) + Complex.I * τ))

lemma def_If_z_plus_h
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1) :
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
      = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, f (( (z + h).re : ℂ) + Complex.I * τ)) := by
  rfl

lemma def_If_z
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
      = (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)) := by
  rfl

lemma def_If_w
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (_hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  simp [If_taxicab]

lemma continuous_vertical_line (a : ℂ) :
  Continuous (fun τ : ℝ => ((a.re : ℂ) + Complex.I * (τ : ℂ))) := by
  have hconst : Continuous (fun _ : ℝ => (a.re : ℂ)) := continuous_const
  have hmul : Continuous (fun τ : ℝ => (Complex.I : ℂ) * (τ : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  convert (preTransparency := .instances) hconst.add hmul using 1
  all_goals try with_reducible_and_instances rfl

lemma norm_re_add_I_mul_le_norm (a : ℂ) {τ : ℝ} (hτ : |τ| ≤ |a.im|) :
  ‖((a.re : ℂ) + Complex.I * (τ : ℂ))‖ ≤ ‖a‖ := by
                                                                              
  set z1 : ℂ := ((a.re : ℂ) + Complex.I * (τ : ℂ)) with hz1
                                       
  have hsq_z1 : ‖z1‖ ^ 2 = z1.re ^ 2 + z1.im ^ 2 := by
    have hx : ‖z1‖ ^ 2 - z1.re ^ 2 = z1.im ^ 2 := Complex.sq_norm_sub_sq_re z1
    have hx' := congrArg (fun t : ℝ => t + z1.re ^ 2) hx
                                          
    have : ‖z1‖ ^ 2 = z1.im ^ 2 + z1.re ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [add_comm] using this
  have hsq_a : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    have hx : ‖a‖ ^ 2 - a.re ^ 2 = a.im ^ 2 := Complex.sq_norm_sub_sq_re a
    have hx' := congrArg (fun t : ℝ => t + a.re ^ 2) hx
    have : ‖a‖ ^ 2 = a.im ^ 2 + a.re ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [add_comm] using this
                             
  have hz1_re : z1.re = a.re := by
    simp [hz1, mul_comm]
  have hz1_im : z1.im = τ := by
    simp [hz1, mul_comm]
                                                  
  have hτ_sq : τ ^ 2 ≤ a.im ^ 2 := by
    simpa using (sq_le_sq.mpr hτ)
                    
  have hsq_le : ‖z1‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    have : a.re ^ 2 + τ ^ 2 ≤ a.re ^ 2 + a.im ^ 2 := add_le_add_right hτ_sq _
    simpa [hsq_z1, hz1_re, hz1_im, hsq_a] using this
                               
  have hnonneg : 0 ≤ ‖a‖ := norm_nonneg _
  exact le_of_sq_le_sq hsq_le hnonneg

lemma closedBall_mono_center0 {r1 R : ℝ} (h : r1 ≤ R) :
  Metric.closedBall (0 : ℂ) r1 ⊆ Metric.closedBall (0 : ℂ) R := by
  intro z hz
  have hz' : dist z (0 : ℂ) ≤ r1 := (Metric.mem_closedBall.mp hz)
  exact Metric.mem_closedBall.mpr (le_trans hz' h)

lemma abs_le_abs_of_mem_uIcc_zero {b t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) b) : |t| ≤ |b| := by
  classical
  by_cases hb : 0 ≤ b
  ·                                  
    have ht' : t ∈ Set.Icc (0 : ℝ) b := by
      simpa [Set.uIcc_of_le hb] using ht
    have ht0 : 0 ≤ t := ht'.1
    have htb : t ≤ b := ht'.2
    have htabs : |t| = t := abs_of_nonneg ht0
    have hbabs : |b| = b := abs_of_nonneg hb
    simpa [htabs, hbabs] using htb
  ·                                  
    have ht' : t ∈ Set.Icc b 0 := by
      simpa [Set.uIcc_of_not_le hb] using ht
    have hb_le : b ≤ 0 := le_trans ht'.1 ht'.2
    have ht_le0 : t ≤ 0 := ht'.2
    have hbabs : |b| = -b := abs_of_nonpos hb_le
    have htabs : |t| = -t := abs_of_nonpos ht_le0
    have hneg : -t ≤ -b := neg_le_neg ht'.1
    simpa [htabs, hbabs] using hneg

lemma vertical_intervalIntegrable_of_mem_ball
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {a : ℂ}
    (ha : a ∈ Metric.closedBall (0 : ℂ) r1) :
    IntervalIntegrable (fun τ : ℝ => f (((a.re : ℂ)) + Complex.I * τ)) volume (0 : ℝ) a.im := by
  classical
                                              
  have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
                                 
  let g : ℝ → ℂ := fun τ => ((a.re : ℂ) + Complex.I * (τ : ℂ))
                                                        
  have hg_cont : ContinuousOn g (Set.uIcc (0 : ℝ) a.im) := by
    simpa [g] using (continuous_vertical_line a).continuousOn
                                                                  
  have hg_maps : Set.MapsTo g (Set.uIcc (0 : ℝ) a.im) (Metric.closedBall (0 : ℂ) R) := by
    intro τ hτ
    have hτabs : |τ| ≤ |a.im| := abs_le_abs_of_mem_uIcc_zero hτ
    have hnorm_le_a : ‖g τ‖ ≤ ‖a‖ := by
      simpa [g] using norm_re_add_I_mul_le_norm a hτabs
    have ha_norm : ‖a‖ ≤ r1 := by
      have : dist a (0 : ℂ) ≤ r1 := (Metric.mem_closedBall.mp ha)
      simpa [dist_eq_norm] using this
    have hnorm_le_r1 : ‖g τ‖ ≤ r1 := le_trans hnorm_le_a ha_norm
    have hg_mem_r1 : g τ ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le_r1
    exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) hg_mem_r1
                                                                          
  have hcomp : ContinuousOn (fun τ : ℝ => f (g τ)) (Set.uIcc (0 : ℝ) a.im) := by
                                                      
    convert (preTransparency := .instances) (ContinuousOn.comp (hg := hf_cont) (hf := hg_cont) (h := hg_maps)) using 1; rfl
                                                           
  have hInt : IntervalIntegrable (fun τ : ℝ => f (g τ)) volume (0 : ℝ) a.im :=
    ContinuousOn.intervalIntegrable (u := fun τ : ℝ => f (g τ)) (a := 0) (b := a.im) hcomp
  simpa [g] using hInt

lemma helper_im_of_w (z h : ℂ) : (((((z + h).re : ℂ) + Complex.I * z.im)).im) = z.im := by
  simp [Complex.add_im]

lemma helper_mul_sub_complex (x y : ℂ) : Complex.I * x - Complex.I * y = Complex.I * (x - y) := by
  simp [mul_sub]

lemma helper_re_of_w (z h : ℂ) : (((((z + h).re : ℂ) + Complex.I * z.im)).re) = (z + h).re := by
  simp

lemma diff_If_zh_w
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
      - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      = Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  classical
  intro w
                              
  let g : ℝ → ℂ := fun τ => f (((z + h).re : ℂ) + Complex.I * τ)
                                                              
  have hInt1 : IntervalIntegrable g volume (0 : ℝ) ((z + h).im) := by
    simpa [g] using
      (vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf (a := z + h) hzh)
  have hInt2 : IntervalIntegrable g volume (0 : ℝ) (z.im) := by
    have hInt2' :
        IntervalIntegrable
          (fun τ : ℝ => f (((( (((z + h).re : ℂ) + Complex.I * z.im)).re : ℂ)) + Complex.I * τ))
          volume (0 : ℝ) (((((z + h).re : ℂ) + Complex.I * z.im)).im) :=
      vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf
        (a := (((z + h).re : ℂ) + Complex.I * z.im)) hw
    simpa [g, helper_re_of_w z h, helper_im_of_w z h] using hInt2'
  have hinterval :
      ((∫ τ in (0 : ℝ)..(z + h).im, g τ) - ∫ τ in (0 : ℝ)..z.im, g τ)
      = ∫ τ in z.im..(z + h).im, g τ :=
    intervalIntegral.integral_interval_sub_left (μ := volume) (f := g) hInt1 hInt2
                                          
  have h1 :
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
          + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ) := by
    have hzph := def_If_z_plus_h hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf (z := z) (h := h) hz hzh
    simpa [g] using hzph
  have h2 :
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
        = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
          + Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ) := by
    have hwdef := def_If_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
    simpa [g, w] using hwdef
                                                           
  calc
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
        = ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
            + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ))
          - ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
            + Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [h1, h2]
    _ = (Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ))
          - (Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = Complex.I *
          ((∫ τ in (0 : ℝ)..(z + h).im, g τ)
            - (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [helper_mul_sub_complex]
    _ = Complex.I * (∫ τ in z.im..(z + h).im, g τ) := by
      simpa using congrArg (fun t => Complex.I * t) hinterval
    _ = Complex.I * (∫ τ in z.im..(z + h).im,
          f (((z + h).re : ℂ) + Complex.I * τ)) := by
      simp [g]

lemma diff_If_w_z_initial_form
  {r1 R R0 : ℝ}
  (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z h : ℂ}
  (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
  (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = (∫ t in z.re..w.re, f (t : ℂ))
      + Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (w.re + Complex.I * τ) - f (z.re + Complex.I * τ))) := by
  intro w

  rw [def_If_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw]
  rw [def_If_z hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz]

  have hw_re : w.re = (z + h).re := by simp [w]
  have hw_im : w.im = z.im := by simp [w]

  have step1 :
    ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)))
      - ((∫ t in (0 : ℝ)..z.re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)))
    = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ)) - (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
      + Complex.I * ((∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
        - (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))) := by ring
  rw [step1]

  have horizontal_integrable_zh : IntervalIntegrable (fun t : ℝ => f (t : ℂ)) volume (0 : ℝ) (z + h).re := by
                                                                          
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp hf.continuousOn Complex.continuous_ofReal.continuousOn
    intro t ht
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real]
                                                                  
    have : ‖z + h‖ ≤ r1 := by simp [← dist_zero_right]; exact Metric.mem_closedBall.mp hzh
    have : |(z + h).re| ≤ ‖z + h‖ := Complex.abs_re_le_norm (z + h)
    have : |t| ≤ |(z + h).re| := abs_le_abs_of_mem_uIcc_zero ht
    linarith [le_of_lt hr1_lt_R]

  have horizontal_integrable_z : IntervalIntegrable (fun t : ℝ => f (t : ℂ)) volume (0 : ℝ) z.re := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp hf.continuousOn Complex.continuous_ofReal.continuousOn
    intro t ht
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real]
    have : ‖z‖ ≤ r1 := by simp [← dist_zero_right]; exact Metric.mem_closedBall.mp hz
    have : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have : |t| ≤ |z.re| := abs_le_abs_of_mem_uIcc_zero ht
    linarith [le_of_lt hr1_lt_R]

  have horizontal_eq :
    (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ)) - (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
    = ∫ t in z.re..(z + h).re, f (t : ℂ) := by
    rw [← intervalIntegral.integral_interval_sub_left horizontal_integrable_zh horizontal_integrable_z]

  have vertical_integrable_zh : IntervalIntegrable (fun τ : ℝ => f (((z + h).re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im := by
                                                     
    rw [← hw_re, ← hw_im]
    exact vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hw

  have vertical_integrable_z : IntervalIntegrable (fun τ : ℝ => f ((z.re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im :=
    vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz

  have vertical_eq :
    (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
      - (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))
    = ∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ)) := by
    rw [← intervalIntegral.integral_sub vertical_integrable_zh vertical_integrable_z]

  rw [horizontal_eq, vertical_eq, hw_re]

lemma algebraic_rearrangement_four_terms (a b c d : ℂ) :
    a - b + c - d = 0 → c - d = b - a := by
  intro h

  calc c - d
    = (a - b + c - d) - (a - b) := by ring
    _ = 0 - (a - b) := by rw [h]
    _ = -(a - b) := by ring
    _ = b - a := by ring

lemma real_between_as_convex_combination (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ t = (1 - lam) * b₁ + lam * b₂ := by
                                                        
  cases' le_total b₁ b₂ with h₁ h₂
  case inl =>

    have ht : b₁ ≤ t ∧ t ≤ b₂ := by
      cases' h with h_left h_right
      · exact h_left
      ·                                                                           
        exact ⟨le_trans h₁ h_right.1, le_trans h_right.2 h₁⟩

    by_cases heq : b₁ = b₂
    ·                                              
      use 0
      constructor
      · norm_num
      constructor
      · norm_num
      · rw [heq] at ht ⊢
        have : t = b₂ := le_antisymm ht.2 ht.1
        rw [this]
        ring
    ·                            
      have hlt : b₁ < b₂ := lt_of_le_of_ne h₁ heq
      let lam := (t - b₁) / (b₂ - b₁)
      use lam
      constructor
      ·           
        apply div_nonneg
        · linarith [ht.1]
        · linarith [hlt]
      constructor
      ·                              
        rw [div_le_iff₀]
        · linarith [ht.2]                                         
        · linarith [hlt]                 
      ·                                 
        unfold lam
        have h_nonzero : b₂ - b₁ ≠ 0 := ne_of_gt (sub_pos.2 hlt)
        field_simp [h_nonzero]; ring
  case inr =>

    have ht : b₂ ≤ t ∧ t ≤ b₁ := by
      cases' h with h_left h_right
      ·                                                                           
        exact ⟨le_trans h₂ h_left.1, le_trans h_left.2 h₂⟩
      · exact h_right

    by_cases heq : b₁ = b₂
    ·                                              
      use 0
      constructor
      · norm_num
      constructor
      · norm_num
      · rw [← heq] at ht ⊢
        have : t = b₁ := le_antisymm ht.2 ht.1
        rw [this, heq]
        ring
    ·                            
      have hlt : b₂ < b₁ := lt_of_le_of_ne h₂ (Ne.symm heq)
      let lam := (b₁ - t) / (b₁ - b₂)
      use lam
      constructor
      ·           
        apply div_nonneg
        · linarith [ht.2]                           
        · linarith [hlt]                 
      constructor
      ·                              
        rw [div_le_iff₀]
        · linarith [ht.1]                                         
        · linarith [hlt]                 
      ·                                 
        unfold lam
        have h_nonzero : b₁ - b₂ ≠ 0 := ne_of_gt (sub_pos.2 hlt)
        field_simp [h_nonzero]; ring

lemma convex_combination_mem_segment {E : Type*} [AddCommGroup E] [Module ℝ E] (x y : E) (t : ℝ)
  (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
  (1 - t) • x + t • y ∈ segment ℝ x y := by

  use (1 - t), t
  constructor
  ·             
    linarith [h₁]
  constructor
  ·         
    exact h₀
  constructor
  ·                   
    ring
  ·                                             
    rfl

lemma vertical_line_in_segment (a : ℂ) (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  a + Complex.I * t ∈ segment ℝ (a + Complex.I * b₁) (a + Complex.I * b₂) := by
                                                
  obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination b₁ b₂ t h

  have h_convex : a + Complex.I * t = (1 - lam) • (a + Complex.I * b₁) + lam • (a + Complex.I * b₂) := by
                                           
    simp only [Complex.real_smul]
                                               
    rw [h_t_eq]
                                 
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
                                                                              
    rw [mul_add]
                                                      
    ring

  rw [h_convex]
  exact convex_combination_mem_segment (a + Complex.I * b₁) (a + Complex.I * b₂) lam h_lam_nonneg h_lam_le_one

lemma horizontal_line_in_segment (a : ℝ) (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  (t : ℂ) + Complex.I * a ∈ segment ℝ ((b₁ : ℂ) + Complex.I * a) ((b₂ : ℂ) + Complex.I * a) := by
                                                     
  obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination b₁ b₂ t h
                                                                        
  have h_convex : (t : ℂ) + Complex.I * a
      = (1 - lam) • ((b₁ : ℂ) + Complex.I * a) + lam • ((b₂ : ℂ) + Complex.I * a) := by
    simp only [Complex.real_smul]
                   
    rw [h_t_eq]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
                                       
  simpa [h_convex] using
    (convex_combination_mem_segment ((b₁ : ℂ) + Complex.I * a) ((b₂ : ℂ) + Complex.I * a) lam h_lam_nonneg h_lam_le_one)

lemma intervalIntegrable_of_continuousOn_range (f : ℂ → ℂ) (g : ℝ → ℂ) (a b : ℝ) (S : Set ℂ)
  (hf : ContinuousOn f S) (hg : Continuous g)
  (hrange : ∀ t ∈ Set.uIcc a b, g t ∈ S) :
  IntervalIntegrable (f ∘ g) volume a b := by
                                                           
  have h_comp : ContinuousOn (f ∘ g) (Set.uIcc a b) := by
    apply ContinuousOn.comp hf (hg.continuousOn) hrange
                                                                     
  exact h_comp.intervalIntegrable

lemma intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball
  {r1 R : ℝ} (hr1_lt_R : r1 < R) {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {a : ℂ} {b₁ b₂ : ℝ}
  (h₁ : ‖a + Complex.I * b₁‖ ≤ r1) (h₂ : ‖a + Complex.I * b₂‖ ≤ r1) :
  IntervalIntegrable (fun t => f (a + Complex.I * t)) volume b₁ b₂ := by
                                                                    
  apply intervalIntegrable_of_continuousOn_range f (fun t => a + Complex.I * ↑t) b₁ b₂ (Metric.closedBall (0 : ℂ) R)
  ·                                                                              
    exact AnalyticOnNhd.continuousOn hf
  ·                                               
    exact Continuous.add continuous_const (Continuous.mul continuous_const continuous_ofReal)
  ·                                                         
    intro t ht
                                                                       
    have h_in_r1 : ‖a + Complex.I * ↑t‖ ≤ r1 := by
                                                            
      have h_segment : a + Complex.I * ↑t ∈ segment ℝ (a + Complex.I * b₁) (a + Complex.I * b₂) := by
        apply vertical_line_in_segment
        exact Set.mem_uIcc.mp ht
                                                              
      have h₁_mem : a + Complex.I * b₁ ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      have h₂_mem : a + Complex.I * b₂ ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
                                         
      have h_subset := (convex_closedBall (0 : ℂ) r1).segment_subset h₁_mem h₂_mem
      have h_in_ball := h_subset h_segment
      rwa [Metric.mem_closedBall, dist_zero_right] at h_in_ball
                                                              
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans h_in_r1 (le_of_lt hr1_lt_R)

lemma cauchy_for_rectangles
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z w : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r1)
    (hzw : ((w.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1)
    (hwz : ((z.re : ℂ) + Complex.I * w.im) ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ x in z.re..w.re, f ((x : ℂ) + Complex.I * (z.im)))
    - (∫ x in z.re..w.re, f ((x : ℂ) + Complex.I * (w.im)))
    + Complex.I * (∫ y in z.im..w.im, f ((w.re : ℂ) + Complex.I * y))
    - Complex.I * (∫ y in z.im..w.im, f ((z.re : ℂ) + Complex.I * y)) = 0 := by
  classical
                                                                                    
  have hA : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                          
    have hz_eq : z = (z.re : ℂ) + Complex.I * z.im := by
      exact (lem_wReIm z)
    rwa [← hz_eq]
  have hC : ((w.re : ℂ) + Complex.I * w.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                          
    have hw_eq : w = (w.re : ℂ) + Complex.I * w.im := by
      exact (lem_wReIm w)
    rwa [← hw_eq]
                                                                                                
  have h_left_in_ball : ∀ y ∈ Set.uIcc z.im w.im,
      ((z.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro y hy
    have hseg : (z.re : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im) ((z.re : ℂ) + Complex.I * w.im) := by
      simpa using vertical_line_in_segment (a := (z.re : ℂ)) (b₁ := z.im) (b₂ := w.im) (t := y)
        (h := Set.mem_uIcc.mp hy)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hA hwz hseg
  have h_right_in_ball : ∀ y ∈ Set.uIcc z.im w.im,
      ((w.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro y hy
    have hseg : (w.re : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((w.re : ℂ) + Complex.I * z.im) ((w.re : ℂ) + Complex.I * w.im) := by
      simpa using vertical_line_in_segment (a := (w.re : ℂ)) (b₁ := z.im) (b₂ := w.im) (t := y)
        (h := Set.mem_uIcc.mp hy)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hzw hC hseg
  have h_point_in_ball : ∀ x ∈ Set.uIcc z.re w.re, ∀ y ∈ Set.uIcc z.im w.im,
      ((x : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro x hx y hy
    have hL : ((z.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := h_left_in_ball y hy
    have hR' : ((w.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := h_right_in_ball y hy
                                                                
    obtain ⟨lam, hlam0, hlam1, hx_eq⟩ := real_between_as_convex_combination z.re w.re x (Set.mem_uIcc.mp hx)
    have hseg_horiz : (x : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((z.re : ℂ) + Complex.I * (y : ℂ)) ((w.re : ℂ) + Complex.I * (y : ℂ)) := by
                                    
      have : (x : ℂ) + Complex.I * (y : ℂ)
          = (1 - lam) • ((z.re : ℂ) + Complex.I * (y : ℂ)) + lam • ((w.re : ℂ) + Complex.I * (y : ℂ)) := by
        simp only [Complex.real_smul]
                                                    
        rw [hx_eq]
        simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      simpa [this] using
        (convex_combination_mem_segment ((z.re : ℂ) + Complex.I * (y : ℂ)) ((w.re : ℂ) + Complex.I * (y : ℂ)) lam hlam0 hlam1)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hL hR' hseg_horiz
                                                                
  set S := ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
  have hS_subset_r1 : S ⊆ Metric.closedBall (0 : ℂ) r1 := by
    intro p hp
    have hx : p.re ∈ [[z.re, w.re]] := hp.1
    have hy : p.im ∈ [[z.im, w.im]] := hp.2
                                                              
    have : ((p.re : ℂ) + Complex.I * (p.im : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 :=
      h_point_in_ball p.re hx p.im hy
                                                                       
    have hp_eq : p = (p.re : ℂ) + Complex.I * (p.im : ℂ) := lem_wReIm p
    rwa [hp_eq]
  have hS_subset_R : S ⊆ Metric.closedBall (0 : ℂ) R :=
    fun p hp => (closedBall_mono_center0 (le_of_lt hr1_lt_R)) (hS_subset_r1 hp)
                                                                               
  have Hdiff : DifferentiableOn ℂ f S := by
    intro p hp
    have hpR : p ∈ Metric.closedBall (0 : ℂ) R := hS_subset_R hp
    exact (hf p hpR).differentiableAt.differentiableWithinAt
                                                          
  simpa [smul_eq_mul, mul_comm] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w Hdiff

lemma cauchy_for_horizontal_strip
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ t in z.re..(z + h).re, f (t : ℂ))
    - (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
    + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
    - Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)) = 0 := by
                                                                               
  let z₀ : ℂ := (z.re : ℂ)
  let w₀ : ℂ := (z + h).re + Complex.I * z.im
                         
  have hz₀ : z₀ ∈ Metric.closedBall (0 : ℂ) r1 := by
    have hz_norm : ‖z‖ ≤ r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzre_le : ‖(z.re : ℂ)‖ ≤ ‖z‖ := by
      rw [Complex.norm_real]
      exact Complex.abs_re_le_norm z
    have : ‖z₀‖ ≤ r1 := le_trans hzre_le hz_norm
    simpa [z₀, Metric.mem_closedBall, dist_eq_norm] using this
  have hw₀ : w₀ ∈ Metric.closedBall (0 : ℂ) r1 := hw
                                                  
  have hzw : ((w₀.re : ℂ) + Complex.I * z₀.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                                                          
    have h1 : ((w₀.re : ℂ) + Complex.I * z₀.im) = ((z + h).re : ℂ) := by
      simp [w₀, z₀, Complex.ofReal_im, mul_zero, add_zero]
    rw [h1]
    have h2 : ‖((z + h).re : ℂ)‖ ≤ ‖z + h‖ := by
      rw [Complex.norm_real]
      exact Complex.abs_re_le_norm (z + h)
    have h3 : ‖z + h‖ ≤ r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzh
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_trans h2 h3
  have hwz : ((z₀.re : ℂ) + Complex.I * w₀.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
                                            
    have h1 : ((z₀.re : ℂ) + Complex.I * w₀.im) = z := by
      simp [z₀, w₀, Complex.ofReal_re]
      exact (lem_wReIm z).symm
    rw [h1]
    exact hz
                                   
  have H := cauchy_for_rectangles (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz₀ hw₀ hzw hwz

  rw [(show z₀.re = z.re by simp [z₀])] at H
  rw [(show z₀.im = (0 : ℝ) by simp [z₀])] at H
  rw [(show w₀.re = (z + h).re by simp [w₀])] at H
  rw [(show w₀.im = z.im by simp [w₀])] at H

  convert (preTransparency := .instances) H using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Complex.ofReal_zero, mul_zero, add_zero]

lemma integrability_from_cauchy_horizontal_strip
    {r1 R R0 : ℝ} (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r1) (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    IntervalIntegrable (fun τ => f (((z + h).re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im ∧
    IntervalIntegrable (fun τ => f ((z.re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im := by
  constructor
  ·                                                         
    apply intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball hr1_lt_R hf
    ·                                           
      simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_real]
      rw [Metric.mem_closedBall, dist_zero_right] at hzh
      exact le_trans (Complex.abs_re_le_norm (z + h)) hzh
    ·                                              
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      exact hw
  ·                                                    
    apply intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball hr1_lt_R hf
    ·                                     
      simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_real]
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact le_trans (Complex.abs_re_le_norm z) hz
    ·                                        
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [← lem_wReIm z]
      exact hz

lemma cauchy_rearrangement_step1
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ)))
      = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) - (∫ t in z.re..(z + h).re, f (t : ℂ)) := by
                                   
  have H := cauchy_for_horizontal_strip hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have integrable := integrability_from_cauchy_horizontal_strip hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have rearrange := algebraic_rearrangement_four_terms
    (∫ t in z.re..(z + h).re, f (t : ℂ))
    (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
    (Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)))
    (Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)))
    H

  have vertical_linearity :
    Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
    - Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))
    = Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ))) := by
    rw [← mul_sub]
    rw [← intervalIntegral.integral_sub integrable.1 integrable.2]

  rw [← vertical_linearity]
  exact rearrange

lemma diff_If_w_z
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
      = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) := by

  have initial_form := diff_If_w_z_initial_form hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have rearrange_step := cauchy_rearrangement_step1 hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have w_re_eq : (((z + h).re : ℂ) + Complex.I * z.im).re = (z + h).re := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]

  simp_rw [initial_form, w_re_eq, rearrange_step]

  ring

lemma If_difference_is_L_path_integral
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
      + Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by

  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im

  calc If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
       - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
     = (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩)
       + (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
          - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩) := by ring
     _ = Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ))
       + (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) := by
       rw [diff_If_zh_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw,
           diff_If_w_z hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw]
     _ = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
       + Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by ring

lemma If_diff_add_sub_identity
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    =
    (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z) + f z)
    + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z) + f z) := by
                                                                                               
  have H :=
    If_difference_is_L_path_integral (hr1_pos) (hr1_lt_R) (hR_lt_R0) (hR0_lt_one) hf hz hzh hw
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using H

lemma intervalIntegrable_of_analyticOnNhd_of_horizontal_endpoints_in_smaller_ball
  {r1 R : ℝ} (hr1_lt_R : r1 < R) {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {im_part : ℝ} {a b : ℝ}
  (h₁ : ‖(a : ℂ) + Complex.I * im_part‖ ≤ r1) (h₂ : ‖(b : ℂ) + Complex.I * im_part‖ ≤ r1) :
  IntervalIntegrable (fun t => f ((t : ℂ) + Complex.I * im_part)) volume a b := by
                                                                    
  apply intervalIntegrable_of_continuousOn_range f (fun t => (t : ℂ) + Complex.I * im_part) a b (Metric.closedBall (0 : ℂ) R)
  ·                                                                              
    exact AnalyticOnNhd.continuousOn hf
  ·                                                                     
    exact Continuous.add continuous_ofReal continuous_const
  ·                                                         
    intro t ht
                                                                       
    have h_in_r1 : ‖(t : ℂ) + Complex.I * im_part‖ ≤ r1 := by
                                                            
      have h_segment : (t : ℂ) + Complex.I * im_part ∈ segment ℝ ((a : ℂ) + Complex.I * im_part) ((b : ℂ) + Complex.I * im_part) := by

        obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination a b t (Set.mem_uIcc.mp ht)

        have h_convex : (t : ℂ) + Complex.I * im_part = (1 - lam) • ((a : ℂ) + Complex.I * im_part) + lam • ((b : ℂ) + Complex.I * im_part) := by
                                                 
          simp only [Complex.real_smul]
                                                   
          rw [h_t_eq]
                                       
          simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
                                             
          ring

        rw [h_convex]
        exact convex_combination_mem_segment ((a : ℂ) + Complex.I * im_part) ((b : ℂ) + Complex.I * im_part) lam h_lam_nonneg h_lam_le_one

      have h₁_mem : (a : ℂ) + Complex.I * im_part ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      have h₂_mem : (b : ℂ) + Complex.I * im_part ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
                                         
      have h_subset := (convex_closedBall (0 : ℂ) r1).segment_subset h₁_mem h₂_mem
      have h_in_ball := h_subset h_segment
      rwa [Metric.mem_closedBall, dist_zero_right] at h_in_ball
                                                              
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans h_in_r1 (le_of_lt hr1_lt_R)

lemma If_diff_linearity
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    =
    ((∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
     + (∫ _t in z.re..(z + h).re, f z))
    + Complex.I *
      ((∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))
       + (∫ _τ in z.im..(z + h).im, f z)) := by
                                                                                             
  have H := If_diff_add_sub_identity hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  have hz_norm : ‖z‖ ≤ r1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
  have hzh_norm : ‖z + h‖ ≤ r1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hzh
  have hw_norm : ‖((z + h).re : ℂ) + Complex.I * z.im‖ ≤ r1 := by
    rwa [Metric.mem_closedBall, dist_zero_right] at hw

  have h_z_eq : z = (z.re : ℂ) + Complex.I * z.im := lem_wReIm z
  have h_zh_eq : z + h = ((z + h).re : ℂ) + Complex.I * (z + h).im := lem_wReIm (z + h)

  have hz_endpoint : ‖(z.re : ℂ) + Complex.I * z.im‖ ≤ r1 := by rwa [← h_z_eq]
  have h_horiz_integrable := intervalIntegrable_of_analyticOnNhd_of_horizontal_endpoints_in_smaller_ball
    hr1_lt_R hf hz_endpoint hw_norm

  have hzh_endpoint : ‖((z + h).re : ℂ) + Complex.I * (z + h).im‖ ≤ r1 := by rwa [← h_zh_eq]
  have h_vert_integrable := intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball
    hr1_lt_R hf hw_norm hzh_endpoint

  have h_const_horiz : IntervalIntegrable (fun _ => f z) volume z.re (z + h).re := intervalIntegrable_const
  have h_const_vert : IntervalIntegrable (fun _ => f z) volume z.im (z + h).im := intervalIntegrable_const

  have h_diff_horiz : IntervalIntegrable (fun t => f (t + Complex.I * z.im) - f z) volume z.re (z + h).re :=
    IntervalIntegrable.sub h_horiz_integrable h_const_horiz

  have h_diff_vert : IntervalIntegrable (fun τ => f (((z + h).re : ℂ) + Complex.I * τ) - f z) volume z.im (z + h).im :=
    IntervalIntegrable.sub h_vert_integrable h_const_vert

  have h1 : ∫ t in z.re..(z + h).re, ((f (t + Complex.I * z.im) - f z) + f z) =
           (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)) + (∫ t in z.re..(z + h).re, f z) :=
    intervalIntegral.integral_add h_diff_horiz h_const_horiz

  have h2 : ∫ τ in z.im..(z + h).im, ((f (((z + h).re : ℂ) + Complex.I * τ) - f z) + f z) =
           (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)) + (∫ τ in z.im..(z + h).im, f z) :=
    intervalIntegral.integral_add h_diff_vert h_const_vert

  rw [H, h1, h2, mul_add]

lemma integral_of_constant_over_L_path
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (_hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ _t in z.re..(z + h).re, f z) + Complex.I * (∫ _τ in z.im..(z + h).im, f z)
      = f z * h := by
                                                           
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const]

  rw [Complex.add_re, Complex.add_im]
  simp only [add_sub_cancel_left]

  rw [Complex.real_smul, Complex.real_smul]

  rw [← mul_assoc]

  rw [← add_mul]

  rw [mul_comm Complex.I (↑h.im)]

  rw [Complex.re_add_im h]

  rw [mul_comm]

noncomputable def Err
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (z h : ℂ) : ℂ :=
  (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
  + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))

lemma If_diff_decomposition_final
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = f z * h
      + Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
                                                                                      
  have H :=
    If_diff_linearity (hr1_pos) (hr1_lt_R) (hR_lt_R0) (hR0_lt_one)
      (f := f) (hf := hf)
      (z := z) (h := h)
      (hz := hz) (hzh := hzh) (hw := hw)
                                                                   
  let A : ℂ := ∫ t in z.re..(z + h).re, f (t + Complex.I * z.im) - f z
  let B : ℂ := ∫ t in z.re..(z + h).re, f z
  let C : ℂ := ∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ) - f z
  let D : ℂ := ∫ τ in z.im..(z + h).im, f z
                                                                    
  have hH' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + B) + Complex.I * (C + D) := by
    simpa [A, B, C, D, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using H
                                                                          
  have hsplit : (A + B) + Complex.I * (C + D)
      = (A + Complex.I * C) + (B + Complex.I * D) := by ring
  have hH'' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + Complex.I * C) + (B + Complex.I * D) := by
    simpa [hsplit] using hH'
                                                               
  have hBD : (B + Complex.I * D) = f z * h := by
    simpa [B, D] using
      integral_of_constant_over_L_path (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh
  have hH''' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + Complex.I * C) + f z * h := by
    simpa [hBD] using hH''
                                                                
  have hH4 : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h + f z * h := by
    simpa [Err, A, C, add_comm, add_left_comm, add_assoc] using hH'''
                                                         
  simpa [Err, add_comm, add_left_comm, add_assoc] using hH4

noncomputable def S_horiz (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
        r = ‖f (t + Complex.I * z.im) - f z‖}

noncomputable def S_vert (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
        r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}

noncomputable def S_max (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  max (S_horiz z h f) (S_vert z h f)

lemma bound_on_Err
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖
      ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := by
                                                          
  unfold Err
                                    
  have hsplit :
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
      ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
        + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ :=
    norm_add_le _ _

  have hI : ‖Complex.I‖ = (1 : ℝ) := by simp
  have hvertnorm :
      ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
        = ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by
    simp [hI, one_mul]

  set SH : Set ℝ := {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
      r = ‖f (t + Complex.I * z.im) - f z‖}
  have hbdd_SH : BddAbove SH := by
    classical
                                                
    have hK : IsCompact (Set.uIcc z.re (z + h).re) := isCompact_uIcc
                                  
    let γ : ℝ → ℂ := fun t => (t : ℂ) + Complex.I * z.im
    have hγ_cont : Continuous γ := by
      convert (preTransparency := .instances) (Complex.continuous_ofReal.add (continuous_const (y := Complex.I * (z.im : ℂ)))) using 1
      all_goals try with_reducible_and_instances rfl
    have hz_mem : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show (z.re : ℂ) + Complex.I * z.im = z.re + z.im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    have hw_mem : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hw
    have hseg_subset :
        (γ '' Set.uIcc z.re (z + h).re) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim
      rcases hwim with ⟨t, ht, rfl⟩
                                                                  
      have hseg : ((t : ℂ) + Complex.I * z.im)
          ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * z.im) := by

        have := horizontal_line_in_segment (a := z.im) (b₁ := z.re) (b₂ := (z + h).re)
          (t := t) (by simpa [Set.mem_uIcc] using ht)
        simpa using this
      have hz_in : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hz_mem
      have hw_in : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hw_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simpa [Metric.mem_closedBall, dist_zero_right] using hw'
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
                                                        
    have hmaps : Set.MapsTo γ (Set.uIcc z.re (z + h).re) (Metric.closedBall (0 : ℂ) R) := by
      intro t ht
      have himg_r1 : γ t ∈ Metric.closedBall (0 : ℂ) r1 := by
        exact hseg_subset (Set.mem_image_of_mem _ ht)
      exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) himg_r1
    have hcont_on : ContinuousOn (fun t => f (γ t)) (Set.uIcc z.re (z + h).re) := by
      convert (preTransparency := .instances) (ContinuousOn.comp (hf_cont) (hγ_cont.continuousOn) hmaps) using 1; rfl
                                                         
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun t => ‖f (γ t) - f z‖) (Set.uIcc z.re (z + h).re) := by
                                              
      have h_cont_sub : ContinuousOn (fun t => f (γ t) - f z) (Set.uIcc z.re (z + h).re) :=
        hcont_on.sub continuousOn_const
                        
      exact h_cont_sub.norm
                                            
    have himage_compact : IsCompact ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      IsCompact.image_of_continuousOn hK hR_cont
                                    
    have hSH_eq : SH = (fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re := by
      ext r; constructor
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
                                           
    have : BddAbove ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      himage_compact.bddAbove
    simpa [hSH_eq] using this

  set SV : Set ℝ := {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
      r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}
  have hbdd_SV : BddAbove SV := by
    classical
                                          
    have hK : IsCompact (Set.uIcc z.im (z + h).im) := isCompact_uIcc
    let γv : ℝ → ℂ := fun τ => ((z + h).re : ℂ) + Complex.I * τ
    have hγv_cont : Continuous γv := by
      have hmul : Continuous (fun τ : ℝ => Complex.I * (τ : ℂ)) := by
        exact continuous_const.mul Complex.continuous_ofReal
      simp only [γv]
      exact continuous_const.add hmul
    have hw_mem' : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    have hzh_mem : (((z + h).re : ℂ) + Complex.I * (z + h).im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show ((z + h).re : ℂ) + Complex.I * (z + h).im = (z + h).re + (z + h).im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hzh
    have hseg_subset :
        (γv '' Set.uIcc z.im (z + h).im) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim; rcases hwim with ⟨τ, hτ, rfl⟩
      have hseg : (((z + h).re : ℂ) + Complex.I * τ)
          ∈ segment ℝ (((z + h).re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * (z + h).im) := by
        have := vertical_line_in_segment (((z + h).re : ℂ)) (b₁ := z.im) (b₂ := (z + h).im) (t := τ)
          (by simpa [Set.mem_uIcc] using hτ)
        simpa using this
      have hz_in := hw_mem'
      have hw_in := hzh_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simp only [Metric.mem_closedBall, dist_zero_right] at hw'
      rwa [Metric.mem_closedBall, dist_zero_right]
    have hmaps : Set.MapsTo γv (Set.uIcc z.im (z + h).im) (Metric.closedBall (0 : ℂ) R) := by
      intro τ hτ; have : γv τ ∈ Metric.closedBall (0 : ℂ) r1 := hseg_subset (Set.mem_image_of_mem _ hτ)
      exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) this
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
    have hcont_on : ContinuousOn (fun τ => f (γv τ)) (Set.uIcc z.im (z + h).im) := by
      convert (preTransparency := .instances) (ContinuousOn.comp (hf_cont) (hγv_cont.continuousOn) hmaps) using 1; rfl
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun τ => ‖f (γv τ) - f z‖) (Set.uIcc z.im (z + h).im) := by
      have h1 : ContinuousOn (fun τ => f (γv τ) - f z) (Set.uIcc z.im (z + h).im) := by
        exact hcont_on.sub continuousOn_const
      exact h1.norm
    have himage_compact : IsCompact ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      IsCompact.image_of_continuousOn hK hR_cont
    have hSV_eq : SV = (fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im := by
      ext r; constructor
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
    have : BddAbove ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      himage_compact.bddAbove
    simpa [hSV_eq] using this

  have hC_horiz : ∀ t ∈ Set.uIcc z.re (z + h).re,
      ‖(f (t + Complex.I * z.im) - f z)‖ ≤ S_horiz z h f := by
    intro t ht
    have hx : ‖f (t + Complex.I * z.im) - f z‖ ∈ SH := ⟨t, ht, rfl⟩
                                              
    have : S_horiz z h f = sSup SH := rfl
    simpa [this] using (le_csSup hbdd_SH hx)

  have hC_vert : ∀ τ ∈ Set.uIcc z.im (z + h).im,
      ‖(f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ S_vert z h f := by
    intro τ hτ
    have hx : ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖ ∈ SV := ⟨τ, hτ, rfl⟩
    have : S_vert z h f = sSup SV := rfl
    simpa [this] using (le_csSup hbdd_SV hx)

  have hH : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            ≤ |(z + h).re - z.re| * S_horiz z h f := by
                                           
    have h_bound : ∀ t, t ∈ [[z.re, (z + h).re]] → ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht; exact hC_horiz t ht
    have h_int : ∀ t ∈ Ι z.re (z + h).re, ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht
      have ht_uIcc : t ∈ Set.uIcc z.re (z + h).re := by
                                             
        exact Set.uIoc_subset_uIcc ht
      exact h_bound t ht_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    convert (preTransparency := .instances) this using 1
    all_goals try with_reducible_and_instances rfl
    ring

  have hV : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
            ≤ |(z + h).im - z.im| * S_vert z h f := by
    have h_bound : ∀ τ, τ ∈ [[z.im, (z + h).im]] → ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ; exact hC_vert τ hτ
    have h_int : ∀ τ ∈ Ι z.im (z + h).im, ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ
      have hτ_uIcc : τ ∈ Set.uIcc z.im (z + h).im := by
                                             
        exact Set.uIoc_subset_uIcc hτ
      exact h_bound τ hτ_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    rwa [mul_comm] at this

  have hre' : (z + h).re - z.re = h.re := by
    simp [Complex.add_re]
  have him' : (z + h).im - z.im = h.im := by
    simp [Complex.add_im]
  have hre : |(z + h).re - z.re| = |h.re| := by simp
  have him : |(z + h).im - z.im| = |h.im| := by simp

  have hH' : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
                ≤ |h.re| * S_max z h f := by
    have : S_horiz z h f ≤ S_max z h f := by exact le_max_left _ _
                                 
    have hH_rewritten : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖ ≤ |h.re| * S_horiz z h f := by
      rwa [hre] at hH
                           
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.re))
    exact le_trans hH_rewritten h_bound

  have hV' : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
                ≤ |h.im| * S_max z h f := by
    have : S_vert z h f ≤ S_max z h f := by exact le_max_right _ _
                                 
    have hV_rewritten : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ |h.im| * S_vert z h f := by
      rwa [him] at hV
                           
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.im))
    exact le_trans hV_rewritten h_bound

  have :=
    calc
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
          ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ := hsplit
      _ = ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by simp
      _ ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := add_le_add hH' hV'

  simpa [Err] using this

lemma S_horiz_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_horiz z h f := by
                                                         
  unfold S_horiz
  apply Real.sSup_nonneg
  intro r hr; rcases hr with ⟨t, ht, rfl⟩; exact norm_nonneg _

lemma S_max_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_max z h f := by
  unfold S_max
  have h1 : 0 ≤ S_horiz z h f := S_horiz_nonneg z h f
  exact le_trans h1 (le_max_left _ _)

lemma bound_on_Err_ratio
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1)
    (hh : h ≠ 0) :
    ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤ 2 * S_max z h f := by

  have h_abs_eq : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ = ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ := rfl

  have h1 := bound_on_Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
                                                                                  
  rw [← add_mul] at h1

  have h_norm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh

  have h2 : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖ / ‖h‖ ≤
            (|h.re| + |h.im|) * S_max z h f / ‖h‖ := by
    exact div_le_div_of_nonneg_right h1 (le_of_lt h_norm_pos)

  rw [← norm_div] at h2

  have h2' : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤
             (|h.re| + |h.im|) / ‖h‖ * S_max z h f := by
    rw [← div_mul_eq_mul_div] at h2
    exact h2

  have h3 : |h.re| + |h.im| ≤ 2 * ‖h‖ := by
                                                                
    calc |h.re| + |h.im|
      ≤ ‖h‖ + ‖h‖ := add_le_add (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
      _ = 2 * ‖h‖ := by ring

  have h4 : (|h.re| + |h.im|) / ‖h‖ ≤ 2 := by
                                                                                         
    rw [div_le_iff₀ h_norm_pos]
    exact h3

  calc ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖
    ≤ (|h.re| + |h.im|) / ‖h‖ * S_max z h f := h2'
    _ ≤ 2 * S_max z h f := mul_le_mul_of_nonneg_right h4 (S_max_nonneg z h f)
open Filter Topology

lemma abs_horizontal_diff_eq_abs_real (z : ℂ) (t : ℝ) : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := by
                                                           
  have h : (t : ℂ) + Complex.I * z.im - z = (t - z.re : ℂ) := by
    apply Complex.ext_iff.mpr
    constructor
    ·                                      
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
                 Complex.I_re, Complex.I_im, Complex.ofReal_im]
      ring
    ·                                       
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
                 Complex.I_re, Complex.I_im, Complex.ofReal_re]
      ring

  rw [h]
                                                                         
  rw [← Complex.ofReal_sub]
                                                                             
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma abs_sub_le_of_mem_uIcc (a b t : ℝ) (ht : t ∈ Set.uIcc a b) : |t - a| ≤ |b - a| ∧ |b - t| ≤ |b - a| := by
                                                  
  have h1 : a ≤ b ∨ b ≤ a := le_total a b
  rcases h1 with hle | hle
  ·                             
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : a ≤ t ∧ t ≤ b := by simpa using ht'
    constructor
    · have h_ta : |t - a| = t - a := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.left)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_right h_bounds.right a
    · have h_bt : |b - t| = b - t := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.right)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_left h_bounds.left b
  ·                         
    have ht' : t ∈ Set.Icc b a := by
      rw [Set.uIcc_comm] at ht
      simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : b ≤ t ∧ t ≤ a := by simpa using ht'
    constructor
    · have h_ta : |t - a| = a - t := by simp [abs_of_nonpos (sub_nonpos.mpr h_bounds.right)]
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_left h_bounds.left a
    · have h_bt : |b - t| = t - b := by
        rw [abs_of_nonpos (sub_nonpos.mpr h_bounds.left)]
        ring
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_right h_bounds.right b

lemma abs_vertical_core (z h : ℂ) (τ : ℝ) : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| := by
                                                                           
  have h1 : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |((h.re : ℝ) + Complex.I * (τ - z.im)).re| + |((h.re : ℝ) + Complex.I * (τ - z.im)).im| := by
    apply Complex.norm_le_abs_re_add_abs_im

  have h2 : ((h.re : ℝ) + Complex.I * (τ - z.im)).re = h.re := by simp
  have h3 : ((h.re : ℝ) + Complex.I * (τ - z.im)).im = τ - z.im := by simp

  rw [h2, h3] at h1
  exact h1

lemma mem_closedBall_mono_radius {z : ℂ} {r R : ℝ} (hz : z ∈ Metric.closedBall (0 : ℂ) r) (h : r ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using le_trans (by simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz) h

lemma tendsto_of_nonneg_local_bound {g : ℂ → ℝ}
  (h_nonneg : ∀ h, 0 ≤ g h)
  (h_loc : ∀ ε > 0, ∃ δ > 0, ∀ h, ‖h‖ < δ → g h ≤ ε) :
  Tendsto g (𝓝 (0:ℂ)) (𝓝 (0:ℝ)) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
                                                       
  have hε_half : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨δ, hδ_pos, hδ⟩ := h_loc (ε / 2) hε_half
  use δ
  exact ⟨hδ_pos, fun h hh_dist => by
    rw [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (h_nonneg h)]
    have : g h ≤ ε / 2 := hδ h (by rwa [Complex.dist_eq, sub_zero] at hh_dist)
    linarith⟩

lemma sum_abs_le_two_mul {x y A : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ A) : |x| + |y| ≤ (2:ℝ) * A := by
  have := add_le_add hx hy
  simpa [two_mul] using this

lemma two_norm_lt_of_norm_lt_half {h : ℂ} {δ : ℝ} (_hpos : 0 < δ) (hbound : ‖h‖ < δ/2) : (2:ℝ) * ‖h‖ < δ := by
  have := mul_lt_mul_of_pos_left hbound (by norm_num : (0:ℝ) < 2)
  simpa [two_mul, add_halves] using this

lemma limit_of_S_is_zero
    {r1 R R0 : ℝ}
  (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) := by
                                                                  
  have f_cont_at_z : ContinuousAt f z := by
                                                                     
    have hz_in_R : z ∈ Metric.closedBall (0 : ℂ) R :=
      mem_closedBall_mono_radius hz (le_of_lt hr1_lt_R)
                                        
    exact (hf z hz_in_R).continuousAt

  apply tendsto_of_nonneg_local_bound
  ·                                  
    exact fun h => S_max_nonneg z h f
  ·                                                                   
    intro ε hε_pos
                                        
    rw [Metric.continuousAt_iff] at f_cont_at_z
    obtain ⟨δ₁, hδ₁_pos, hf_bound⟩ := f_cont_at_z ε hε_pos

    use δ₁ / 2
    constructor
    · exact half_pos hδ₁_pos
    · intro h hh_norm

      unfold S_max
      apply max_le

      · unfold S_horiz
                                                 
        apply Real.sSup_le
        ·                                        
          intro r hr
          obtain ⟨t, ht, rfl⟩ := hr

          have key_dist : dist ((t : ℂ) + Complex.I * z.im) z < δ₁ := by
                                                                     
            rw [dist_eq]
                                                                         
            have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := abs_horizontal_diff_eq_abs_real z t
            simp [eq_transform]
                                                                
            have t_bound : |t - z.re| ≤ |(z + h).re - z.re| := (abs_sub_le_of_mem_uIcc z.re (z + h).re t ht).1
            have re_diff_le : |(z + h).re - z.re| ≤ ‖h‖ := by
                                       
              simpa [Complex.add_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (Complex.abs_re_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            calc |t - z.re|
              _ ≤ |(z + h).re - z.re| := t_bound
              _ ≤ ‖h‖ := re_diff_le
              _ < δ₁ / 2 := h_bound
              _ < δ₁ := by linarith
                                              
          have f_dist := hf_bound key_dist
                                                         
          rw [dist_eq] at f_dist
                                 
          exact le_of_lt f_dist
        ·              
          exact le_of_lt hε_pos

      · unfold S_vert
        apply Real.sSup_le
        ·                                        
          intro r hr
          obtain ⟨τ, hτ, rfl⟩ := hr
                                                    
          have key_dist : dist (((z + h).re : ℂ) + Complex.I * τ) z < δ₁ := by
            rw [dist_eq]

            have h_eq : (((z + h).re : ℂ) + Complex.I * τ - z) = (h.re : ℝ) + Complex.I * (τ - z.im) := by
              apply Complex.ext_iff.mpr
              constructor
              · simp [Complex.add_re, Complex.sub_re]
              · simp [Complex.add_im, Complex.sub_im]
            rw [h_eq]
                                                             
            have τ_bound0 : |τ - z.im| ≤ |(z + h).im - z.im| := (abs_sub_le_of_mem_uIcc z.im (z + h).im τ hτ).1
            have im_diff_eq : |(z + h).im - z.im| = |h.im| := by
              simp [Complex.add_im, sub_eq_add_neg, add_assoc]
            have τ_bound : |τ - z.im| ≤ |h.im| := by simpa [im_diff_eq] using τ_bound0
                                                                 
            have vertical_bound : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| :=
              abs_vertical_core z h τ
            have sum_bound : |h.re| + |τ - z.im| ≤ |h.re| + |h.im| := by
              exact add_le_add_right τ_bound _
            have norm_bound := sum_abs_le_two_mul (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            have final_bound := two_norm_lt_of_norm_lt_half hδ₁_pos h_bound
            calc ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖
              _ ≤ |h.re| + |τ - z.im| := vertical_bound
              _ ≤ |h.re| + |h.im| := sum_bound
              _ ≤ (2 : ℝ) * ‖h‖ := norm_bound
              _ < δ₁ := final_bound
                                              
          have f_dist := hf_bound key_dist
          rw [dist_eq] at f_dist
                                 
          exact le_of_lt f_dist
        ·              
          exact le_of_lt hε_pos

lemma eventually_corner_and_sum_in_closedBall {z : ℂ} {R' : ℝ}
  (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    (z + h) ∈ Metric.closedBall (0 : ℂ) R' ∧
    (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) R' := by
                         
  have hρ_pos : 0 < R' - ‖z‖ := sub_pos.mpr hz
  have h_small : ∀ᶠ h in 𝓝 (0:ℂ), h ∈ Metric.ball (0 : ℂ) (R' - ‖z‖) :=
    Metric.ball_mem_nhds (0 : ℂ) hρ_pos
  refine h_small.mono ?_
  intro h hhball
  have hnorm_lt : ‖h‖ < R' - ‖z‖ := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hhball
                                              
  have hsum_lt : ‖z‖ + ‖h‖ < R' := by
    have htemp : ‖z‖ + ‖h‖ < ‖z‖ + (R' - ‖z‖) := add_lt_add_right hnorm_lt _
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htemp
  have hzph_le : ‖z + h‖ ≤ R' :=
    le_of_lt (lt_of_le_of_lt (norm_add_le _ _) hsum_lt)
  have hzph_mem : (z + h) ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hzph_le
                                                                       
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
                                                           
  have tri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    have := norm_add_le (w - z) z
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                                            
  let t : ℝ := (z + h).re
  have hwz_eq : w - z = (t : ℂ) + Complex.I * z.im - z := by
    simp [w, t, sub_eq_add_neg, add_assoc]
  have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| :=
    abs_horizontal_diff_eq_abs_real z t
  have t_sub_re : t - z.re = h.re := by
    simp [t, Complex.add_re, sub_eq_add_neg, add_assoc]
  have hwz_abs2 : ‖w - z‖ = |h.re| := by
    simpa [hwz_eq, t_sub_re] using eq_transform
  have hwz_le : ‖w - z‖ ≤ ‖h‖ := by
    simpa [hwz_abs2] using (Complex.abs_re_le_norm h)
  have hw_le'' : ‖w‖ ≤ ‖h‖ + ‖z‖ := by
    exact le_trans tri (add_le_add_left hwz_le _)
  have hw_lt : ‖w‖ < R' := by
    have : ‖h‖ + ‖z‖ < R' := by simpa [add_comm] using hsum_lt
    exact lt_of_le_of_lt hw_le'' this
  have hw_mem : w ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [w, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using (le_of_lt hw_lt)
  exact And.intro hzph_mem hw_mem

lemma limit_of_Err_ratio_is_zero
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
                                                 
  set g : ℂ → ℂ := fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h
                               
  have hS : Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) :=
    limit_of_S_is_zero (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz
                                        
  have h_upper : Tendsto (fun h => |(2 : ℝ) * S_max z h f|) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun x : ℝ => |(2 : ℝ) * x| :=
      (continuous_const.mul continuous_id).abs
    have h0 := hcont.tendsto (0 : ℝ)
    simpa only [Function.comp_def, mul_zero, abs_zero] using h0.comp hS
                                            
  have h_lower_nonneg : ∀ᶠ h in 𝓝 0, 0 ≤ ‖g h‖ :=
    Filter.Eventually.of_forall (fun _ => by simpa [g] using (norm_nonneg (g _)))
                                                                      
  let δ : ℝ := (R - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
    simpa [δ] using half_pos this
  let R' : ℝ := r1 + δ
  have hR'_pos : 0 < R' := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R'] using this
  have hR'_lt_R : R' < R := by
    have hδlt : δ < R - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R))
    have : r1 + δ < r1 + (R - r1) := add_lt_add_right hδlt r1
    simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                 
  have hz_le_r1 : ‖z‖ ≤ r1 := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hr1_le_R' : r1 ≤ R' := by
      have : 0 ≤ δ := le_of_lt hδ_pos
      simpa [R'] using (le_add_of_nonneg_right this : r1 ≤ r1 + δ)
    have : ‖z‖ ≤ R' := le_trans hz_le_r1 hr1_le_R'
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                                                                      
  have h_event : ∀ᶠ h in 𝓝 0, ‖g h‖ ≤ |(2 : ℝ) * S_max z h f| := by
                                                                                          
    have hcorner := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') (hz := by
                                                    
      have : ‖z‖ ≤ r1 := hz_le_r1
      exact lt_of_le_of_lt this (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos)))
    refine hcorner.mono ?_
    intro h hh
    have hzh' : z + h ∈ Metric.closedBall (0 : ℂ) R' := hh.1
    have hw' : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) R' := hh.2
    by_cases hh0 : h = 0
    · have : 0 ≤ |(2 : ℝ) * S_max z h f| := abs_nonneg _
      simp [g, hh0, div_zero, norm_zero]
    ·                                        
      have hb :=
        bound_on_Err_ratio (r1:=R') (R:=R) (R0:=R0)
          hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (h:=h) hz' hzh' hw' hh0
      have hb' : ‖g h‖ ≤ 2 * S_max z h f := by
        simpa [g, norm, Err] using hb
      exact le_trans hb' (le_abs_self ((2 : ℝ) * S_max z h f))
                                      
  have h_norm_tendsto : Tendsto (fun h => ‖g h‖) (𝓝 0) (𝓝 0) := by
    refine Filter.Tendsto.squeeze' tendsto_const_nhds h_upper h_lower_nonneg h_event
                                                         
  have h_dist_tendsto : Tendsto (fun h => dist (g h) 0) (𝓝 0) (𝓝 0) := by
    simpa [dist_eq_norm] using h_norm_tendsto
  simpa [g] using (tendsto_iff_dist_tendsto_zero).2 h_dist_tendsto

open Classical
                                                                                      
noncomputable def If_ext
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) : ℂ → ℂ :=
  fun w =>
    if h : w ∈ Metric.closedBall (0 : ℂ) r1 then
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, h⟩
    else
      0

lemma If_ext_eq_taxicab_of_mem {r1 R R0 : ℝ} (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) r1) :
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
      = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
  classical
  simp [If_ext, hw]

lemma If_taxicab_param_invariance {r1₁ r1₂ R R0 : ℝ}
    (hr1₁_pos : 0 < r1₁) (hr1₁_lt_R : r1₁ < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (hr1₂_pos : 0 < r1₂) (hr1₂_lt_R : r1₂ < R)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ}
    (hw₁ : w ∈ Metric.closedBall (0 : ℂ) r1₁)
    (hw₂ : w ∈ Metric.closedBall (0 : ℂ) r1₂) :
    If_taxicab hr1₁_pos hr1₁_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₁⟩
    = If_taxicab hr1₂_pos hr1₂_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₂⟩ := by

  simp [If_taxicab]

lemma eventually_decomposition_for_ext
  {R' R R0 : ℝ} (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  (z : ℂ) (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
    g (z + h) - g z = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
                                                                             
  have h_event := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') hz
  refine h_event.mono ?_
  intro h hh
             
  let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
                                                        
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                                           
  have hgzh : g (z + h)
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z + h) hh.1
  have hgz : g z
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z) hz'
                                                              
  have H :=
    If_diff_decomposition_final (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one (f:=f) (hf:=hf)
      (z:=z) (h:=h)
      (hz:=hz') (hzh:=hh.1) (hw:=hh.2)
                                               
  calc
    g (z + h) - g z
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩
          - If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
            simp [hgzh, hgz]
    _ = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
      simpa using H

lemma tendsto_Err_ratio_radius (R' R R0 : ℝ) (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z : ℂ} (hz : ‖z‖ < R') :
  Tendsto (fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
                                               
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
                                                 
  simpa using
    (limit_of_Err_ratio_is_zero (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (hz:=hz'))

lemma hasDerivWithinAt_congr_eqOn {f g : ℂ → ℂ} {s : Set ℂ} {z f' : ℂ}
  (hEq : Set.EqOn f g s) (hz : z ∈ s) :
  HasDerivWithinAt g f' s z → HasDerivWithinAt f f' s z := by
  intro hg
  have hfg : ∀ x ∈ s, f x = g x := fun x hx => hEq hx
  simpa using (HasDerivWithinAt.congr_of_mem (h := hg) (hs := hfg) (hx := hz))

lemma differentiableOn_of_hasDerivWithinAt {f : ℂ → ℂ} {s : Set ℂ} {F : ℂ → ℂ}
  (h : ∀ z ∈ s, HasDerivWithinAt f (F z) s z) : DifferentiableOn ℂ f s := by
  intro z hz
  exact (h z hz).differentiableWithinAt

lemma If_ext_agree_on_smallBall {r1 R' R R0 : ℝ}
  (hr1_pos : 0 < r1) (hR'_pos : 0 < R') (hr1_lt_R : r1 < R) (hR'_lt_R : R' < R) (hr1_lt_R' : r1 < R') (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
  Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
           (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
           (Metric.closedBall (0 : ℂ) r1) := by
  intro w hw
                                                                                
  have hw' : w ∈ Metric.closedBall (0 : ℂ) R' :=
    mem_closedBall_mono_radius (z:=w) (r:=r1) (R:=R') hw (le_of_lt hr1_lt_R')
                                                                  
  have hleft :
      If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=r1) (R:=R) (R0:=R0)
        hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw)
  have hright :
      If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0)
        hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw')
                                           
  have hparam :=
    If_taxicab_param_invariance (r1₁:=r1) (r1₂:=R') (R:=R) (R0:=R0)
      hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hR'_pos hR'_lt_R hf (w:=w) hw hw'
                     
  calc
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := hleft
    _ = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := hparam
    _ = If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w := by
          simpa using hright.symm

lemma hasDerivAt_of_local_decomposition' (g : ℂ → ℂ) (z F : ℂ)
  (Err_func : ℂ → ℂ)
  (hdecomp : ∀ᶠ h in 𝓝 (0:ℂ), g (z + h) - g z = F * h + Err_func h)
  (hErr : Tendsto (fun h => Err_func h / h) (𝓝 (0:ℂ)) (𝓝 (0:ℂ))) :
  HasDerivAt g F z := by
                                                             
  have hdecomp_within : ∀ᶠ h in 𝓝[≠] (0:ℂ), g (z + h) - g z = F * h + Err_func h :=
    (hdecomp.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ)))
                                                                 
  have h_ne0 : ∀ᶠ h in 𝓝[≠] (0:ℂ), h ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℂ)) (s := ({0}ᶜ : Set ℂ))] with h hh
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
                                                   
  have h_eq_slope : ∀ᶠ h in 𝓝[≠] (0:ℂ),
      h⁻¹ • (g (z + h) - g z) = F + Err_func h / h := by
    refine (hdecomp_within.and h_ne0).mono ?_
    intro h hh
    rcases hh with ⟨hEq, hne⟩
                                                   
    have H0 : h⁻¹ • (g (z + h) - g z) = h⁻¹ • (F * h + Err_func h) := by
      simpa using congrArg (fun x => h⁻¹ • x) hEq
                                     
    have h1 : h⁻¹ * (F * h) = F := by
      have hne' : h ≠ 0 := hne
      calc
        h⁻¹ * (F * h) = F * (h⁻¹ * h) := by
          ac_rfl
        _ = F * 1 := by simp [hne']
        _ = F := by simp
    have h2 : h⁻¹ * Err_func h = Err_func h / h := by
      simp [div_eq_mul_inv, mul_comm]
    calc
      h⁻¹ • (g (z + h) - g z)
          = h⁻¹ • (F * h + Err_func h) := H0
      _ = h⁻¹ * (F * h + Err_func h) := by simp [smul_eq_mul]
      _ = h⁻¹ * (F * h) + h⁻¹ * (Err_func h) := by simp [mul_add]
      _ = F + Err_func h / h := by simp [h1, h2]
                                        
  have hErr_within : Tendsto (fun h => Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) :=
    hErr.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
  have h_const : Tendsto (fun _ : ℂ => F) (𝓝[≠] (0:ℂ)) (𝓝 F) := tendsto_const_nhds
  have h_sum : Tendsto (fun h => F + Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (F + 0)) :=
    h_const.add hErr_within
  have h_target : Tendsto (fun h => h⁻¹ • (g (z + h) - g z)) (𝓝[≠] (0:ℂ)) (𝓝 F) := by
    have := (Filter.tendsto_congr' h_eq_slope).2 h_sum
    simpa [zero_add] using this
                                                             
  exact (hasDerivAt_iff_tendsto_slope_zero).2 h_target

lemma uniqueDiffWithinAt_convex_complex {s : Set ℂ} (hconv : Convex ℝ s)
    (hs : (interior s).Nonempty) {x : ℂ} (hx : x ∈ closure s) :
    UniqueDiffWithinAt ℂ s x := by
                                                                   
  have hR : UniqueDiffWithinAt ℝ s x :=
    uniqueDiffWithinAt_convex (E := ℂ) (conv := hconv) (hs := hs) (x := x) (hx := hx)
                                                       
  have dR : Dense ((Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) : Set ℂ) := by
    simpa using (hR.dense_tangentConeAt)
                                                                  
  have h_tc_subset : tangentConeAt ℝ s x ⊆ tangentConeAt ℂ s x :=
    tangentConeAt_mono_field
                                                                             
  set TC : Set ℂ := tangentConeAt ℂ s x
  set Sℂ : Submodule ℂ ℂ := Submodule.span ℂ TC
  set Sℝ : Submodule ℝ ℂ := Sℂ.restrictScalars ℝ
  have h_span_le : (Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) ≤ Sℝ := by
                                                   
    refine Submodule.span_le.mpr ?_
    intro v hv
    have hv' : v ∈ TC := h_tc_subset hv
    have : v ∈ Sℂ := Submodule.subset_span hv'
    simpa [Sℝ] using this
                                                                            
  have hsubset_sets :
      ((Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) : Set ℂ)
        ⊆ ((Sℂ : Submodule ℂ ℂ) : Set ℂ) := by
    intro z hz
    have hz' : z ∈ Sℝ := h_span_le hz
    simpa [Sℝ] using hz'
  have dC : Dense ((Sℂ : Submodule ℂ ℂ) : Set ℂ) := dR.mono hsubset_sets
                                 
  exact ⟨dC, hx⟩

lemma interior_closedBall_nonempty_of_pos {R : ℝ} (hR_pos : 0 < R) :
    (interior (Metric.closedBall (0 : ℂ) R)).Nonempty := by
                                                               
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hR_pos
                                                                  
  have hsub : Metric.ball (0 : ℂ) R ⊆ interior (Metric.closedBall (0 : ℂ) R) :=
    Metric.ball_subset_interior_closedBall
                                   
  exact ⟨0, hsub h0mem⟩

lemma mem_closure_of_mem_closedBall {R : ℝ} {z : ℂ}
  (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
  z ∈ closure (Metric.closedBall (0 : ℂ) R) := by
  exact subset_closure hz

lemma uniqueDiffWithinAt_closedBall_complex_of_mem {R : ℝ} {z : ℂ}
  (hR_pos : 0 < R) (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
  UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) R) z :=
by
                              
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) R) :=
    convex_closedBall (0 : ℂ) R
                                         
  have hnonempty : (interior (Metric.closedBall (0 : ℂ) R)).Nonempty :=
    interior_closedBall_nonempty_of_pos (R := R) hR_pos
                                                
  have hz_cl : z ∈ closure (Metric.closedBall (0 : ℂ) R) :=
    mem_closure_of_mem_closedBall (R := R) (z := z) hz
                                              
  exact uniqueDiffWithinAt_convex_complex hconv hnonempty hz_cl

lemma If_is_differentiable_on
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
    DifferentiableOn ℂ (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1)
    ∧
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      derivWithin (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1) z = f z := by
  set s : Set ℂ := Metric.closedBall (0 : ℂ) r1
  have hHasDerivWithinAt : ∀ z ∈ s,
      HasDerivWithinAt (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (f z) s z := by
    intro z hz
                                                        
    let δ : ℝ := (R - r1) / 2
    have hδ_pos : 0 < δ := by
      have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
      simpa [δ] using half_pos this
    let R' : ℝ := r1 + δ
    have hR'_pos : 0 < R' := by
      have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
      simpa [R'] using this
    have hR'_lt_R : R' < R := by
      have hδlt : δ < R - r1 := by
        have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
        simpa [δ] using (half_lt_self this)
      have : r1 + δ < r1 + (R - r1) := add_lt_add_right hδlt r1
      simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hr1_lt_R' : r1 < R' := by
      have : r1 < r1 + δ := by simpa [add_comm, add_left_comm, add_assoc, R', δ] using (lt_of_le_of_lt (le_of_eq rfl) (add_lt_add_right hδ_pos r1))
      simpa [R'] using this
                                       
    have hz_le_r1 : ‖z‖ ≤ r1 := by
      simpa [s, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
    have hz_lt_R' : ‖z‖ < R' := lt_of_le_of_lt hz_le_r1 (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos))
                                             
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
                                         
    have hdecomp := eventually_decomposition_for_ext (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf z hz_lt_R'
                                
    have hErr := tendsto_Err_ratio_radius (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf hz_lt_R'
                                                                
    have hDerivAt_g : HasDerivAt g (f z) z :=
      hasDerivAt_of_local_decomposition' (g := g) (z := z) (F := f z)
        (Err_func := fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h)
        (hdecomp := by
                                                                                          
          simpa [g] using hdecomp)
        (hErr := by
                                                                         
          simpa using hErr)
                                               
    have hWithin_g : HasDerivWithinAt g (f z) s z := hDerivAt_g.hasDerivWithinAt
                                                      
    have hEq : Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
                        (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
                        s :=
      If_ext_agree_on_smallBall (r1:=r1) (R':=R') (R:=R) (R0:=R0)
        hr1_pos hR'_pos hr1_lt_R hR'_lt_R hr1_lt_R' hR_lt_R0 hR0_lt_one hf
                                                  
    exact hasDerivWithinAt_congr_eqOn (f := If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
      (g := g) (s := s) (z := z) (f' := f z) hEq hz hWithin_g
                                 
  refine And.intro ?hdiff ?hderiv
  ·                                                                            
    apply differentiableOn_of_hasDerivWithinAt
    intro z hz
    exact hHasDerivWithinAt z hz
  ·                                   
    intro z hz
    have hUD : UniqueDiffWithinAt ℂ s z :=
      uniqueDiffWithinAt_closedBall_complex_of_mem (R := r1) hr1_pos (z := z) (hz := by simpa [s] using hz)
    have hD := hHasDerivWithinAt z hz
    simpa using hD.derivWithin hUD

open scoped Topology

theorem AnalyticOnNhd.mono_closedBall {B : ℂ → ℂ} {R : ℝ} (R' : ℝ)
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall 0 R)) (hR' : R' < R) :
    AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by

  exact hB.mono (Metric.closedBall_subset_closedBall (le_of_lt hR'))

lemma I_is_antiderivative
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J : ℂ → ℂ, AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) ∧
      J 0 = 0 ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z := by
  classical
                                           
  have hB_on_R' : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.mono_closedBall R' hB hR'_lt_R
  have hderiv_on_R' : AnalyticOnNhd ℂ (deriv B) (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.deriv hB_on_R'
  let L : ℂ → ℂ := fun z => deriv B z / B z
  have hL_on_R' : AnalyticOnNhd ℂ L (Metric.closedBall (0 : ℂ) R') := by
    simpa [L] using AnalyticOnNhd.div hderiv_on_R' hB_on_R' hB_ne_zero
                                      
  let δ : ℝ := (R' - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R' - r1 := sub_pos.mpr hr1_lt_R'
    simpa [δ] using half_pos this
  let R_mid : ℝ := r1 + δ
  have hR_mid_pos : 0 < R_mid := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R_mid] using this
  have hr1_lt_R_mid : r1 < R_mid := by
    have : 0 < δ := hδ_pos
    simpa [R_mid] using (lt_add_of_pos_right r1 this)
  have hR_mid_lt_R' : R_mid < R' := by
    have hδlt : δ < R' - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R'))
    have : r1 + δ < r1 + (R' - r1) := add_lt_add_right hδlt r1
    simpa [R_mid, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                                                        
  let J : ℂ → ℂ :=
    If_ext (r1 := R_mid) (R := R') (R0 := R) hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one L hL_on_R'

  have hIf :=
    (If_is_differentiable_on (r1 := R_mid) (R := R') (R0 := R)
      hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one (f := L) hL_on_R')
  have hDiffOn_mid : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) R_mid) := by
    simpa [J] using hIf.1
                                                         
  have hDiffOn_ball_R_mid : DifferentiableOn ℂ J (Metric.ball (0 : ℂ) R_mid) :=
    hDiffOn_mid.mono Metric.ball_subset_closedBall
                                                                       
  have hJ_analyticOnNhd : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) := by
    intro z hz
                                                               
    have hz_le : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
                                                                                
    exact (DifferentiableOn.analyticAt (s := Metric.ball (0 : ℂ) R_mid)
      (f := J) hDiffOn_ball_R_mid (Metric.isOpen_ball.mem_nhds hz_ball))
                
  have h0_in_mid : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R_mid := by
    simpa [Metric.mem_closedBall, dist_self] using (le_of_lt hR_mid_pos)
  have hJ0 : J 0 = 0 := by
    simp [J, If_ext, If_taxicab, h0_in_mid]
                                                           
  have hderiv_eq : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = L z := by
    intro z hz
                                        
    have hz_le : dist z (0 : ℂ) ≤ r1 := by simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
    have hz_cb_mid : z ∈ Metric.closedBall (0 : ℂ) R_mid := Metric.ball_subset_closedBall hz_ball
                                                                                      
    have h_cb_nhds : Metric.closedBall (0 : ℂ) R_mid ∈ 𝓝 z :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz_ball) Metric.ball_subset_closedBall
                                                                                     
    have hDW_eq_L : derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z = L z := by
      simpa [J] using hIf.2 z hz_cb_mid
                                                                                                    
    have hHasWithin : HasDerivWithinAt J (derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z)
        (Metric.closedBall (0 : ℂ) R_mid) z :=
      (hDiffOn_mid z hz_cb_mid).hasDerivWithinAt
    have hHasWithinL : HasDerivWithinAt J (L z) (Metric.closedBall (0 : ℂ) R_mid) z := by
      simpa [hDW_eq_L]
        using hHasWithin
                                                                           
    have hHasDerivAt : HasDerivAt J (L z) z :=
      HasDerivWithinAt.hasDerivAt hHasWithinL h_cb_nhds
                                           
    simpa using hHasDerivAt.deriv
                       
  refine ⟨J, hJ_analyticOnNhd, hJ0, ?_⟩
  intro z hz
  simpa [L] using hderiv_eq z hz

noncomputable def H_auxiliary
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (_hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    (J : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp (J z) / B z

lemma H_at_zero
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (_hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 = 1 / B 0 := by
  simp [H_auxiliary, hJ_zero]

lemma log_deriv_id
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (_hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z = deriv B z := by
  intro z hz
                                                   
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR'_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR'_le
    simpa using hzR''
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hJd := hJ_deriv z hz
  have hmult := congrArg (fun t => t * B z) hJd
  have hR2 : (deriv B z / B z) * B z = deriv B z * B z / B z := by
    simpa using (div_mul_eq_mul_div (deriv B z) (B z) (B z))
  have hmult' : deriv J z * B z = deriv B z * B z / B z := by
    simpa [hR2] using hmult
  have hdiv' : deriv B z * B z / B z = deriv B z := by
    field_simp [hBnz]
  calc
    deriv J z * B z = deriv B z * B z / B z := hmult'
    _ = deriv B z := by simpa using hdiv'

lemma log_deriv_identity
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z - deriv B z = 0 := by
  intro z hz
  have h_eq := log_deriv_id hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  rw [h_eq]
  simp

lemma H_derivative_quotient_rule
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z =
      (deriv (fun w => Complex.exp (J w)) z * B z - deriv B z * Complex.exp (J z)) / (B z)^2 := by
  intro z hz
                                        
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR_le
    simpa using hzR''
                                                      
  have hB_nz : B z ≠ 0 := hB_ne_zero z hzR
  have hB' : AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by
    apply AnalyticOnNhd.mono_closedBall R' hB
    assumption
  have hB_diff : DifferentiableAt ℂ B z := (hB' z hzR).differentiableAt
  have hJ_diff : DifferentiableAt ℂ J z := (hJ z hz).differentiableAt
  have hF_diff : DifferentiableAt ℂ (fun w => Complex.exp (J w)) z := hJ_diff.cexp
                                            
  have h := deriv_div (hc := hF_diff) (hd := hB_diff) (hx := hB_nz)
  unfold H_auxiliary
  simpa only [Pi.div_def, mul_comm] using h

lemma exp_I_derivative_chain_rule
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (_hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (fun w => Complex.exp (J w)) z = deriv J z * Complex.exp (J z) := by
  intro z hz
  have hJ_diff : DifferentiableAt ℂ J z := (hJ z hz).differentiableAt
  have hJ_has : HasDerivAt J (deriv J z) z := hJ_diff.hasDerivAt
  have hcomp := (Complex.hasDerivAt_exp (J z)).comp z hJ_has
                           
  simpa only [Function.comp_def, mul_comm] using hcomp.deriv

lemma H_derivative_calc
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z =
      (deriv J z * B z - deriv B z) * Complex.exp (J z) / (B z)^2 := by
  intro z hz
                                 
  have hquot := H_derivative_quotient_rule hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                            
  have hchain := exp_I_derivative_chain_rule hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                             
  rw [hquot, hchain]

  have h1 : deriv J z * Complex.exp (J z) * B z - deriv B z * Complex.exp (J z) =
           Complex.exp (J z) * (deriv J z * B z - deriv B z) := by ring
  rw [h1]

  ring

lemma H_derivative_is_zero
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 := by
  intro z hz
  have hcalc :=
    H_derivative_calc hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  have hident :=
    log_deriv_identity hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  simpa [hident] using hcalc

lemma zero_mem_closedBall_zero_radius {r1 : ℝ} (hr1 : 0 ≤ r1) : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r1 := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using hr1

lemma H_deriv_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 := by
  simpa using
    (H_derivative_is_zero hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv)

lemma H_auxiliary_differentiableOn_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    DifferentiableOn ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) :=
by
                                              
  have hsubset : Metric.closedBall (0 : ℂ) r1 ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    have hz' : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hle : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    have : dist z (0 : ℂ) ≤ R := le_trans hz' hle
    simpa [Metric.mem_closedBall] using this
                                                    
  have hJ_diff : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) r1) :=
    hJ.differentiableOn
  have hB_diff_r1 : DifferentiableOn ℂ B (Metric.closedBall (0 : ℂ) r1) :=
    (hB.differentiableOn).mono hsubset
                                                         
  have hExp_diff : DifferentiableOn ℂ Complex.exp (Set.univ : Set ℂ) :=
    (Complex.differentiable_exp.differentiableOn)
  have hExp_comp : DifferentiableOn ℂ (fun z => Complex.exp (J z)) (Metric.closedBall (0 : ℂ) r1) := by
    refine hExp_diff.comp hJ_diff ?_
    intro x hx; simp
                                                 
  have hB_ne_zero_r1 : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z ≠ 0 := by
    intro z hz; exact hB_ne_zero z (by
    have x : Metric.closedBall 0 r1 ⊆ Metric.closedBall 0 R' := Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_R')
    simp
    simp at hz
    linarith
    )
                                                
  have hdiv : DifferentiableOn ℂ (fun z => Complex.exp (J z) / B z)
      (Metric.closedBall (0 : ℂ) r1) :=
    hExp_comp.div hB_diff_r1 hB_ne_zero_r1
                                     
  unfold H_auxiliary
  exact hdiv

lemma hasDerivAt_H_auxiliary_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      HasDerivAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) 0 z := by
  intro z hz
                                               
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hR_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR_le
    simpa [Metric.mem_closedBall] using hzR''
  have hBnz : B z ≠ 0 := hB_ne_zero z (hzR)
                                               
  have hJ_anal : AnalyticAt ℂ J z := hJ z hz
  have hExp_diff_at_Jz : DifferentiableAt ℂ Complex.exp (J z) :=
    Complex.differentiableAt_exp
  have hc_diff : DifferentiableAt ℂ (fun w => Complex.exp (J w)) z :=
    hExp_diff_at_Jz.comp z hJ_anal.differentiableAt

  have hB' : AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by
    apply AnalyticOnNhd.mono_closedBall R' hB
    assumption
  have hd_diff : DifferentiableAt ℂ B z := (hB' z hzR).differentiableAt
                                                                      
  have hH_diff : DifferentiableAt ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z := by
    unfold H_auxiliary
    convert (preTransparency := .instances) hc_diff.div hd_diff hBnz using 1
    all_goals try with_reducible_and_instances rfl
  have hH_has : HasDerivAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z) z :=
    hH_diff.hasDerivAt
  have hderiv0 : deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 :=
    H_deriv_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  simpa [hderiv0] using hH_has

lemma fderivWithin_eq_zero_of_derivWithin_eq_zero {s : Set ℂ} {f : ℂ → ℂ} {x : ℂ}
    (_hdiff : DifferentiableWithinAt ℂ f s x)
    (hderiv : derivWithin f s x = 0) :
    fderivWithin ℂ f s x = 0 := by
  rw [← toSpanSingleton_derivWithin, hderiv]
  simp

lemma hasDerivWithinAt_of_hasDerivAt {f : ℂ → ℂ} {s : Set ℂ} {x : ℂ}
    (h : HasDerivAt f 0 x) : HasDerivWithinAt f 0 s x := by
  simpa using h.hasDerivWithinAt

lemma H_auxiliary_fderivWithin_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 :=
by
  intro z hz
                                                                                   
  have hHasAt :=
    hasDerivAt_H_auxiliary_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero
      hJ hJ_zero hJ_deriv z hz
  have hHasWithin :
      HasDerivWithinAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) 0
        (Metric.closedBall (0 : ℂ) r1) z :=
    hasDerivWithinAt_of_hasDerivAt hHasAt
                                         
  have hdiff : DifferentiableWithinAt ℂ
      (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) z :=
    hHasWithin.differentiableWithinAt
                                                                            
  classical
  have hderivWithin0 :
      derivWithin (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 := by
    by_cases hUDc : UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) r1) z
    · simpa using hHasWithin.derivWithin hUDc
    · simpa using
        (derivWithin_zero_of_not_uniqueDiffWithinAt
          (𝕜 := ℂ)
          (f := H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
          (s := Metric.closedBall (0 : ℂ) r1) (x := z) hUDc)
                                              
  exact fderivWithin_eq_zero_of_derivWithin_eq_zero hdiff hderivWithin0

lemma H_is_constant
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z =
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 := by
  intro z hz
                              
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) r1) := by
    simpa using (convex_closedBall (0 : ℂ) r1)
                                              
  have hdiff : DifferentiableOn ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) :=
    H_auxiliary_differentiableOn_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ
                                            
  have hfderiv0 : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) x = 0 :=
    H_auxiliary_fderivWithin_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv
                                 
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r1 :=
    zero_mem_closedBall_zero_radius (le_of_lt hr1_pos)
                                           
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      ‖fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
          (Metric.closedBall (0 : ℂ) r1) x‖ ≤ 0 := by
    intro x hx
    simp [hfderiv0 x hx]
  have hineq :=
    Convex.norm_image_sub_le_of_norm_fderivWithin_le (𝕜 := ℂ)
      (f := H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (s := Metric.closedBall (0 : ℂ) r1) (x := (0 : ℂ)) (y := z)
      hdiff hbound hs h0mem hz
  have hzero : H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z -
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 = 0 := by
    have : ‖H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z -
        H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0‖ ≤ 0 := by
      simpa using hineq
    simpa [norm_le_zero_iff] using this
  simpa [sub_eq_add_neg] using sub_eq_zero.mp hzero

lemma H_is_one
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z = 1 / B 0 := by
  intro z hz
  have hconst := H_is_constant hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  have h0 := H_at_zero hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv
  simpa [h0] using hconst

lemma analytic_log_exists
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z = B 0 * Complex.exp (J z) := by
  intro z hz
                                             
  have hH_const := H_is_one hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                         
  unfold H_auxiliary at hH_const
                                          
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    exact le_trans hzR' (by linarith)
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hR_pos : 0 < R := lt_trans (lt_trans hr1_pos hr1_lt_R') hR'_lt_R
  have hB0nz : B 0 ≠ 0 := hB_ne_zero 0 (by
    simp [Metric.closedBall, dist_zero_right]
    exact le_of_lt (by linarith))
                                                  
  have heq : Complex.exp (J z) * B 0 = B z := by
    field_simp [hBnz, hB0nz] at hH_const
    exact hH_const
                                              
  rw [← heq, mul_comm]

lemma modulus_of_exp_I
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (_hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (_hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (Complex.exp (J z)) = Real.exp (Complex.re (J z)) := by
  intro z hz
  exact Complex.norm_exp (J z)

lemma modulus_of_B_product_form
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * norm (Complex.exp (J z)) := by
  intro z hz
  have hBform := analytic_log_exists hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                          
  simpa [norm_mul] using (congrArg norm hBform)

lemma modulus_of_exp_log
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * Real.exp (Complex.re (J z)) := by
  intro z hz
  rw [modulus_of_B_product_form hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]
  rw [modulus_of_exp_I hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]

lemma log_modulus_as_sum
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) =
      Real.log (norm (B 0)) + Real.log (Real.exp (Complex.re (J z))) := by
  intro z hz
                                                     
  have h_eq := modulus_of_exp_log hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                                         
  rw [h_eq, Real.log_mul]
  ·                       
                                                                            
    simp
    apply hB_ne_zero
                                           
    rw [Metric.mem_closedBall, dist_self]
    linarith
  ·                                        
    exact Real.exp_ne_zero _

lemma real_log_of_modulus_difference
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J z) := by
  intro z hz
                                     
  have h_sum := log_modulus_as_sum hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
                                    
  rw [h_sum]
                                                                       
  rw [Real.log_exp]
  ring

theorem log_of_analytic
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J_B : ℂ → ℂ,
      AnalyticOnNhd ℂ J_B (Metric.closedBall (0 : ℂ) r1) ∧
      J_B 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J_B z = deriv B z / B z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1,
        Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J_B z)) := by
  have hB_ne_zero_R' : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0 := hB_ne_zero
  obtain ⟨J_B, hJ, hJ0, hJderiv⟩ :=
    I_is_antiderivative hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero_R'
  refine ⟨J_B, hJ, hJ0, hJderiv, ?_⟩
  intro z hz
  simpa using
    (real_log_of_modulus_difference hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ0 hJderiv z hz)

end Erdos970
end

section
-- module Solutions.OAIQ096_CM.Erdos970_PNT2_LogDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


def zerosetKfR (R : ℝ) (_hR : 0 < R) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0}

open Filter Metric _root_.Set Bornology Function

open Classical

lemma lem_frho_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    f ρ = 0 := h_rho_in_KfR1.2

lemma lem_m_rho_is_nat (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≠ ⊤ := by
  intro ρ h_rho_in_KfR1
                                           
  have hρ_closed_R1 : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
                                    
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
                       
  have hρ_ball1 : ρ ∈ Metric.ball (0 : ℂ) 1 := by
    have hdist_le : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_closed_R1)
    have hdist_lt : dist ρ (0 : ℂ) < 1 := by linarith
    simpa [Metric.mem_ball] using hdist_lt
                       
  have hf_at_ρ : AnalyticAt ℂ f ρ := by
                                      
    have hsubset : Metric.closedBall (0 : ℂ) R1 ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)
    have hρ_closed1 : ρ ∈ Metric.closedBall (0 : ℂ) 1 := hsubset hρ_closed_R1
    exact h_f_analytic ρ hρ_closed1
                                                    
  by_contra htop
                                                           
  have h_eventually_zero : ∀ᶠ z in nhds ρ, f z = 0 := by
    have h_equiv : (analyticOrderAt f ρ = ⊤ ↔ ∀ᶠ z in nhds ρ, f z = 0) := by
      simp [analyticOrderAt, hf_at_ρ]
    exact h_equiv.mp (by simpa using htop)
                                                     
  have hf_on_ball : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      (Metric.ball_subset_closedBall : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1) hz
    exact h_f_analytic z hz'
                                  
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) :=
    (Metric.isConnected_ball (by exact (zero_lt_one : (0 : ℝ) < 1))).isPreconnected
                                                  
  have h_eqOn_zero : Set.EqOn f 0 (Metric.ball (0 : ℂ) 1) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf_on_ball h_preconn hρ_ball1
      h_eventually_zero
                                 
  have h0_in_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball]
  have : f 0 = 0 := by
    have h := h_eqOn_zero h0_in_ball
    simpa [Pi.zero_apply] using h
  exact h_f_nonzero_at_zero this

lemma analyticOrderAt_ge_one_of_zero (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) (hz : f z = 0) (hfinite : analyticOrderAt f z ≠ ⊤) : analyticOrderAt f z ≥ 1 := by
                                                                 
  have h_order_ne_zero : analyticOrderAt f z ≠ 0 := by
    intro h_order_zero
                                                              
    have h_f_ne_zero : f z ≠ 0 := by
      rw [← AnalyticAt.analyticOrderAt_eq_zero hf]
      exact h_order_zero
                                    
    exact h_f_ne_zero hz
                                                                      
  cases' h : analyticOrderAt f z with n
  ·                                 
                               
    rw [h] at hfinite
    exact False.elim (hfinite rfl)
  ·                                                 

    rw [h] at h_order_ne_zero
    have n_ne_zero : n ≠ 0 := by
      intro n_zero
      rw [n_zero, Nat.cast_zero] at h_order_ne_zero
      exact h_order_ne_zero rfl
                                 
    have n_ge_one : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr n_ne_zero
                            
    exact Nat.cast_le.mpr n_ge_one

lemma lem_m_rho_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≥ 1 := by
  intro ρ h_rho_in_KfR1
                                                     
  have h_f_rho_zero : f ρ = 0 := lem_frho_zero R R1 hR1_pos hR1_lt_R f h_f_analytic ρ h_rho_in_KfR1
                                                        
  have h_order_finite : analyticOrderAt f ρ ≠ ⊤ := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 ρ h_rho_in_KfR1
                       
  have h_f_analytic_at_rho : AnalyticAt ℂ f ρ := by
    apply h_f_analytic
                                            
    have h_R1_lt_1 : R1 < 1 := by linarith
    have h_rho_in_R1 : ρ ∈ Metric.closedBall 0 R1 := h_rho_in_KfR1.1
    exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) h_rho_in_R1
                                                                          
  exact analyticOrderAt_ge_one_of_zero f ρ h_f_analytic_at_rho h_f_rho_zero h_order_finite

noncomputable def Cf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (_hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))                                                        
    (z : ℂ) : ℂ :=
  if hz : z ∈ zerosetKfR R1 (by linarith) f then
    h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase z), (z - ρ) ^ (analyticOrderAt f ρ).toNat
  else
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat

lemma lem_denomAnalAt (S : Finset ℂ) (n : ℂ → ℕ)
    (_hn_pos : ∀ s ∈ S, 0 < n s) (w : ℂ) (hw : w ∉ S) :
    AnalyticAt ℂ (fun z => ∏ s ∈ S, (z - s) ^ (n s)) w ∧
    (∏ s ∈ S, (w - s) ^ (n s)) ≠ 0 := by
  constructor
  ·                          
                                 
    let f : ℂ → ℂ → ℂ := fun s z => (z - s) ^ (n s)
    have h_each_analytic : ∀ s ∈ S, AnalyticAt ℂ (f s) w := by
      intro s hs
      simp only [f]
                                                               
      have h_sub : AnalyticAt ℂ (fun z => z - s) w := by
        exact AnalyticAt.sub analyticAt_id analyticAt_const
                                              
      exact h_sub.pow (n s)
    have h_prod := Finset.analyticAt_prod S h_each_analytic
    convert (preTransparency := .instances) h_prod using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext z; simp [f])
  ·                                
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    apply pow_ne_zero
                     
    intro h_eq
                                         
    have h_w_eq_s : w = s := by
      rwa [← sub_eq_zero]
                                              
    rw [h_w_eq_s] at hw
    exact hw hs

lemma lem_ratioAnalAt (w : ℂ) (R R1 : ℝ) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h w)
    (S : Finset ℂ) (_hS : ↑S ⊆ Metric.closedBall (0 : ℂ) R1) (n : ℂ → ℕ)
    (hn_pos : ∀ s ∈ S, 0 < n s)
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1 \ ↑S) :
    AnalyticAt ℂ (fun z => h z / ∏ s ∈ S, (z - s) ^ (n s)) w := by
  classical
                                                  
  have hden := lem_denomAnalAt (S := S) (n := n)
      (_hn_pos := hn_pos) (w := w)
      (hw := by simpa using hw.2)
                                                   
  exact AnalyticAt.div hh hden.1 hden.2

lemma lem_Cf_analytic_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) z := by

  have h_ratio_analytic : AnalyticAt ℂ (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) z := by
    apply lem_ratioAnalAt z R R1 hR1_lt_R hR_lt_1 f

    · apply h_f_analytic
      exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1

    · intro ρ hρ
      have h_mem : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
      exact h_mem.1

    · intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hs
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros

      cases' h_cases : analyticOrderAt f s with n
      ·                    
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      ·                               
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1)

    · constructor
      · exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1
      ·                                     
        intro h_z_in_finset
        have h_z_in_zeros : z ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp h_z_in_finset
        exact hz.2 h_z_in_zeros

  have h_eventually_eq : (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds z]
    (fun w => Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w) := by
                                                           
    have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2
    have h_open : IsOpen (Set.compl (zerosetKfR R1 (by linarith) f)) := h_finite_zeros.isClosed.isOpen_compl
    apply Filter.eventually_of_mem (h_open.mem_nhds hz_not_in)
    intro w hw_not_in_compl
                                                              
    have hw_not_in_zeros : w ∉ zerosetKfR R1 (by linarith) f := hw_not_in_compl
                                                         
    show f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat =
         Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w
                                                                          
    rw [Cf, dif_neg hw_not_in_zeros]

  exact h_ratio_analytic.congr h_eventually_eq

lemma lem_Cf_at_sigma_onK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z = σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  refine Filter.Eventually.of_forall ?_
  intro z hz
  subst hz
  simp [Cf, hσ]

lemma lem_Cf_at_sigma_offK0
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z /
      ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                        
  obtain ⟨h_σ_analytic, h_σ_ne_zero, h_f_eq⟩ := h_σ_spec σ hσ

  have h_σ_eventually_nonzero : ∀ᶠ z in nhds σ, h_σ σ z ≠ 0 := by
    have h_cont : ContinuousAt (h_σ σ) σ := h_σ_analytic.continuousAt
    exact h_cont.eventually_ne h_σ_ne_zero

  have h_f_eventually_nonzero : ∀ᶠ z in nhds σ, z ≠ σ → f z ≠ 0 := by
    filter_upwards [h_f_eq, h_σ_eventually_nonzero] with z h_fz_eq h_σz_nonzero
    intro hz_ne
    rw [h_fz_eq]
    apply mul_ne_zero
    · apply pow_ne_zero
      exact sub_ne_zero.mpr hz_ne
    · exact h_σz_nonzero

  have h_eventually_not_in_zeroset : ∀ᶠ z in nhds σ, z ≠ σ → z ∉ zerosetKfR R1 (by linarith) f := by
    filter_upwards [h_f_eventually_nonzero] with z h_fz_nonzero
    intro hz_ne hz_in_zeroset
    exact h_fz_nonzero hz_ne hz_in_zeroset.2

  filter_upwards [h_f_eq, h_eventually_not_in_zeroset] with z h_fz_eq h_not_in_zeroset
  intro hz_ne
                                                                    
  have hz_not_in_K : z ∉ zerosetKfR R1 (by linarith) f := h_not_in_zeroset hz_ne
                                                       
  unfold Cf
  simp [hz_not_in_K, h_fz_eq]

lemma lem_prod_no_sigma1
    {R R1 : ℝ} {hR1_pos : 0 < R1} {_hR1_lt_R : R1 < R} {_hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {_h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) (z : ℂ) :
    ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat =
    (z - σ) ^ (analyticOrderAt f σ).toNat *
    ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  classical
  have hmem : σ ∈ h_finite_zeros.toFinset :=
    (Set.Finite.mem_toFinset (hs := h_finite_zeros)).2 hσ
  simpa using
    (Finset.mul_prod_erase (s := h_finite_zeros.toFinset)
      (f := fun ρ => (z - ρ) ^ (analyticOrderAt f ρ).toNat) (a := σ) hmem).symm

lemma lem_Cf_at_sigma_offK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                            
  have h_cf_form := @lem_Cf_at_sigma_offK0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  filter_upwards [h_cf_form] with z h_cf_z
  intro hz_ne_sigma
                                              
  rw [h_cf_z hz_ne_sigma]
                                                 
  have h_prod_decomp := @lem_prod_no_sigma1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ z
                                                                            
  rw [h_prod_decomp]
                                                                  
  apply mul_div_mul_left
                       
  apply pow_ne_zero
  exact sub_ne_zero.mpr hz_ne_sigma

lemma lem_Cf_at_sigma
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ,
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                                 
  have h_on := @lem_Cf_at_sigma_onK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
  have h_off := @lem_Cf_at_sigma_offK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
                                      
  filter_upwards [h_on, h_off] with z hz_on hz_off
  by_cases h : z = σ
  ·                                                                
    have eq_result := hz_on h
                                                                  
    rw [h] at eq_result ⊢
    exact eq_result
  ·                                  
    exact hz_off h

lemma lem_h_ratio_anal
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (_hσ : σ ∈ zerosetKfR R1 (by linarith) f)
    (g : ℂ → ℂ) (hg_analytic : AnalyticAt ℂ g σ) :
    AnalyticAt ℂ
      (fun z => g z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (z - ρ) ^ (analyticOrderAt f ρ).toNat) σ := by
                                                                             
  have hden := lem_denomAnalAt (S := h_finite_zeros.toFinset.erase σ)
    (n := fun ρ => (analyticOrderAt f ρ).toNat)
    (_hn_pos := by
      intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := by
        have h_mem_erase : s ∈ h_finite_zeros.toFinset.erase σ := hs
        have h_mem_orig : s ∈ h_finite_zeros.toFinset := Finset.mem_of_mem_erase h_mem_erase
        exact h_finite_zeros.mem_toFinset.mp h_mem_orig
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      cases' h_cases : analyticOrderAt f s with n
      ·                    
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      ·                               
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1))
    (w := σ)
    (hw := by
      simp [Finset.mem_erase])
                                                   
  exact AnalyticAt.div hg_analytic hden.1 hden.2

lemma lem_Cf_analytic_at_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) σ := by
                                                                               
  have h_eventually_eq := @lem_Cf_at_sigma R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  obtain ⟨h_σ_analytic, _, _⟩ := h_σ_spec σ hσ
  have h_ratio_analytic := @lem_h_ratio_anal R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ (h_σ σ) h_σ_analytic

  have h_rev_eq : (fun z => h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds σ]
                  (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) := by
    filter_upwards [h_eventually_eq] with z h_z
    exact h_z.symm

  exact AnalyticAt.congr h_ratio_analytic h_rev_eq

lemma lem_f_nonzero_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {_hR1_lt_R : R1 < R} {_hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {_h_f_nonzero_at_zero : f 0 ≠ 0}
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    f z ≠ 0 := by
  exact fun h => hz.2 ⟨hz.1, h⟩

lemma lem_Cf_nonzero_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z ≠ 0 := by
                                                     
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2

  have h_cf_eq : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp [hz_not_in]

  rw [h_cf_eq]

  apply div_ne_zero

  · apply @lem_f_nonzero_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero z hz

  · apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
                                                     
    apply pow_ne_zero
                                  
    intro h_eq
                                                            
    have hz_eq_rho : z = ρ := by
      rwa [sub_eq_zero] at h_eq
                                                                             
    have hρ_in : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
    rw [hz_eq_rho] at hz_not_in
    exact hz_not_in hρ_in

lemma lem_Cf_nonzero_on_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ σ ≠ 0 := by
  have hnum : h_σ σ σ ≠ 0 := (h_σ_spec σ hσ).2.1
  have hden :
      (∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (σ - ρ) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro ρ hρmem
    have hρ_ne_σ : ρ ≠ σ := (Finset.mem_erase.mp hρmem).1
    have hσ_ne_ρ : σ ≠ ρ := hρ_ne_σ.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hσ_ne_ρ)
  have :
      h_σ σ σ /
          ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
            (σ - ρ) ^ (analyticOrderAt f ρ).toNat ≠
        0 := by
    exact div_ne_zero hnum hden
  simpa [Cf, hσ] using this

lemma lem_Cf_never_zero
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z ≠ 0 := by
                                                         
  by_cases h : z ∈ zerosetKfR R1 (by linarith) f
  ·                                           
    exact lem_Cf_nonzero_on_K h_finite_zeros h_σ h_σ_spec z h
  ·                                           
    have hz_diff : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f := ⟨hz, h⟩
    exact lem_Cf_nonzero_off_K h_finite_zeros h_σ h_σ_spec z hz_diff

noncomputable def Bf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) : ℂ :=
  Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z *
  ∏ ρ ∈ h_finite_zeros.toFinset,
    ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat

lemma lem_finset_prod_analyticAt {α : Type*} {S : Finset α} {g : α → ℂ → ℂ} (w : ℂ) :
  (∀ a ∈ S, AnalyticAt ℂ (g a) w) → AnalyticAt ℂ (fun z => ∏ a ∈ S, g a z) w := by
  intro h
  classical
  induction S using Finset.induction with
  | empty =>
                                                                
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | insert a s ha ih =>
                                                     
    simp only [Finset.prod_insert ha]
                                               
    apply AnalyticAt.fun_mul
    ·                        
      apply h
      exact Finset.mem_insert_self a s
    ·                                                           
      apply ih
      intro b hb
      apply h
      exact Finset.mem_insert_of_mem hb

theorem lem_Bf_is_analytic (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) := by
                                   
  intro z hz

  have h_blaschke_linear : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => (R : ℂ) - star ρ * w / (R : ℂ)) z := by
    intro ρ hρ
                                         
    have h_eq : (fun w : ℂ => (R : ℂ) - star ρ * w / (R : ℂ)) =
                (fun w : ℂ => (R : ℂ) + (-(star ρ) / (R : ℂ)) * w) := by
      funext w
      field_simp
      ring
    rw [h_eq]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)

  have h_powers : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    exact (h_blaschke_linear ρ hρ).fun_pow _

  have h_product : AnalyticAt ℂ (fun w => ∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
                                                                       
    apply lem_finset_prod_analyticAt z
    intro ρ hρ
    apply h_powers
    exact hρ
                                                             
  by_cases hz_in : z ∈ zerosetKfR R1 (by linarith) f
  ·                                                                                 
    have h_cf_at_sigma := @lem_Cf_analytic_at_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in
                                                                          
    exact AnalyticAt.fun_mul h_cf_at_sigma h_product

  ·                                                    
    have hz_in_compl : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f := by
      constructor
      · exact hz
      · exact hz_in
    have h_cf_off := @lem_Cf_analytic_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in_compl
    exact AnalyticAt.fun_mul h_cf_off h_product

variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)

lemma f_zero_ne_zero (h_f_zero : f 0 = 1) : f 0 ≠ 0 := by
  rw [h_f_zero]; simp

lemma Bf_is_analytic_on_disk
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) :=
    let hspec := h_σ_spec
    lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
      h_finite_zeros h_σ hspec

lemma lem_Bf_eq_prod_Cf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z, Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) *
      (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z) := by
  intro z
  rw [Bf]
  ring

lemma lem_num_prod_never_zero_all
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (_hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1,
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
  intro z hz
  apply Finset.prod_ne_zero_iff.mpr
  intro ρ hρ
  apply pow_ne_zero

  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    rwa [Set.Finite.mem_toFinset h_finite_zeros] at hρ
  have hρ_bound : ‖ρ‖ ≤ R1 := by
    rw [zerosetKfR] at hρ_mem; simp at hρ_mem; exact hρ_mem.1
  have hz_bound : ‖z‖ ≤ R1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz

  have hR_pos : (0 : ℝ) < R := lt_trans hR1_pos hR1_lt_R

  have key_positive : (0 : ℝ) < R - R1 * R1 / R := by
                                                  
    have h1 : R1 * R1 < R * R := by
      apply mul_self_lt_mul_self (le_of_lt hR1_pos) hR1_lt_R
    have h2 : R1 * R1 / R < R := by
      rw [div_lt_iff₀ hR_pos]
      exact h1
    linarith [h2]

  suffices h : (0 : ℝ) < ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ by
    exact norm_pos_iff.mp h

  have triangle_ineq : ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ ≥ ‖(R : ℂ)‖ - ‖star ρ * z / (R : ℂ)‖ :=
    norm_sub_norm_le _ _

  have R_norm_eq : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_of_nonneg (le_of_lt hR_pos)]

  have product_bound : ‖star ρ * z / (R : ℂ)‖ ≤ R1 * R1 / R := by
    rw [norm_div, norm_mul, norm_star, R_norm_eq]

    have mult_bound : ‖ρ‖ * ‖z‖ ≤ R1 * R1 := by
      exact mul_le_mul hρ_bound hz_bound (norm_nonneg _) (le_of_lt hR1_pos)
                                                                                
    have : ‖ρ‖ * ‖z‖ / R ≤ R1 * R1 / R := by
      exact div_le_div_of_nonneg_right mult_bound (le_of_lt hR_pos)
    exact this

  rw [R_norm_eq] at triangle_ineq
  linarith [triangle_ineq, product_bound, key_positive]

lemma Bf_never_zero
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1, Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z ≠ 0 := by
  intro z hz
                                                               
  rw [lem_Bf_eq_prod_Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec]
                                                                  
  apply mul_ne_zero
  ·                                                                                  
    exact lem_num_prod_never_zero_all R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec z hz
  ·                                                       
    exact lem_Cf_never_zero h_finite_zeros h_σ h_σ_spec z hz

noncomputable def Lf : ℂ → ℂ :=
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  Classical.choose (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
)

end Erdos970
end

section
-- module Solutions.OAIQ096_CM.Sobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance instCoeFunForallReal : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance instCoeRealComplex : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance instNeg : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance instHSMulReal : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

end CS
end

section
-- module Solutions.OAIQ096_CM.Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

section lemmas

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas
end

section
-- module Solutions.OAIQ096_CM.MeasureTheory_Function_LpSpace_Restrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict`

`L^p` extension-by-zero maps for restricted measures.

Mathlib provides the equivalence

`MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s)`

(`MeasureTheory.memLp_indicator_iff_restrict`). This file packages the corresponding map on `Lp`
spaces:

`Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ`,

given by extension-by-zero (via `Set.indicator`).

## Main definitions

- `MeasureTheory.Lp.extendByZeroₗ`
- `MeasureTheory.Lp.extendByZeroₗᵢ`
-/

namespace MeasureTheory

open scoped ENNReal

namespace Lp

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)

noncomputable def extendByZeroFun (f : Lp E p (μ.restrict s)) : Lp E p μ :=
  let hf : MemLp (fun x : α => f x) p (μ.restrict s) := Lp.memLp f
  let hfi : MemLp (s.indicator fun x : α => f x) p μ :=
    (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s) (f := fun x : α => f x) hs).2 hf
  hfi.toLp (s.indicator fun x : α => f x)

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
lemma extendByZeroFun_coe (f : Lp E p (μ.restrict s)) :
    extendByZeroFun (μ := μ) (p := p) (s := s) hs f =ᵐ[μ] s.indicator fun x : α => f x := by
  dsimp [extendByZeroFun]
  exact MemLp.coeFn_toLp _

/-- Extension-by-zero as a linear map `Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ`. -/
noncomputable def extendByZeroₗ : Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ where
  toFun := extendByZeroFun (μ := μ) (p := p) (s := s) hs
  map_add' f g := by
    classical
    -- Prove equality by comparing pointwise representatives.
    refine Lp.ext ?_
    have h_add_restrict :
        (fun x : α => (f + g) x) =ᵐ[μ.restrict s] fun x : α => f x + g x := by
      exact (Lp.coeFn_add (μ := μ.restrict s) f g)
    have h_add_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (f + g) x = f x + g x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_add_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (f + g)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs g
      , coeFn_add (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
          (extendByZeroFun (μ := μ) (p := p) (s := s) hs g)
      , h_add_on
      ] with x hfg hf hg hadd hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = (f + g) x := by simp [Set.indicator_of_mem, hx]
        _ = f x + g x := hsum'
        _ = s.indicator (fun x : α => f x) x + s.indicator (fun x : α => g x) x := by
            simp [Set.indicator_of_mem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            simp [hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
    ·
      have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            -- both summands are zero off `s`
            simp [Set.indicator_of_notMem, hx, hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
  map_smul' c f := by
    classical
    refine Lp.ext ?_
    have h_smul_restrict :
        (fun x : α => (c • f) x) =ᵐ[μ.restrict s] fun x : α => c • f x := by
      exact (Lp.coeFn_smul (μ := μ.restrict s) c f)
    have h_smul_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (c • f) x = c • f x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_smul_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (c • f)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , coeFn_smul c (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
      , h_smul_on
      ] with x hcf hf hsmul hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = (c • f) x := by simp [Set.indicator_of_mem, hx]
        _ = c • f x := hsum'
        _ = c • s.indicator (fun x : α => f x) x := by simp [Set.indicator_of_mem, hx]
        _ = c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by simp [hf]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := hsmul'
    ·
      have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
            have hf0 :
                extendByZeroFun (μ := μ) (p := p) (s := s) hs f x = 0 := by
              simpa [Set.indicator_of_notMem, hx] using hf
            have hcx :
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x = 0 := by
              calc
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x =
                    c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by
                      simpa [Pi.smul_apply] using hsmul
                _ = 0 := by simp [hf0]
            simpa using hcx.symm

/-- Extension-by-zero as a linear isometry. -/
noncomputable def extendByZeroₗᵢ : Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ where
  toLinearMap := extendByZeroₗ (μ := μ) (p := p) (s := s) hs
  norm_map' f := by
    classical
    -- Unfold into `MemLp.toLp` and reduce to `eLpNorm_indicator_eq_eLpNorm_restrict`.
    have hfi :
        MemLp (s.indicator fun x : α => f x) p μ :=
      (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs).2 (Lp.memLp f)
    -- Norm in the codomain is the `eLpNorm` of the indicator.
    have hnorm_out :
        ‖extendByZeroₗ (μ := μ) (p := p) (s := s) hs f‖ =
          ENNReal.toReal (eLpNorm (s.indicator fun x : α => f x) p μ) := by
      dsimp [extendByZeroₗ, extendByZeroFun]
      simp [norm_toLp (f := s.indicator (fun x : α => f x)) hfi]
    -- Rewrite the `eLpNorm` of the indicator as a restricted `eLpNorm`.
    have hnorm_restrict :
        eLpNorm (s.indicator fun x : α => f x) p μ =
          eLpNorm (fun x : α => f x) p (μ.restrict s) := by
      simpa using (eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs)
    -- Combine with the definition of the `Lp` norm on the restricted space.
    simp [hnorm_out, hnorm_restrict, norm_def]

lemma extendByZeroₗᵢ_ae_eq (f : Lp E p (μ.restrict s)) :
    ((extendByZeroₗᵢ (μ := μ) (p := p) (s := s) hs) f : α → E) =ᵐ[μ]
      s.indicator fun x : α => f x := by
  -- Unfold to the underlying `extendByZeroFun` and use the defining AE equality.
  simpa [extendByZeroₗᵢ, extendByZeroₗ] using
    (extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f)

end

end Lp

end MeasureTheory
end


