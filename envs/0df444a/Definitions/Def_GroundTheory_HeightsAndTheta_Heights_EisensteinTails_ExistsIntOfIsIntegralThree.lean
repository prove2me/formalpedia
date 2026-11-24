-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EisensteinTails_ExistsIntOfIsIntegralThree
-- name    : GroundTheory_HeightsAndTheta_Heights_EisensteinTails_ExistsIntOfIsIntegralThree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:10.584401+00:00
-- url     : https://prove2.me/theorems/f5b165d1-e441-48a5-979b-af294d34fc62
-- title:
--   Exists Int Of Is Integral Three
-- statement:
--   Definitions and structural lemmas for Exists Int Of Is Integral Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EisensteinTails/ExistsIntOfIsIntegralThree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex NumberField Filter Topology
open UpperHalfPlane hiding I
open NumberField.ComplexEmbedding
open scoped Real nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum
instance neZero_of_prime (d : ℕ) [Fact d.Prime] : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
def chi (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
def Lval (d : ℕ) [Fact d.Prime] (s : ℂ) : ℂ := DirichletCharacter.LFunction (chi d) s
def Lc (d : ℕ) [Fact d.Prime] : ℂ := deriv (Lval d) 1 / Lval d 1
def L0 (d : ℕ) [Fact d.Prime] : ℂ := deriv (Lval d) 0 / Lval d 0
def abelian₂ (d : ℕ) [Fact d.Prime] (s : ℂ) : ℂ :=
  ((d : ℂ) / π) ^ ((s + 1) / 2) * Gamma ((s + 1) / 2) * Lval d s
def phi (τ : ℍ) : ℝ := Real.log (4 * π * τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 4)
def sqrtNeg (d : ℕ) : ℂ := I * (Real.sqrt d : ℂ)
def Kfield (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {sqrtNeg d}
abbrev K (d : ℕ) : Type := ↥(Kfield d)
theorem sqrtNeg_sq (d : ℕ) : sqrtNeg d ^ 2 = -(d : ℂ) := by
  rw [sqrtNeg, mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring
theorem isIntegral_sqrtNeg (d : ℕ) : IsIntegral ℚ (sqrtNeg d) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simp [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, sqrtNeg_sq]
instance (d : ℕ) : NumberField (K d) where
  to_finiteDimensional := IntermediateField.adjoin.finiteDimensional (isIntegral_sqrtNeg d)
def IsTauOf (d : ℕ) (C : ClassGroup (𝓞 (K d))) (τ : ℍ) : Prop :=
  ∃ J : (FractionalIdeal (𝓞 (K d))⁰ (K d))ˣ, ClassGroup.mk (K d) J = C ∧
    ∃ c : ℂ, c ≠ 0 ∧ (algebraMap (K d) ℂ) '' ((J : FractionalIdeal (𝓞 (K d))⁰ (K d)) : Set (K d)) =
      {z : ℂ | ∃ m n : ℤ, z = c * ((m : ℂ) + (n : ℂ) * (τ : ℂ))}
open scoped Classical in

def phiClass (d : ℕ) (C : ClassGroup (𝓞 (K d))) : ℝ :=
  if h : ∃ τ, IsTauOf d C τ then phi h.choose else 0
def A1 (d : ℕ) : ℝ :=
  (1 / (classNumber (K d) : ℝ)) * ∑ C : ClassGroup (𝓞 (K d)), phiClass d C
def partialZeta (d : ℕ) (C : ClassGroup (𝓞 (K d))) (s : ℂ) : ℂ :=
  ∑' a : {a : (Ideal (𝓞 (K d)))⁰ // ClassGroup.mk0 a = C},
    ((Ideal.absNorm (a.1 : Ideal (𝓞 (K d))) : ℕ) : ℂ) ^ (-s)
def eisTerm (τ : ℍ) (s : ℂ) (p : ℤ × ℤ) : ℂ :=
  (τ.im : ℂ) ^ s / ((‖(p.1 : ℂ) * (τ : ℂ) + p.2‖ : ℝ) : ℂ) ^ (2 * s)
def eis (τ : ℍ) (s : ℂ) : ℂ := ∑' p : {p : ℤ × ℤ // p ≠ 0}, eisTerm τ s p
def expTwoPiI (x : ℝ) : ℂ := cexp (2 * π * I * x)
def rowSum (m : ℤ) (τ : ℍ) (s : ℂ) : ℂ :=
  ∑' n : ℤ, ((‖(m : ℂ) * (τ : ℂ) + n‖ : ℝ) : ℂ) ^ (-2 * s)
def freqIntegral (k : ℤ) (Y : ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, expTwoPiI (-(k * t)) * ((t ^ 2 + Y ^ 2 : ℝ) : ℂ) ^ (-s)
def eisRest (τ : ℍ) (s : ℂ) : ℂ :=
  (τ.im : ℂ) ^ s * ∑' m : {m : ℤ // m ≠ 0}, ∑' k : {k : ℤ // k ≠ 0},
    expTwoPiI (k * m * τ.re) * freqIntegral k (|(m : ℝ)| * τ.im) s
def qpar (τ : ℍ) : ℂ := cexp (2 * π * I * (τ : ℂ))
section Hermitian
@[instance_reducible]
def corePi {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ c, AddCommGroup (V c)] [∀ c, Module ℂ (V c)]
    (h : ∀ c, InnerProductSpace.Core ℂ (V c)) : InnerProductSpace.Core ℂ (∀ c, V c) where
  inner x y := ∑ c, (h c).inner (x c) (y c)
  conj_inner_symm x y := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ ↦ (h c).conj_inner_symm _ _
  re_inner_nonneg x := by
    rw [map_sum]
    exact Finset.sum_nonneg fun c _ ↦ (h c).re_inner_nonneg _
  add_left x y z := by
    simp only [Pi.add_apply, (h _).add_left, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [Pi.smul_apply, (h _).smul_left, Finset.mul_sum]
  definite x hx := by
    have hre : ∑ c, ((h c).inner (x c) (x c)).re = 0 := by
      rw [← Complex.re_sum]
      exact congrArg Complex.re hx
    funext c
    refine core_eq_zero_of_re (h c) _ ?_
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun c _ ↦ (h c).re_inner_nonneg (x c))).1 hre c
      (Finset.mem_univ c)
theorem corePi_inner {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ c, AddCommGroup (V c)]
    [∀ c, Module ℂ (V c)] (h : ∀ c, InnerProductSpace.Core ℂ (V c)) (x y : ∀ c, V c) :
    (corePi h).inner x y = ∑ c, (h c).inner (x c) (y c) := rfl
variable {K' : Type*} [Field K']
def fibrePi (σ : K' →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → Type*)
    [∀ c, AddCommGroup (E c)] [∀ c, Module (𝓞 K') (E c)] :
    Fibre σ (∀ c, E c) ≃ₗ[ℂ] ∀ c, Fibre σ (E c) :=
  (TensorProduct.piRight (𝓞 K') (ComplexAt σ) (ComplexAt σ) E).restrictScalars ℂ
theorem fibrePi_conjMap (σ : K' →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → Type*)
    [∀ c, AddCommGroup (E c)] [∀ c, Module (𝓞 K') (E c)] (x : Fibre σ (∀ c, E c)) :
    fibrePi (conjugate σ) E (conjMap σ (∀ c, E c) x) =
      fun c ↦ conjMap σ (E c) (fibrePi σ E x c) := by
  induction x using TensorProduct.induction_on with
  | zero => funext c; simp only [map_zero, Pi.zero_apply]
  | tmul z v => rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    funext c
    simp only [Pi.add_apply, map_add]
instance projective_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ c, AddCommGroup (E c)] [∀ c, Module R (E c)]
    [∀ c, Module.Projective R (E c)] : Module.Projective R (∀ c, E c) :=
  Module.Projective.of_equiv DFinsupp.linearEquivFunOnFintype
variable [NumberField K']
def piMetric {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ c, AddCommGroup (E c)]
    [∀ c, Module (𝓞 K') (E c)] [∀ c, Module.Finite (𝓞 K') (E c)]
    [∀ c, Module.Projective (𝓞 K') (E c)] (h : ∀ c, HermitianMetric K' (E c)) :
    HermitianMetric K' (∀ c, E c) where
  form σ := coreComap (corePi fun c ↦ (h c).form σ) (fibrePi σ E).toLinearMap (fibrePi σ E).injective
  form_conj σ x y := by
    simp only [coreComap_inner, LinearEquiv.coe_coe, fibrePi_conjMap, corePi_inner, map_sum,
      (h _).form_conj]
def formScale {E : Type*} [AddCommGroup E] [Module (𝓞 K') E] [Module.Finite (𝓞 K') E]
    [Module.Projective (𝓞 K') E] (h : HermitianMetric K' E) (t : ℝ) (ht : 0 < t) :
    HermitianMetric K' E :=
  h.scale (Real.sqrt t) (Real.sqrt_pos.2 ht)
theorem volFrac_pos {ι : Type*} [Fintype ι] {vol : ι → ℝ} (hvol : ∀ c, 0 < vol c) (c : ι) :
    0 < vol c / ∑ c', vol c' :=
  div_pos (hvol c) (lt_of_lt_of_le (hvol c)
    (Finset.single_le_sum (fun i _ ↦ (hvol i).le) (Finset.mem_univ c)))
end Hermitian
def ChiFacts.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    (chi d).IsPrimitive ∧ chi d (-1) = -1 ∧ ∀ a : ZMod d, (chi d a).im = 0
def CompletedForm.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    (∀ s : ℂ, (∀ n : ℕ, s ≠ -(2 * n + 1)) →
      DirichletCharacter.completedLFunction (chi d) s =
        (π : ℂ) ^ (-(s + 1) / 2) * Gamma ((s + 1) / 2) * Lval d s) ∧
    ∃ ε : ℂ, ε ≠ 0 ∧ ∀ s : ℂ, (∀ n : ℕ, s ≠ -(2 * n + 1)) → (∀ n : ℕ, 1 - s ≠ -(2 * n + 1)) →
      abelian₂ d (1 - s) = ε * abelian₂ d s
def LNonzero.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 → Lval d 1 ≠ 0 ∧ Lval d 0 ≠ 0
def LogDerivRelation.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    (1 / 2 : ℂ) * (Real.log (d / π) : ℂ) + (1 / 2 : ℂ) * digamma (1 / 2) + L0 d =
      -((1 / 2 : ℂ) * (Real.log (d / π) : ℂ) + (1 / 2 : ℂ) * digamma 1 + Lc d)
def LeafFE.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    L0 d = -Lc d - (Real.log (d / π) : ℂ) + (Real.eulerMascheroniConstant : ℂ) + (Real.log 2 : ℂ)
def PhiInvariant.Statement : Prop :=
  ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ), phi (g • τ) = phi τ
def TauExists.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 → ∀ C : ClassGroup (𝓞 (K d)),
    (∃ τ : ℍ, IsTauOf d C τ) ∧ ∀ τ τ' : ℍ, IsTauOf d C τ → IsTauOf d C τ' → phi τ = phi τ'
def EisSummable.Statement : Prop :=
  ∀ τ : ℍ,
    (∀ s : ℂ, 1 < s.re → Summable fun p : {p : ℤ × ℤ // p ≠ 0} ↦ ‖eisTerm τ s p‖) ∧
    (∀ S : Set ℂ, IsCompact S → S ⊆ {s : ℂ | 1 < s.re} →
      ∃ u : {p : ℤ × ℤ // p ≠ 0} → ℝ, Summable u ∧ ∀ s ∈ S, ∀ p : {p : ℤ × ℤ // p ≠ 0}, ‖eisTerm τ s p‖ ≤ u p) ∧
    AnalyticOnNhd ℂ (eis τ) {s : ℂ | 1 < s.re}
def EisRows.Statement : Prop :=
  ∀ (τ : ℍ) (s : ℂ), 1 < s.re →
    eis τ s = 2 * riemannZeta (2 * s) * (τ.im : ℂ) ^ s +
      (τ.im : ℂ) ^ s * ∑' m : {m : ℤ // m ≠ 0}, rowSum m τ s
def RowPoisson.Statement : Prop :=
  ∀ (τ : ℍ) (s : ℂ), 1 < s.re → ∀ m : ℤ, m ≠ 0 →
    rowSum m τ s = ∑' k : ℤ, expTwoPiI (k * m * τ.re) * freqIntegral k (|(m : ℝ)| * τ.im) s
def ZeroFrequency.Statement : Prop :=
  ∀ (Y : ℝ), 0 < Y → ∀ s : ℂ, 1 / 2 < s.re →
    freqIntegral 0 Y s = (Real.sqrt π : ℂ) * Gamma (s - 1 / 2) / Gamma s * (Y : ℂ) ^ (1 - 2 * s)
def NonzeroFrequencyBound.Statement : Prop :=
  (∀ k : ℤ, k ≠ 0 → ∀ Y : ℝ, 0 < Y →
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 1 / 2 < s.re → F s = freqIntegral k Y s) ∧
  ∀ y₀ : ℝ, 0 < y₀ → ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ s ∈ Metric.ball (1 : ℂ) r, ∀ k : ℤ, k ≠ 0 →
    ∀ Y : ℝ, y₀ ≤ Y → ‖freqIntegral k Y s‖ ≤ C * Real.exp (-(π * |(k : ℝ)| * Y)) * Y ^ (1 - 2 * s.re)
def NonzeroFrequencyValue.Statement : Prop :=
  ∀ k : ℤ, k ≠ 0 → ∀ Y : ℝ, 0 < Y →
    freqIntegral k Y 1 = ((π / Y * Real.exp (-(2 * π * |(k : ℝ)| * Y)) : ℝ) : ℂ)
def EisExpansion.Statement : Prop :=
  ∀ τ : ℍ,
    (∀ s : ℂ, 1 < s.re →
      eis τ s = 2 * riemannZeta (2 * s) * (τ.im : ℂ) ^ s +
        2 * (Real.sqrt π : ℂ) * Gamma (s - 1 / 2) / Gamma s * riemannZeta (2 * s - 1) *
          (τ.im : ℂ) ^ (1 - s) + eisRest τ s) ∧
    ∃ U : Set ℂ, IsOpen U ∧ (1 : ℂ) ∈ U ∧ AnalyticOnNhd ℂ (eisRest τ) U
def BValue.Statement : Prop :=
  ∀ τ : ℍ,
    eisRest τ 1 = ((-(2 * π) * Real.log (‖∏' n : ℕ, (1 - qpar τ ^ (n + 1))‖ ^ 2) : ℝ) : ℂ)
def KroneckerFirstLimit.Statement : Prop :=
  ∀ τ : ℍ, ∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧
    (∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → F s = eis τ s - π / (s - 1)) ∧
    F 1 = ((2 * π * (Real.eulerMascheroniConstant - Real.log 2 -
      Real.log (Real.sqrt τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 2)) : ℝ) : ℂ)
def PartialZetaEis.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 → ∀ (C : ClassGroup (𝓞 (K d))) (τ : ℍ), IsTauOf d C⁻¹ τ →
    ∀ s : ℂ, 1 < s.re →
      partialZeta d C s =
        (1 / (Units.torsionOrder (K d) : ℂ)) * ((2 / Real.sqrt d : ℝ) : ℂ) ^ s * eis τ s
def ZetaFactor.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    (∀ s : ℂ, 1 < s.re → dedekindZeta (K d) s = riemannZeta s * Lval d s) ∧
    Tendsto (fun s : ℂ ↦ dedekindZeta (K d) s - Lval d 1 / (s - 1)) (𝓝[{s : ℂ | 1 < s.re}] 1)
      (𝓝 (Lval d 1 * ((Real.eulerMascheroniConstant : ℂ) + Lc d)))
def ClassNumberL.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    ((2 * π * classNumber (K d) / (Units.torsionOrder (K d) * Real.sqrt d) : ℝ) : ℂ) = Lval d 1
def ClassMeanIdentity.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    (A1 d : ℂ) = (Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * π / Real.sqrt d) : ℂ) - Lc d
def LeafKL.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 → (A1 d : ℂ) = L0 d + (1 / 2 : ℂ) * (Real.log d : ℂ)
def OrthogonalDegree.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ c, AddCommGroup (E c)] [∀ c, Module (𝓞 F) (E c)] [∀ c, Module.Finite (𝓞 F) (E c)]
    [∀ c, Module.Projective (𝓞 F) (E c)] (h : ∀ c, HermitianMetric F (E c)),
    arithDegree (piMetric h) = ∑ c, arithDegree (h c)
def ScaleDegree.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (E : Type) [AddCommGroup E] [Module (𝓞 F) E]
    [Module.Finite (𝓞 F) E] [Module.Projective (𝓞 F) E] (h : HermitianMetric F E) (t : ℝ)
    (ht : 0 < t),
    arithDegree (formScale h t ht) =
      arithDegree h - (1 / 2) * Module.finrank ℚ F * Module.finrank (𝓞 F) E * Real.log t
def SumWeights.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ c, AddCommGroup (E c)] [∀ c, Module (𝓞 F) (E c)] [∀ c, Module.Finite (𝓞 F) (E c)]
    [∀ c, Module.Projective (𝓞 F) (E c)] (h : ∀ c, HermitianMetric F (E c)) (vol : ι → ℝ)
    (hvol : ∀ c, 0 < vol c),
    arithDegree (piMetric fun c ↦ formScale (h c) (vol c / ∑ c', vol c') (volFrac_pos hvol c)) /
        Module.finrank ℚ F =
      ∑ c, arithDegree (h c) / Module.finrank ℚ F +
        (1 / 2) * ∑ c, Module.finrank (𝓞 F) (E c) * Real.log ((∑ c', vol c') / vol c) ∧
    ∑ c, arithDegree (h c) / Module.finrank ℚ F ≤
      arithDegree (piMetric fun c ↦ formScale (h c) (vol c / ∑ c', vol c') (volFrac_pos hvol c)) /
        Module.finrank ℚ F
def MertensUpper.Statement : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log x + C
section Inhabitants
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩
example : (Nat.Prime 3 ∧ 3 % 4 = 3) ∧ (Nat.Prime 7 ∧ 7 % 4 = 3) :=
  ⟨⟨Nat.prime_three, rfl⟩, ⟨by norm_num, rfl⟩⟩
example : NumberField (K 3) := inferInstance
example : NumberField (K 7) := inferInstance
theorem chi_neg_one_of_mod_four (d : ℕ) [Fact d.Prime] (hd : d % 4 = 3) : chi d (-1) = -1 := by
  have hsq : ¬ IsSquare (-1 : ZMod d) := by
    rw [FiniteField.isSquare_neg_one_iff, ZMod.card]
    omega
  have h := quadraticChar_neg_one_iff_not_isSquare.2 hsq
  simp only [chi, MulChar.ringHomComp_apply, h, map_neg, map_one]
theorem chi_isPrimitive_of_mod_four (d : ℕ) [hp : Fact d.Prime] (hd : d % 4 = 3) :
    (chi d).IsPrimitive := by
  have hne : chi d ≠ 1 := by
    intro h
    have h1 := chi_neg_one_of_mod_four d hd
    rw [h, MulChar.one_apply (isUnit_one.neg : IsUnit (-1 : ZMod d))] at h1
    norm_num at h1
  have hc : (chi d).conductor ≠ 1 := fun h ↦ hne (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h)
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out _ (DirichletCharacter.conductor_dvd_level (chi d))) with h | h
  · exact absurd h hc
  · exact h
example : (chi 3).IsPrimitive ∧ (chi 7).IsPrimitive :=
  ⟨chi_isPrimitive_of_mod_four 3 rfl, chi_isPrimitive_of_mod_four 7 rfl⟩
def quadSpan (d : ℕ) : IntermediateField ℚ ℂ where
  carrier := {z | ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * sqrtNeg d}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, f, rfl⟩
    refine ⟨a * c - d * b * f, a * f + b * c, ?_⟩
    have h := sqrtNeg_sq d
    push_cast
    linear_combination (b * f : ℂ) * h
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, f, rfl⟩
    exact ⟨a + c, b + f, by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  algebraMap_mem' q := ⟨q, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    by_cases hz : (a : ℂ) + (b : ℂ) * sqrtNeg d = 0
    · rw [hz, inv_zero]
      exact ⟨0, 0, by simp⟩
    · have hN : (a ^ 2 + d * b ^ 2 : ℚ) ≠ 0 := by
        intro hN
        have ha2 : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, (Nat.cast_nonneg d : (0 : ℚ) ≤ d)]
        have ha : a = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 ha2
        have hdb : (d : ℚ) * b ^ 2 = 0 := by rw [ha] at hN; simpa using hN
        apply hz
        rcases mul_eq_zero.1 hdb with h | h
        · have hd0 : d = 0 := by exact_mod_cast h
          subst hd0
          simp [ha, sqrtNeg]
        · have hb : b = 0 := pow_eq_zero_iff two_ne_zero |>.1 h
          simp [ha, hb]
      refine ⟨a / (a ^ 2 + d * b ^ 2), -b / (a ^ 2 + d * b ^ 2), ?_⟩
      have hNc : ((a : ℂ) ^ 2 + (d : ℂ) * (b : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hN
      have h := sqrtNeg_sq d
      refine inv_eq_of_mul_eq_one_right ?_
      push_cast
      have e : ((a : ℂ) + (b : ℂ) * sqrtNeg d) *
          ((a : ℂ) / ((a : ℂ) ^ 2 + (d : ℂ) * (b : ℂ) ^ 2) +
            -(b : ℂ) / ((a : ℂ) ^ 2 + (d : ℂ) * (b : ℂ) ^ 2) * sqrtNeg d) =
          ((a : ℂ) ^ 2 - (b : ℂ) ^ 2 * sqrtNeg d ^ 2) / ((a : ℂ) ^ 2 + (d : ℂ) * (b : ℂ) ^ 2) := by
        ring
      rw [e, h, div_eq_one_iff_eq hNc]
      ring
theorem Kfield_le_quadSpan (d : ℕ) : Kfield d ≤ quadSpan d :=
  IntermediateField.adjoin_simple_le_iff.2 ⟨0, 1, by simp⟩
theorem exists_rat_of_mem (d : ℕ) (x : K d) :
    ∃ a b : ℚ, (x : ℂ) = (a : ℂ) + (b : ℂ) * sqrtNeg d :=
  Kfield_le_quadSpan d x.2
def omegaC : ℂ := (-1 + sqrtNeg 3) / 2
theorem omegaC_eq : omegaC = ((-1 / 2 : ℚ) : ℂ) + ((1 / 2 : ℚ) : ℂ) * sqrtNeg 3 := by
  unfold omegaC
  push_cast
  ring
theorem omegaC_im_pos : 0 < omegaC.im := by
  simp [omegaC, sqrtNeg]
def omegaH : ℍ := ⟨omegaC, omegaC_im_pos⟩
theorem omegaC_root : omegaC ^ 2 + omegaC + 1 = 0 := by
  have h := sqrtNeg_sq 3
  unfold omegaC
  push_cast at h
  linear_combination h / 4
theorem omegaC_mem : omegaC ∈ Kfield 3 := by
  rw [omegaC_eq]
  exact add_mem (SubfieldClass.ratCast_mem _ _)
    (mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _))
def omegaK : K 3 := ⟨omegaC, omegaC_mem⟩
theorem isIntegral_omegaK : IsIntegral ℤ omegaK := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.X + 1, by monicity!, ?_⟩
  apply Subtype.ext
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_one,
    IntermediateField.coe_add, IntermediateField.coe_pow, IntermediateField.coe_one,
    IntermediateField.coe_zero]
  exact omegaC_root
def omegaO : 𝓞 (K 3) := ⟨omegaK, isIntegral_omegaK⟩
theorem rat_eq_int_of_isIntegral {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) : ∃ n : ℤ, q = n := by
  have e : (algebraMap ℚ ℂ).toIntAlgHom q = (q : ℂ) := by simp
  have h' : IsIntegral ℤ q :=
    (isIntegral_algHom_iff ((algebraMap ℚ ℂ).toIntAlgHom) (algebraMap ℚ ℂ).injective).1 (e ▸ h)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h'
  exact ⟨n, by rw [← hn]; simp⟩
theorem int_of_three_mul_sq {c : ℚ} {k : ℤ} (h : 3 * c ^ 2 = k) : ∃ n : ℤ, c = n := by
  have hint : IsIntegral ℤ (3 * c) := by
    refine IsIntegral.of_pow two_pos ?_
    have e : (3 * c) ^ 2 = algebraMap ℤ ℚ (3 * k) := by
      simp only [algebraMap_int_eq, eq_intCast, Int.cast_mul, Int.cast_ofNat]
      linear_combination 3 * h
    rw [e]
    exact isIntegral_algebraMap
  obtain ⟨j, hj⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hj' : (j : ℚ) = 3 * c := by simpa using hj
  have hsq : j ^ 2 = 3 * k := by
    have : ((j ^ 2 : ℤ) : ℚ) = ((3 * k : ℤ) : ℚ) := by
      push_cast
      rw [hj']
      linear_combination 3 * h
    exact_mod_cast this
  obtain ⟨j', rfl⟩ := Prime.dvd_of_dvd_pow Int.prime_three (⟨k, hsq⟩ : (3 : ℤ) ∣ j ^ 2)
  exact ⟨j', by push_cast at hj'; linarith⟩
theorem exists_int_of_isIntegral_three {a b : ℚ}
    (h : IsIntegral ℤ ((a : ℂ) + (b : ℂ) * sqrtNeg 3)) :
    ∃ m n : ℤ, (a : ℂ) + (b : ℂ) * sqrtNeg 3 = (m : ℂ) + (n : ℂ) * omegaC := by
  have hα := sqrtNeg_sq 3
  have hconj : starRingEnd ℂ (sqrtNeg 3) = -sqrtNeg 3 := by simp [sqrtNeg]
  have hc : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * sqrtNeg 3) := by
    have e : (a : ℂ) - (b : ℂ) * sqrtNeg 3 =
        (starRingEnd ℂ).toIntAlgHom ((a : ℂ) + (b : ℂ) * sqrtNeg 3) := by
      change _ = starRingEnd ℂ ((a : ℂ) + (b : ℂ) * sqrtNeg 3)
      rw [map_add, map_mul, hconj, map_ratCast, map_ratCast]
      ring
    rw [e]
    exact h.map _
  have hsum : IsIntegral ℤ (((2 * a : ℚ)) : ℂ) := by
    have e : (((2 * a : ℚ)) : ℂ) =
        ((a : ℂ) + (b : ℂ) * sqrtNeg 3) + ((a : ℂ) - (b : ℂ) * sqrtNeg 3) := by
      push_cast
      ring
    rw [e]
    exact h.add hc
  have hprod : IsIntegral ℤ (((a ^ 2 + 3 * b ^ 2 : ℚ)) : ℂ) := by
    have e : (((a ^ 2 + 3 * b ^ 2 : ℚ)) : ℂ) =
        ((a : ℂ) + (b : ℂ) * sqrtNeg 3) * ((a : ℂ) - (b : ℂ) * sqrtNeg 3) := by
      have hb2 : (b : ℂ) ^ 2 * sqrtNeg 3 ^ 2 = (b : ℂ) ^ 2 * (-3) := by
        rw [hα]
        push_cast
        ring
      push_cast
      linear_combination hb2
    rw [e]
    exact h.mul hc
  obtain ⟨m, hm⟩ := rat_eq_int_of_isIntegral hsum
  obtain ⟨N, hN⟩ := rat_eq_int_of_isIntegral hprod
  obtain ⟨c, hcq⟩ := int_of_three_mul_sq (c := 2 * b) (k := 4 * N - m ^ 2) (by
    push_cast
    rw [← hN, ← hm]
    ring)
  have hmc : m ^ 2 + 3 * c ^ 2 = 4 * N := by
    have : ((m ^ 2 + 3 * c ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [← hm, ← hcq, ← hN]
      ring
    exact_mod_cast this
  have hev : Even (m + c) := by
    have hp : Even ((m + c) * (m - c)) := ⟨2 * (N - c ^ 2), by linear_combination hmc⟩
    rcases Int.even_mul.1 hp with h1 | h1
    · exact h1
    · have e : m + c = (m - c) + 2 * c := by ring
      rw [e]
      exact h1.add (even_two_mul c)
  obtain ⟨k, hk⟩ := hev
  refine ⟨k, c, ?_⟩
  have hmC : (2 : ℂ) * a = m := by exact_mod_cast hm
  have hcC : (2 : ℂ) * b = c := by exact_mod_cast hcq
  have hkC : (m : ℂ) + c = k + k := by exact_mod_cast hk
  unfold omegaC
  linear_combination (1 / 2 : ℂ) * hmC + (sqrtNeg 3 / 2) * hcC + (1 / 2 : ℂ) * hkC
theorem image_one_three :
    (algebraMap (K 3) ℂ) '' ((1 : FractionalIdeal (𝓞 (K 3))⁰ (K 3)) : Set (K 3)) =
      {z : ℂ | ∃ m n : ℤ, z = 1 * ((m : ℂ) + (n : ℂ) * (omegaH : ℂ))} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 (SetLike.mem_coe.1 hx)
    obtain ⟨a, b, hab⟩ := exists_rat_of_mem 3 (algebraMap (𝓞 (K 3)) (K 3) x')
    have hint : IsIntegral ℤ (algebraMap (K 3) ℂ (algebraMap (𝓞 (K 3)) (K 3) x')) :=
      (RingOfIntegers.isIntegral_coe x').map (IsScalarTower.toAlgHom ℤ (K 3) ℂ)
    have e : algebraMap (K 3) ℂ (algebraMap (𝓞 (K 3)) (K 3) x') =
        (a : ℂ) + (b : ℂ) * sqrtNeg 3 := hab
    rw [e] at hint ⊢
    obtain ⟨m, n, hmn⟩ := exists_int_of_isIntegral_three hint
    exact ⟨m, n, by rw [hmn, one_mul]; rfl⟩
  · rintro ⟨m, n, rfl⟩
    refine ⟨algebraMap (𝓞 (K 3)) (K 3) ((m : 𝓞 (K 3)) + (n : 𝓞 (K 3)) * omegaO),
      SetLike.mem_coe.2 ((FractionalIdeal.mem_one_iff _).2 ⟨_, rfl⟩), ?_⟩
    simp only [map_add, map_mul, map_intCast, one_mul]
    rfl
theorem isTauOf_three : IsTauOf 3 1 omegaH :=
  ⟨1, map_one _, 1, one_ne_zero, image_one_three⟩
example : IsTauOf 3 (1 : ClassGroup (𝓞 (K 3)))⁻¹ omegaH := by
  rw [inv_one]
  exact isTauOf_three
example : HermitianMetric (K 3) (Fin 2 → 𝓞 (K 3)) := piMetric fun _ ↦ HermitianMetric.integers (K 3)
def volTwo : Fin 2 → ℝ := ![1, 2]
theorem volTwo_pos : ∀ c, 0 < volTwo c := by
  intro c
  fin_cases c <;> simp [volTwo]
example : HermitianMetric (K 3) (Fin 2 → 𝓞 (K 3)) :=
  piMetric fun c ↦ formScale (HermitianMetric.integers (K 3)) (volTwo c / ∑ c', volTwo c')
    (volFrac_pos volTwo_pos c)
example : HermitianMetric (K 3) (𝓞 (K 3)) := formScale (HermitianMetric.integers (K 3)) 2 two_pos
end Inhabitants
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum


