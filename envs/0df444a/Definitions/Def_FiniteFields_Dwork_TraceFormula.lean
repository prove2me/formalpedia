-- Prove2me | Definitions.Def_FiniteFields_Dwork_TraceFormula
-- name    : FiniteFields_Dwork_TraceFormula
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T01:34:01.441544+00:00
-- url     : https://prove2.me/theorems/a73ddb43-49f6-4e2a-b207-9d938b266e6b
-- title:
--   Toric point counts, coefficient base change and Fredholm determinants $\det(1-Xu)$ for Dwork's trace formula
-- statement:
--   Let $k$ be a finite field with $q=p^a$ elements, $L=K_0(\zeta)$ the ramified coefficient field, $w$ a positive weight on $\mathbb N^d$, and $f$ a polynomial over $k$ with finite support. Let $F_f$ be its splitting product and $\alpha_{f,q}$ Dwork's $q$-level operator on the Tate algebra $L\langle x\rangle$, as in the preceding files.
--
--   1. **Toric point counts.** A finitely supported polynomial $f=\sum_u a_ux^u$ is evaluated by its finite monomial sum. For $s\ge1$ the toric hypersurface count is
--   $$N^*_s(f)=\#\big\{x\in(\mathbb F_{q^s}^{\times})^d : f(x)=0\big\}.$$
--   2. **Base change of coefficients.** For an embedding $k\to K$ of finite fields of characteristic $p$, the file defines the induced maps $W(k)\to W(K)$, on fraction fields, on the completions $K_0(k)\to K_0(K)$ (an isometry), and the extension $K_0(k)(\zeta)\to K_0(K)(\zeta)$ sending $\zeta$ to $\zeta$. These induce base change of Tate-algebra elements coefficientwise and of residue polynomials $f$.
--   3. **Iterated splitting products.** The dilation $g(x)\mapsto g(x^m)$ is a ring endomorphism of $L\langle x\rangle$ for $m\neq0$. The products $H_m$ are defined by
--   $$H_0=1,\qquad H_{j+1}(x)=H_j(x^p)\cdot\big(\sigma_L^{-(j+1)}F_f\big)(x),$$
--   where $\sigma_L^{-1}$ acts on coefficients. The diagonal splitting coefficient is the coefficient of $x^{(q^s-1)u}$ in $H_{as}$. The file also defines the kernel of the iterate $\alpha_{f,q}^{\,s}$ in the monomial basis and the power $q^s=p^{as}$.
--   4. **Evaluation.** For $g=\sum_ua_ux^u\in K\langle x\rangle$ and $x\in K^d$ with all $|x_i|=1$, the value $g(x)=\sum_ua_ux^u$ is defined, and $g\mapsto g(x)$ is continuous and linear. The file also twists the coefficients of $f$ by a power of the inverse Frobenius of $k$.
--   5. **Auxiliary variable.** For $f$ in $d$ variables, $x_0f(x)$ is the corresponding polynomial in $d+1$ variables.
--   6. **Finite Fredholm determinants.** For an endomorphism $u$ of a finite free module over a commutative ring $R$,
--   $$\det(1-Xu)=X^{n}\chi_u(1/X)\in R[X],\qquad -\frac{\frac{d}{dX}\det(1-Xu)}{\det(1-Xu)}\in R[[X]],$$
--   where $n$ is the rank and $\chi_u$ the characteristic polynomial. The file also defines the variant $\det(1-X\,ba)$ for maps $a:M\to N$ and $b:N\to M$.
--
--   The file also contains the structural lemmas these definitions need, such as norm compatibility of base change, multiplicativity of dilation, and summability of evaluations on the unit polydisc.
--
--   These are the objects that enter Dwork's trace formula (Lemma 2, formula (14), in §2) and its use in §3, formulas (16)–(21). The toric counts are expressed through character sums, the auxiliary variable $x_0$ turns the character sum into a point count, and finite Fredholm determinants normalize the trace–determinant relation.
--
--   **Formalization Note** The toric count is indexed like all extension counts: the Lean index $n$ refers to the extension of degree $n+1$.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §2: Lemma 2 and the trace formula (14), $(q^s-1)^n\operatorname{Tr}((\psi\circ H)^s)=\sum_{x^{q^s-1}=1}\prod_{j<s}H(x^{q^j})$; §3: formulas (16)–(21) (character sums, $q^sN_s$ as a trace, Fredholm determinants). Lean: ported from the `finite_fields` project (commit e8b5bf14), modules `WeilConjectures/Dwork/WittTraceCharacter/TraceCharacter.lean`, `WeilConjectures/Dwork/ExtensionAdditiveCharacter.lean`, `WeilConjectures/Dwork/ToricCharacterSum.lean`, `WeilConjectures/Dwork/CyclotomicBaseChange/Transport.lean`, `WeilConjectures/Dwork/DworkTraceFormula/Core.lean`, `WeilConjectures/Dwork/DworkTraceFormula/Auxiliary.lean`, `WeilConjectures/Dwork/DworkTraceFormula/Terminal.lean`, `WeilConjectures/LinearAlgebra/Fredholm.lean`.

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter

section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
local instance dw4e2TraceCharacterResiduePrimeAlgebra : Algebra (ZMod p) k := ZMod.algebra k p
end FiniteFields.Dwork
end
end

section
noncomputable section
open scoped BigOperators
namespace FiniteFields.Dwork
attribute [local instance] dw4eResiduePrimeAlgebra dw4eExtensionCharP
section Eval
variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] {d : ℕ}
def finitePolynomialEval (f : MonomialIndex d →₀ R) (x : Fin d → A) : A :=
  f.sum fun u a => algebraMap R A a * ∏ i, x i ^ u i
theorem finitePolynomialEval_eq_sum (f : MonomialIndex d →₀ R) (x : Fin d → A) :
    finitePolynomialEval R A f x
      = ∑ u ∈ f.support, algebraMap R A (f u) * ∏ i, x i ^ u i := rfl
end Eval
section Torus
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime] [Field k₀] [CharP k₀ p₀] [Finite k₀]
abbrev affineTorus (d n : ℕ) : Type :=
  {x : FiniteFields.AffinePoints k₀ p₀ d n // ∀ i, x i ≠ 0}
abbrev toricHypersurfacePoint {d : ℕ} (f : MonomialIndex d →₀ k₀) (n : ℕ) : Type :=
  {x : affineTorus k₀ p₀ d n //
    finitePolynomialEval k₀ (FiniteFields.Extension k₀ p₀ n) f
      (x : Fin d → FiniteFields.Extension k₀ p₀ n) = 0}
def toricHypersurfacePointCount {d : ℕ} (f : MonomialIndex d →₀ k₀) (n : ℕ) : ℕ :=
  Nat.card (toricHypersurfacePoint k₀ p₀ f n)
end Torus
section Orthogonality
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime] [Field k₀] [CharP k₀ p₀] [Finite k₀]
end Orthogonality
section CharacterSum
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime] [Field k₀] [CharP k₀ p₀] [Finite k₀]
end CharacterSum
section SplittingProduct
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime] [Field k₀] [CharP k₀ p₀] [Finite k₀]
end SplittingProduct
end FiniteFields.Dwork
end
end

section
noncomputable section
open Polynomial
open scoped NNReal WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
 theorem coefficientField_p_nnreal_ne_zero : ((p : ℝ≥0)) ≠ 0 := by
  have h := (Fact.out : p.Prime).pos
  exact_mod_cast h.ne'
theorem coefficientField_norm_eq (x : CoefficientField k p) :
    ‖x‖ = (WithZeroMulInt.toNNReal (coefficientField_p_nnreal_ne_zero p) (Valued.v x) : ℝ) := by
  have hres :=
    Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (v := (Valued.v : Valuation (CoefficientField k p) ℤᵐ⁰))
      (coefficientFieldValuation_surjective k p) x
  have key : (Valuation.RankOne.hom (Valued.v : Valuation (CoefficientField k p) ℤᵐ⁰))
        (Valued.v.restrict x)
      = (WithZeroMulInt.toNNReal (coefficientField_p_nnreal_ne_zero p))
        ((Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt
          (Valued.v : Valuation (CoefficientField k p) ℤᵐ⁰)) (Valued.v.restrict x)) := rfl
  rw [Valued.toNormedField.norm_def, key, hres]
end FiniteFields.Dwork
end
end

section
noncomputable section
open Polynomial
open scoped NNReal WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
section BaseChange
 theorem coefficientAddVal_uniformizer (F : Type*) (q : ℕ) [Fact q.Prime] [Field F]
    [CharP F q] [Finite F] :
    IsDiscreteValuationRing.addVal (CoefficientRing F q) (q : CoefficientRing F q) = 1 :=
  IsDiscreteValuationRing.addVal_uniformizer (WittVector.irreducible q)
 theorem valuedBase_surjective :
    Function.Surjective (Valued.v : WithVal (coefficientValuation k p) → ℤᵐ⁰) := by
  intro γ
  obtain ⟨x, hx⟩ := coefficientValuation_surjective k p γ
  exact ⟨WithVal.toVal (coefficientValuation k p) x, hx⟩
variable (K : Type*) [Field K] [CharP K p] [Finite K] (σ : k →+* K)
def coefficientRingBaseChange : CoefficientRing k p →+* CoefficientRing K p :=
  WittVector.map σ
omit [CharP k p] [Finite k] [CharP K p] [Finite K] in
theorem coefficientRingBaseChange_injective :
    Function.Injective (coefficientRingBaseChange k p K σ) :=
  WittVector.map_injective σ σ.injective
theorem coefficientAddVal_baseChange (a : CoefficientRing k p) :
    IsDiscreteValuationRing.addVal (CoefficientRing K p) (coefficientRingBaseChange k p K σ a)
      = IsDiscreteValuationRing.addVal (CoefficientRing k p) a := by
  by_cases ha : a = 0
  · simp [ha]
  · obtain ⟨n, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' (p := p) a ha
    have hzk : IsDiscreteValuationRing.addVal (CoefficientRing k p) (u : CoefficientRing k p) = 0 :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr u.isUnit
    have hzK : IsDiscreteValuationRing.addVal (CoefficientRing K p)
        (coefficientRingBaseChange k p K σ (u : CoefficientRing k p)) = 0 :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (u.isUnit.map _)
    rw [map_mul, map_pow, map_natCast]
    rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow,
      AddValuation.map_pow, coefficientAddVal_uniformizer K p, coefficientAddVal_uniformizer k p,
      hzk, hzK]
theorem coefficientIntValuation_baseChange (a : CoefficientRing k p) :
    (IsDiscreteValuationRing.maximalIdeal (CoefficientRing K p)).intValuation
        (coefficientRingBaseChange k p K σ a)
      = (IsDiscreteValuationRing.maximalIdeal (CoefficientRing k p)).intValuation a := by
  simp only [IsDiscreteValuationRing.intValuation_maximalIdeal, coefficientAddVal_baseChange]
def coefficientFractionFieldBaseChange :
    CoefficientFractionField k p →+* CoefficientFractionField K p :=
  IsFractionRing.lift
    (g := (algebraMap (CoefficientRing K p) (CoefficientFractionField K p)).comp
      (coefficientRingBaseChange k p K σ))
    ((IsFractionRing.injective (CoefficientRing K p)
      (CoefficientFractionField K p)).comp (coefficientRingBaseChange_injective k p K σ))
omit [Finite k] [Finite K] in
@[simp]
theorem coefficientFractionFieldBaseChange_algebraMap (a : CoefficientRing k p) :
    coefficientFractionFieldBaseChange k p K σ
        (algebraMap (CoefficientRing k p) (CoefficientFractionField k p) a)
      = algebraMap (CoefficientRing K p) (CoefficientFractionField K p)
          (coefficientRingBaseChange k p K σ a) :=
  IsFractionRing.lift_algebraMap _ a
theorem coefficientValuation_baseChange (x : CoefficientFractionField k p) :
    coefficientValuation K p (coefficientFractionFieldBaseChange k p K σ x)
      = coefficientValuation k p x := by
  obtain ⟨a, b, _hb, hx⟩ := IsFractionRing.div_surjective (CoefficientRing k p) x
  rw [← hx, map_div₀, coefficientFractionFieldBaseChange_algebraMap,
    coefficientFractionFieldBaseChange_algebraMap, Valuation.map_div, Valuation.map_div]
  simp only [coefficientValuation,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    coefficientIntValuation_baseChange]
def coefficientValuedBaseChange :
    WithVal (coefficientValuation k p) →+* WithVal (coefficientValuation K p) :=
  ((WithVal.equiv (coefficientValuation K p)).symm.toRingHom).comp
    ((coefficientFractionFieldBaseChange k p K σ).comp
      (WithVal.equiv (coefficientValuation k p)).toRingHom)
 theorem coefficientValuedBaseChange_value (x : WithVal (coefficientValuation k p)) :
    Valued.v (coefficientValuedBaseChange k p K σ x) = Valued.v x := by
  change coefficientValuation K p
      (coefficientFractionFieldBaseChange k p K σ x.ofVal) = coefficientValuation k p x.ofVal
  exact coefficientValuation_baseChange k p K σ x.ofVal
theorem coefficientValuedBaseChange_uniformContinuous :
    UniformContinuous (coefficientValuedBaseChange k p K σ) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero (WithVal (coefficientValuation k p)) ℤᵐ⁰).tendsto_iff
      (Valued.hasBasis_nhds_zero (WithVal (coefficientValuation K p)) ℤᵐ⁰),
    true_and, forall_const]
  intro γ
  obtain ⟨x₀, hx₀⟩ := valuedBase_surjective k p
    (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hcne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  have hx₀ne : Valued.v.restrict x₀ ≠ (0 : _) := by
    rw [Ne, Valuation.restrict_eq_zero_iff, hx₀]
    exact hcne
  refine ⟨Units.mk0 (Valued.v.restrict x₀) hx₀ne, fun x hx => ?_⟩
  change Valued.v.restrict (coefficientValuedBaseChange k p K σ x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, coefficientValuedBaseChange_value]
  change Valued.v.restrict x < (Units.mk0 (Valued.v.restrict x₀) hx₀ne).1 at hx
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx
  simpa only [Units.val_mk0, Valuation.embedding_restrict, hx₀] using hx
def coefficientFieldBaseChange : CoefficientField k p →+* CoefficientField K p :=
  UniformSpace.Completion.mapRingHom (coefficientValuedBaseChange k p K σ)
    (coefficientValuedBaseChange_uniformContinuous k p K σ).continuous
theorem coefficientFieldBaseChange_coe (a : WithVal (coefficientValuation k p)) :
    coefficientFieldBaseChange k p K σ (a : CoefficientField k p)
      = ((coefficientValuedBaseChange k p K σ a : WithVal (coefficientValuation K p)) :
          CoefficientField K p) :=
  UniformSpace.Completion.mapRingHom_coe
    (coefficientValuedBaseChange_uniformContinuous k p K σ).continuous a
theorem coefficientFieldBaseChange_continuous :
    Continuous (coefficientFieldBaseChange k p K σ) :=
  UniformSpace.Completion.continuous_map
theorem norm_coefficientFieldBaseChange (x : CoefficientField k p) :
    ‖coefficientFieldBaseChange k p K σ x‖ = ‖x‖ := by
  have hagree : (fun a : WithVal (coefficientValuation k p) =>
        ‖coefficientFieldBaseChange k p K σ (a : CoefficientField k p)‖)
      = fun a : WithVal (coefficientValuation k p) => ‖(a : CoefficientField k p)‖ := by
    funext a
    rw [coefficientFieldBaseChange_coe, coefficientField_norm_eq, coefficientField_norm_eq,
      Valued.valuedCompletion_apply, Valued.valuedCompletion_apply,
      coefficientValuedBaseChange_value]
  have heq := DenseRange.equalizer
    (UniformSpace.Completion.denseRange_coe (α := WithVal (coefficientValuation k p)))
    (continuous_norm.comp (coefficientFieldBaseChange_continuous k p K σ))
    continuous_norm hagree
  exact congrFun heq x
end BaseChange
end FiniteFields.Dwork
end
end

section
noncomputable section
open Polynomial
open scoped NNReal WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
section CyclotomicLift
variable (K : Type*) [Field K] [CharP K p] [Finite K] [Algebra k K]
@[reducible]
def dworkCyclotomicBaseAlgebra : Algebra (CoefficientField k p) (DworkCyclotomicField K p) :=
  RingHom.toAlgebra ((algebraMap (CoefficientField K p) (DworkCyclotomicField K p)).comp
    (coefficientFieldBaseChange k p K (algebraMap k K)))
attribute [local instance 100] dworkCyclotomicBaseAlgebra
 theorem neZero_p : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
 theorem neZero_p_coefficientField : NeZero ((p : ℕ) : CoefficientField k p) :=
  ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
 theorem aeval_dworkPrimitiveRoot_base :
    (Polynomial.aeval (dworkPrimitiveRoot K p))
        (minpoly (CoefficientField k p) (dworkPrimitiveRoot k p)) = 0 := by
  haveI := neZero_p p
  haveI := neZero_p_coefficientField k p
  rw [dworkPrimitiveRoot_minpoly, DworkCyclotomicPolynomial, Polynomial.aeval_def,
    ← Polynomial.eval_map, Polynomial.map_cyclotomic]
  exact (dworkPrimitiveRoot_isPrimitiveRoot K p).isRoot_cyclotomic (Fact.out : p.Prime).pos
def dworkCyclotomicBaseChangeAlgHom :
    DworkCyclotomicField k p →ₐ[CoefficientField k p] DworkCyclotomicField K p :=
  haveI := neZero_p p
  haveI := neZero_p_coefficientField k p
  PowerBasis.lift
    ((dworkPrimitiveRoot_isPrimitiveRoot k p).powerBasis (CoefficientField k p))
    (dworkPrimitiveRoot K p)
    (by
      simpa only [IsPrimitiveRoot.powerBasis_gen] using aeval_dworkPrimitiveRoot_base k p K)
def dworkCyclotomicBaseChange :
    DworkCyclotomicField k p →+* DworkCyclotomicField K p :=
  (dworkCyclotomicBaseChangeAlgHom k p K).toRingHom
@[simp]
theorem dworkCyclotomicBaseChange_apply (x : DworkCyclotomicField k p) :
    dworkCyclotomicBaseChange k p K x = dworkCyclotomicBaseChangeAlgHom k p K x := rfl
theorem dworkCyclotomicBaseChange_algebraMap (x : CoefficientField k p) :
    dworkCyclotomicBaseChange k p K
        (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) x)
      = algebraMap (CoefficientField K p) (DworkCyclotomicField K p)
          (coefficientFieldBaseChange k p K (algebraMap k K) x) := by
  exact (dworkCyclotomicBaseChangeAlgHom k p K).commutes x
theorem norm_dworkCyclotomicBaseChange (x : DworkCyclotomicField k p) :
    ‖dworkCyclotomicBaseChange k p K x‖ = ‖x‖ := by
  set f : AbsoluteValue (DworkCyclotomicField k p) ℝ :=
    { toFun := fun y => ‖dworkCyclotomicBaseChange k p K y‖
      map_mul' := fun y z => by simp only [map_mul, norm_mul]
      nonneg' := fun _ => norm_nonneg _
      eq_zero' := fun y => by
        constructor
        · intro hy
          exact (dworkCyclotomicBaseChange k p K).injective
            (by rw [norm_eq_zero.mp hy, map_zero])
        · intro hy
          rw [hy, map_zero, norm_zero]
      add_le' := fun y z => by
        simp only [map_add]
        exact norm_add_le _ _ } with hfdef
  have hext : ∀ y : CoefficientField k p,
      f (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) y) = ‖y‖ := by
    intro y
    show ‖dworkCyclotomicBaseChange k p K
      (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) y)‖ = ‖y‖
    rw [dworkCyclotomicBaseChange_algebraMap, dworkCyclotomicField_norm_algebraMap,
      norm_coefficientFieldBaseChange]
  haveI : Algebra.IsAlgebraic (CoefficientField k p) (DworkCyclotomicField k p) :=
    Algebra.IsAlgebraic.of_finite (CoefficientField k p) (DworkCyclotomicField k p)
  have hspec := spectralNorm_unique_field_norm_ext (f := f) hext x
  have hnorm : ‖x‖ = spectralNorm (CoefficientField k p) (DworkCyclotomicField k p) x := rfl
  rw [hnorm]
  exact hspec
end CyclotomicLift
end FiniteFields.Dwork
end
end

section
noncomputable section
open Polynomial
open scoped NNReal WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
section Transport
variable (K : Type*) [Field K] [CharP K p] [Finite K] [Algebra k K]
attribute [local instance 100] dworkCyclotomicBaseAlgebra
theorem dworkCyclotomicBaseChange_isometry :
    Isometry (dworkCyclotomicBaseChange k p K) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_dworkCyclotomicBaseChange k p K)
theorem dworkCyclotomicBaseChange_continuous :
    Continuous (dworkCyclotomicBaseChange k p K) :=
  (dworkCyclotomicBaseChange_isometry k p K).continuous
end Transport
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
local instance dw5cResiduePrimeAlgebra : Algebra (ZMod p) k := ZMod.algebra k p
variable {d : ℕ} (w : PositiveMonomialWeight d)
section Antidiagonal
omit [Fact p.Prime] [Field k] [CharP k p] [Finite k] in
 theorem monomialFrobenius_apply (m : ℕ) (u : MonomialIndex d) (i : Fin d) :
    monomialFrobenius m u i = m * u i := rfl
omit [Fact p.Prime] [Field k] [CharP k p] [Finite k] in
 theorem antidiagonal_dilated_split {m : ℕ} (hm : m ≠ 0)
    {u γ x : MonomialIndex d}
    (hx : monomialFrobenius m γ + x = monomialFrobenius m u) :
    γ + (u - γ) = u ∧ monomialFrobenius m (u - γ) = x := by
  have hcoord : ∀ i, m * γ i + x i = m * u i := by
    intro i
    have h := DFunLike.congr_fun hx i
    simpa [monomialFrobenius_apply] using h
  have hle : ∀ i, γ i ≤ u i := by
    intro i
    have h := hcoord i
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.pos_of_ne_zero hm)
    omega
  constructor
  · ext i
    have hli := hle i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply]
    omega
  · ext i
    have h := hcoord i
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (hle i)
    have hmt : m * (γ i + t) = m * γ i + m * t := by ring
    rw [ht] at h
    simp only [monomialFrobenius_apply, Finsupp.tsub_apply, ht,
      Nat.add_sub_cancel_left]
    omega
omit [Fact p.Prime] [Field k] [CharP k p] [Finite k] in
 theorem sum_antidiagonal_monomialFrobenius {M : Type*} [AddCommMonoid M]
    {m : ℕ} (hm : m ≠ 0) (u : MonomialIndex d)
    (F : MonomialIndex d × MonomialIndex d → M)
    (hF : ∀ x : MonomialIndex d × MonomialIndex d,
      (¬ ∃ γ, monomialFrobenius m γ = x.1) → F x = 0) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (monomialFrobenius m u), F x
      = ∑ y ∈ Finset.HasAntidiagonal.antidiagonal u,
          F (monomialFrobenius m y.1, monomialFrobenius m y.2) := by
  classical
  set dilate : MonomialIndex d × MonomialIndex d → MonomialIndex d × MonomialIndex d :=
    fun y => (monomialFrobenius m y.1, monomialFrobenius m y.2) with hdilate
  have hinj : ∀ y ∈ Finset.HasAntidiagonal.antidiagonal u, ∀ z ∈ Finset.HasAntidiagonal.antidiagonal u,
      dilate y = dilate z → y = z := by
    intro y _ z _ hyz
    have h1 := congrArg Prod.fst hyz
    have h2 := congrArg Prod.snd hyz
    exact Prod.ext (monomialFrobenius_injective m hm h1)
      (monomialFrobenius_injective m hm h2)
  have himage : (Finset.HasAntidiagonal.antidiagonal u).image dilate
      ⊆ Finset.HasAntidiagonal.antidiagonal (monomialFrobenius m u) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    rw [← monomialFrobenius_add]
    exact congrArg (monomialFrobenius m) (Finset.HasAntidiagonal.mem_antidiagonal.mp hy)
  have hvanish : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (monomialFrobenius m u),
      x ∉ (Finset.HasAntidiagonal.antidiagonal u).image dilate → F x = 0 := by
    intro x hx hnot
    refine hF x ?_
    rintro ⟨γ, hγ⟩
    apply hnot
    have hsum : monomialFrobenius m γ + x.2 = monomialFrobenius m u := by
      rw [hγ]
      exact Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    obtain ⟨hsplit, hsecond⟩ := antidiagonal_dilated_split hm hsum
    refine Finset.mem_image.mpr ⟨(γ, u - γ), Finset.HasAntidiagonal.mem_antidiagonal.mpr hsplit, ?_⟩
    exact Prod.ext hγ hsecond
  rw [← Finset.sum_subset himage hvanish, Finset.sum_image hinj]
end Antidiagonal
section Dilation
 def dw5cDiscreteMonomial (u : MonomialIndex d) : DiscreteMonomialIndex d :=
  WithTopology.toTopology ⊥ u
 theorem dw5cDiscreteMonomial_injective :
    Function.Injective (dw5cDiscreteMonomial (d := d)) :=
  WithTopology.toTopology_injective ⊥
 def dilationCoordinate (m : ℕ)
    (g : OverconvergentSeries (DworkCyclotomicField k p) d w) (u : MonomialIndex d) :
    DworkCyclotomicField k p := by
  classical
  exact if hu : ∃ v, monomialFrobenius m v = u then
    seriesCoefficient w (Classical.choose hu) g else 0
 theorem dilationCoordinate_dilated {m : ℕ} (hm : m ≠ 0)
    (g : OverconvergentSeries (DworkCyclotomicField k p) d w) (u : MonomialIndex d) :
    dilationCoordinate k p w m g (monomialFrobenius m u) = seriesCoefficient w u g := by
  classical
  have hu : ∃ v, monomialFrobenius m v = monomialFrobenius m u := ⟨u, rfl⟩
  rw [dilationCoordinate, dif_pos hu]
  exact congrArg (fun v => seriesCoefficient w v g)
    (monomialFrobenius_injective m hm (Classical.choose_spec hu))
 theorem dilationCoordinate_of_not_dilated (m : ℕ)
    (g : OverconvergentSeries (DworkCyclotomicField k p) d w) (u : MonomialIndex d)
    (hu : ¬ ∃ v, monomialFrobenius m v = u) :
    dilationCoordinate k p w m g u = 0 := by
  classical
  rw [dilationCoordinate, dif_neg hu]
 theorem dilationCoordinate_zeroAtInfty (m : ℕ)
    (g : OverconvergentSeries (DworkCyclotomicField k p) d w) :
    Tendsto (fun U : DiscreteMonomialIndex d =>
      dilationCoordinate k p w m g U.ofTopology) (cocompact _) (nhds 0) := by
  classical
  rw [Filter.cocompact_eq_cofinite, Metric.tendsto_nhds]
  intro ε hε
  have hsmall := Metric.tendsto_nhds.mp
    (by simpa only [Filter.cocompact_eq_cofinite] using zero_at_infty g) ε hε
  set A : Set (MonomialIndex d) :=
    {v | ¬ dist (seriesCoefficient w v g) 0 < ε} with hA
  have hAfinite : A.Finite := by
    have hfinite : {U : DiscreteMonomialIndex d | ¬ dist (g U) 0 < ε}.Finite :=
      Filter.eventually_cofinite.mp hsmall
    exact hfinite.preimage (dw5cDiscreteMonomial_injective (d := d)).injOn
  have hEfinite : ((dw5cDiscreteMonomial (d := d)) '' (monomialFrobenius m '' A)).Finite :=
    (hAfinite.image _).image _
  filter_upwards [hEfinite.eventually_cofinite_notMem] with U hU
  by_cases hrange : ∃ v, monomialFrobenius m v = U.ofTopology
  · have hnot : Classical.choose hrange ∉ A := by
      intro hmem
      exact hU ⟨monomialFrobenius m (Classical.choose hrange),
        ⟨Classical.choose hrange, hmem, rfl⟩,
        by rw [Classical.choose_spec hrange]; rfl⟩
    have := not_not.mp hnot
    rw [dilationCoordinate, dif_pos hrange]
    exact this
  · rw [dilationCoordinate_of_not_dilated k p w m g _ hrange]
    simpa using hε
 def tateDilationSeries (m : ℕ)
    (g : OverconvergentSeries (DworkCyclotomicField k p) d w) :
    OverconvergentSeries (DworkCyclotomicField k p) d w where
  toFun U := dilationCoordinate k p w m g U.ofTopology
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := dilationCoordinate_zeroAtInfty k p w m g
def tateDilation (m : ℕ) (g : RamifiedOverconvergentTateAlgebra k p w) :
    RamifiedOverconvergentTateAlgebra k p w :=
  ⟨tateDilationSeries k p w m g.toSeries⟩
theorem tateDilation_coefficient_dilated {m : ℕ} (hm : m ≠ 0)
    (g : RamifiedOverconvergentTateAlgebra k p w) (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w (monomialFrobenius m u) (tateDilation k p w m g)
      = overconvergentTateAlgebraCoefficient w u g :=
  dilationCoordinate_dilated k p w hm g.toSeries u
theorem tateDilation_coefficient_of_not_dilated (m : ℕ)
    (g : RamifiedOverconvergentTateAlgebra k p w) (u : MonomialIndex d)
    (hu : ¬ ∃ v, monomialFrobenius m v = u) :
    overconvergentTateAlgebraCoefficient w u (tateDilation k p w m g) = 0 :=
  dilationCoordinate_of_not_dilated k p w m g.toSeries u hu
theorem tate_ext {g h : RamifiedOverconvergentTateAlgebra k p w}
    (hgh : ∀ u, overconvergentTateAlgebraCoefficient w u g
      = overconvergentTateAlgebraCoefficient w u h) : g = h := by
  refine OverconvergentTateAlgebra.ext ?_
  ext U
  have h := hgh U.ofTopology
  simpa [overconvergentTateAlgebraCoefficient_apply, seriesCoefficient_apply] using h
@[simp]
theorem tateDilation_one {m : ℕ} (hm : m ≠ 0) :
    tateDilation k p w m (1 : RamifiedOverconvergentTateAlgebra k p w) = 1 := by
  classical
  refine tate_ext k p w fun u => ?_
  by_cases hu : ∃ v, monomialFrobenius m v = u
  · obtain ⟨v, rfl⟩ := hu
    rw [tateDilation_coefficient_dilated k p w hm, coefficient_one, coefficient_one]
    have hiff : monomialFrobenius m v = 0 ↔ v = 0 := by
      constructor
      · intro h
        exact monomialFrobenius_injective m hm (by simpa using h)
      · rintro rfl
        simp
    by_cases hv : v = 0
    · simp [hv]
    · rw [if_neg hv, if_neg (fun h => hv (hiff.mp h))]
  · rw [tateDilation_coefficient_of_not_dilated k p w m _ u hu, coefficient_one,
      if_neg (fun h => hu ⟨0, by simp [h]⟩)]
theorem tateDilation_mul {m : ℕ} (hm : m ≠ 0)
    (g h : RamifiedOverconvergentTateAlgebra k p w) :
    tateDilation k p w m (g * h)
      = tateDilation k p w m g * tateDilation k p w m h := by
  classical
  have hvanish : ∀ x : MonomialIndex d × MonomialIndex d,
      (¬ ∃ γ, monomialFrobenius m γ = x.1) →
        overconvergentTateAlgebraCoefficient w x.1 (tateDilation k p w m g) *
          overconvergentTateAlgebraCoefficient w x.2 (tateDilation k p w m h) = 0 := by
    intro x hx
    rw [tateDilation_coefficient_of_not_dilated k p w m g x.1 hx, zero_mul]
  refine tate_ext k p w fun u => ?_
  by_cases hu : ∃ v, monomialFrobenius m v = u
  · obtain ⟨v, rfl⟩ := hu
    rw [tateDilation_coefficient_dilated k p w hm, coefficient_mul, coefficient_mul,
      sum_antidiagonal_monomialFrobenius hm v _ hvanish]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [tateDilation_coefficient_dilated k p w hm,
      tateDilation_coefficient_dilated k p w hm]
  · rw [tateDilation_coefficient_of_not_dilated k p w m _ u hu, coefficient_mul]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    by_cases hx1 : ∃ γ, monomialFrobenius m γ = x.1
    · by_cases hx2 : ∃ δ, monomialFrobenius m δ = x.2
      · obtain ⟨γ, hγ⟩ := hx1
        obtain ⟨δ, hδ⟩ := hx2
        refine absurd ⟨γ + δ, ?_⟩ hu
        rw [monomialFrobenius_add, hγ, hδ]
        exact Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      · rw [tateDilation_coefficient_of_not_dilated k p w m h x.2 hx2, mul_zero]
    · rw [tateDilation_coefficient_of_not_dilated k p w m g x.1 hx1, zero_mul]
end Dilation
section Intertwine
end Intertwine
section Telescope
def dworkIteratedSplittingProduct (f : MonomialIndex d →₀ k) (m : ℕ) :
    RamifiedOverconvergentTateAlgebra k p w :=
  Nat.rec (1 : RamifiedOverconvergentTateAlgebra k p w)
    (fun j prev => tateDilation k p w p prev
      * (ramifiedCoefficientwiseFrobeniusInv k p w)^[j + 1]
          (teichmullerSplittingProduct k p w f))
    m
@[simp]
theorem dworkIteratedSplittingProduct_zero (f : MonomialIndex d →₀ k) :
    dworkIteratedSplittingProduct k p w f 0 = 1 := rfl
end Telescope
section ExponentDivisionKernel
end ExponentDivisionKernel
section IteratedKernel
def dworkQPow (s : ℕ) : ℕ := p ^ (Module.finrank (ZMod p) k * s)
def dworkQFrobeniusIteratedKernel (f : MonomialIndex d →₀ k) (s : ℕ) :
    InfiniteWeightedKernel (K := DworkCyclotomicField k p) (d := d) :=
  fun u v => overconvergentTateAlgebraCoefficient w u
    ((dworkQFrobenius k p w f)^[s] (unitMonomial k p w v))
end IteratedKernel
section FiniteTrace
end FiniteTrace
section CutoffTracePower
end CutoffTracePower
section TraceLimit
 def monomialCutoffFinset (bound : ℕ) : Finset (MonomialIndex d) :=
  (Finset.univ : Finset (WeightedCutoff w bound)).image Subtype.val
 def cutoffPowerDiagonal (f : MonomialIndex d →₀ k) (s bound : ℕ)
    (v : MonomialIndex d) : DworkCyclotomicField k p :=
  if hv : monomialWeight w v ≤ bound then
    ((cutoffKernel w (dworkQFrobeniusKernel k p w f) bound) ^ s) ⟨v, hv⟩ ⟨v, hv⟩ else 0
section MatrixBounds
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end MatrixBounds
def dworkSplittingDiagonal (f : MonomialIndex d →₀ k) (s : ℕ) (u : MonomialIndex d) :
    DworkCyclotomicField k p :=
  overconvergentTateAlgebraCoefficient w (monomialFrobenius (dworkQPow k p s - 1) u)
    (dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k * s))
end TraceLimit
section Evaluation
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
 instance dw5cNonarchimedeanRing : NonarchimedeanRing K :=
  { (inferInstance : IsTopologicalRing K) with
    is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }
def tateEvalTerm (g : OverconvergentTateAlgebra K d w) (x : Fin d → K) (u : MonomialIndex d) : K :=
  overconvergentTateAlgebraCoefficient w u g * ∏ i, x i ^ u i
omit [CompleteSpace K] in
theorem norm_tateEvalTerm (g : OverconvergentTateAlgebra K d w) {x : Fin d → K}
    (hx : ∀ i, ‖x i‖ = 1) (u : MonomialIndex d) :
    ‖tateEvalTerm w g x u‖ = ‖overconvergentTateAlgebraCoefficient w u g‖ := by
  rw [tateEvalTerm, norm_mul, norm_prod,
    Finset.prod_eq_one fun i _ => by rw [norm_pow, hx i, one_pow], mul_one]
omit [CompleteSpace K] in
theorem tendsto_overconvergentTateAlgebraCoefficient_cofinite
    (g : OverconvergentTateAlgebra K d w) :
    Tendsto (fun u : MonomialIndex d => overconvergentTateAlgebraCoefficient w u g)
      cofinite (nhds 0) := by
  have hzero := zero_at_infty g.toSeries
  rw [Filter.cocompact_eq_cofinite] at hzero
  exact hzero.comp (dw5cDiscreteMonomial_injective (d := d)).tendsto_cofinite
theorem summable_tateEvalTerm (g : OverconvergentTateAlgebra K d w) {x : Fin d → K}
    (hx : ∀ i, ‖x i‖ = 1) : Summable (tateEvalTerm w g x) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_zero_iff_norm_tendsto_zero.mp
    (tendsto_overconvergentTateAlgebraCoefficient_cofinite w g)).congr fun u => ?_
  exact (norm_tateEvalTerm w g hx u).symm
def tateEval (g : OverconvergentTateAlgebra K d w) (x : Fin d → K) : K :=
  ∑' u : MonomialIndex d, tateEvalTerm w g x u
theorem tateEval_add {x : Fin d → K} (hx : ∀ i, ‖x i‖ = 1)
    (g h : OverconvergentTateAlgebra K d w) :
    tateEval w (g + h) x = tateEval w g x + tateEval w h x := by
  rw [tateEval, tateEval, tateEval,
    ← (summable_tateEvalTerm w g hx).tsum_add (summable_tateEvalTerm w h hx)]
  refine tsum_congr fun u => ?_
  rw [tateEvalTerm, tateEvalTerm, tateEvalTerm, map_add, add_mul]
end Evaluation
section NuclearRootsOfUnity
end NuclearRootsOfUnity
section SplittingEvaluation
section GenericEval
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
omit [CompleteSpace K] in
theorem norm_coefficient_le (g : OverconvergentTateAlgebra K d w) (u : MonomialIndex d) :
    ‖overconvergentTateAlgebraCoefficient w u g‖ ≤ ‖g‖ := by
  rw [overconvergentTateAlgebraCoefficient_apply, seriesCoefficient_apply,
    ← OverconvergentTateAlgebra.norm_toSeries,
    ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm g.toSeries.toBCF _
omit [CompleteSpace K] in
theorem tateEval_smul {x : Fin d → K} (_hx : ∀ i, ‖x i‖ = 1) (c : K)
    (g : OverconvergentTateAlgebra K d w) :
    tateEval w (c • g) x = c * tateEval w g x := by
  rw [tateEval, tateEval, ← tsum_mul_left]
  refine tsum_congr fun u => ?_
  rw [tateEvalTerm, tateEvalTerm, map_smul, smul_eq_mul, mul_assoc]
omit [CompleteSpace K] in
theorem norm_tateEval_le (g : OverconvergentTateAlgebra K d w) {x : Fin d → K}
    (hx : ∀ i, ‖x i‖ = 1) : ‖tateEval w g x‖ ≤ ‖g‖ := by
  rw [tateEval]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg g) fun u => ?_
  rw [norm_tateEvalTerm w g hx u]
  exact norm_coefficient_le w g u
def tateEvalCLM {x : Fin d → K} (hx : ∀ i, ‖x i‖ = 1) :
    OverconvergentTateAlgebra K d w →L[K] K :=
  LinearMap.mkContinuous
    { toFun := fun g => tateEval w g x
      map_add' := tateEval_add w hx
      map_smul' := fun c g => tateEval_smul w hx c g } 1 (by
      intro g
      change ‖tateEval w g x‖ ≤ 1 * ‖g‖
      simpa only [one_mul] using norm_tateEval_le w g hx)
@[simp]
theorem tateEvalCLM_apply {x : Fin d → K} (hx : ∀ i, ‖x i‖ = 1)
    (g : OverconvergentTateAlgebra K d w) : tateEvalCLM w hx g = tateEval w g x := rfl
end GenericEval
end SplittingEvaluation
section FrobeniusSplitting
def residueFrobeniusInv : k ≃+* k := (frobeniusEquiv k p).symm
theorem residueFrobeniusInv_iterate_zero (m : ℕ) : (residueFrobeniusInv k p)^[m] (0 : k) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_zero]
def residueFrobeniusTwist (m : ℕ) (f : MonomialIndex d →₀ k) : MonomialIndex d →₀ k :=
  Finsupp.mapRange ((residueFrobeniusInv k p)^[m]) (residueFrobeniusInv_iterate_zero k p m) f
@[simp]
theorem residueFrobeniusTwist_apply (m : ℕ) (f : MonomialIndex d →₀ k) (u : MonomialIndex d) :
    residueFrobeniusTwist k p m f u = (residueFrobeniusInv k p)^[m] (f u) := rfl
end FrobeniusSplitting
section PhiFree
theorem tateDilation_add {m : ℕ} (hm : m ≠ 0) (g h : RamifiedOverconvergentTateAlgebra k p w) :
    tateDilation k p w m (g + h) = tateDilation k p w m g + tateDilation k p w m h := by
  classical
  refine tate_ext k p w fun u => ?_
  by_cases hu : ∃ v, monomialFrobenius m v = u
  · obtain ⟨v, rfl⟩ := hu
    rw [map_add, tateDilation_coefficient_dilated k p w hm,
      tateDilation_coefficient_dilated k p w hm, tateDilation_coefficient_dilated k p w hm,
      map_add]
  · rw [map_add, tateDilation_coefficient_of_not_dilated k p w m _ u hu,
      tateDilation_coefficient_of_not_dilated k p w m g u hu,
      tateDilation_coefficient_of_not_dilated k p w m h u hu, add_zero]
def tateDilationRingHom {m : ℕ} (hm : m ≠ 0) :
    RamifiedOverconvergentTateAlgebra k p w →+* RamifiedOverconvergentTateAlgebra k p w where
  toFun := tateDilation k p w m
  map_one' := tateDilation_one k p w hm
  map_mul' := tateDilation_mul k p w hm
  map_zero' := by
    refine tate_ext k p w fun u => ?_
    classical
    by_cases hu : ∃ v, monomialFrobenius m v = u
    · obtain ⟨v, rfl⟩ := hu
      rw [tateDilation_coefficient_dilated k p w hm, map_zero, map_zero]
    · rw [tateDilation_coefficient_of_not_dilated k p w m _ u hu, map_zero]
  map_add' := tateDilation_add k p w hm
@[simp]
theorem tateDilationRingHom_apply {m : ℕ} (hm : m ≠ 0)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    tateDilationRingHom k p w hm g = tateDilation k p w m g := rfl
end PhiFree
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] dw5cResiduePrimeAlgebra
variable {d : ℕ} (w : PositiveMonomialWeight d)
section TateBaseChange
variable (K : Type*) [Field K] [CharP K p] [Finite K] [Algebra k K]
 def tateBaseChangeSeries (g : RamifiedOverconvergentTateAlgebra k p w) :
    OverconvergentSeries (DworkCyclotomicField K p) d w where
  toFun U := dworkCyclotomicBaseChange k p K (g.toSeries U)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' :=
    ((dworkCyclotomicBaseChange_continuous k p K).tendsto' 0 0 (map_zero _)).comp
      (zero_at_infty g.toSeries)
def tateBaseChange (g : RamifiedOverconvergentTateAlgebra k p w) :
    RamifiedOverconvergentTateAlgebra K p w :=
  ⟨tateBaseChangeSeries k p w K g⟩
@[simp]
theorem tateBaseChange_coefficient (g : RamifiedOverconvergentTateAlgebra k p w)
    (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (tateBaseChange k p w K g)
      = dworkCyclotomicBaseChange k p K (overconvergentTateAlgebraCoefficient w u g) := rfl
theorem tateBaseChange_add (g h : RamifiedOverconvergentTateAlgebra k p w) :
    tateBaseChange k p w K (g + h) = tateBaseChange k p w K g + tateBaseChange k p w K h := by
  refine tate_ext K p w fun u => ?_
  rw [tateBaseChange_coefficient, map_add, map_add, map_add, tateBaseChange_coefficient,
    tateBaseChange_coefficient]
theorem tateBaseChange_zero :
    tateBaseChange k p w K (0 : RamifiedOverconvergentTateAlgebra k p w) = 0 := by
  refine tate_ext K p w fun u => ?_
  rw [tateBaseChange_coefficient, map_zero, map_zero, map_zero]
def tateBaseChangeAddHom :
    RamifiedOverconvergentTateAlgebra k p w →+ RamifiedOverconvergentTateAlgebra K p w where
  toFun := tateBaseChange k p w K
  map_zero' := tateBaseChange_zero k p w K
  map_add' := tateBaseChange_add k p w K
@[simp]
theorem tateBaseChangeAddHom_apply (g : RamifiedOverconvergentTateAlgebra k p w) :
    tateBaseChangeAddHom k p w K g = tateBaseChange k p w K g := rfl
def residueBaseChange (f : MonomialIndex d →₀ k) : MonomialIndex d →₀ K :=
  Finsupp.mapRange (algebraMap k K) (map_zero _) f
omit [Finite k] [Finite K] in
@[simp]
theorem residueBaseChange_apply (f : MonomialIndex d →₀ k) (u : MonomialIndex d) :
    residueBaseChange (k := k) (K := K) f u = algebraMap k K (f u) := rfl
end TateBaseChange
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] dw5cResiduePrimeAlgebra
variable {d : ℕ} (w : PositiveMonomialWeight d)
section AuxiliaryVariable
def dworkAuxiliaryPolynomial (f : MonomialIndex d →₀ k) : MonomialIndex (d + 1) →₀ k :=
  Finsupp.mapDomain (fun u : MonomialIndex d => Finsupp.cons 1 u) f
end AuxiliaryVariable
section TorusReindex
omit [Fact p.Prime] [Field k] [CharP k p] [Finite k] in
 def consPiEquiv (A : Type*) (n : ℕ) : (Fin (n + 1) → A) ≃ A × (Fin n → A) where
  toFun f := (f 0, Fin.tail f)
  invFun q := Fin.cons q.1 q.2
  left_inv f := Fin.cons_self_tail f
  right_inv q := by
    refine Prod.ext ?_ ?_ <;> simp
end TorusReindex
end FiniteFields.Dwork
end
end

section
noncomputable section
open Module Polynomial PowerSeries
namespace FiniteFields.LinearAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
def fredholmDeterminant (u : Module.End R M) : R[X] :=
  u.charpoly.reverse
def fredholmLogDerivative (u : Module.End R M) : R⟦X⟧ :=
  -(PowerSeries.derivative R (fredholmDeterminant u : R⟦X⟧)) *
    PowerSeries.invOfUnit (fredholmDeterminant u : R⟦X⟧) 1
section FiniteRank
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
def finiteRankFredholmDeterminant (a : M →ₗ[R] N) (b : N →ₗ[R] M) : R[X] :=
  fredholmDeterminant (b.comp a)
end FiniteRank
end FiniteFields.LinearAlgebra
end
end


