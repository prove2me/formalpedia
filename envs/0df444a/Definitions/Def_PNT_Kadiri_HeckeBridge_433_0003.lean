-- Prove2me | Definitions.Def_PNT_Kadiri_HeckeBridge_433_0003
-- name    : PNT_Kadiri_HeckeBridge_433_0003
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-12T12:29:00.679384+00:00
-- url     : https://prove2.me/theorems/03ccae7c-b27d-401f-b3ad-756af234964c
-- title:
--   Complete Hecke-to-zeta bridge, part 0003
-- statement:
--   Complete proved arithmetic and analytic lemmas connecting the Eisenstein Hecke L-function to ordinary Dirichlet L-functions and the Riemann zeta function. The final bridge transfers Hecke nonvanishing in Re(s) > 7/8 to zeta nonvanishing. Original hypotheses and proof bodies are retained; no unproved theorem is imported. Source modules: OAI.NumberTheory.DirichletL.Eisenstein.Rows, OAI.NumberTheory.DirichletL.EisensteinTheta, OAI.NumberTheory.DirichletL.Mellin.LocalNonvanishing, OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice, OAI.NumberTheory.DirichletL.Arithmetic.NormFiberMellin, OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs
-- source:
--   OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0; ported to Lean 4.33.1 and pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_HeckeSevenEighths
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0002

/- Complete Hecke-to-Dirichlet and zeta bridge lemmas.
Source: OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.Rows
section
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

section
open scoped BigOperators Classical MatrixGroups

section

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT


end

section
open ActualEisensteinCubic ConcreteTraceCRT

def integerLattice : Submodule ℤ ((Fin 2 × Fin 2) → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2 × Fin 2)))

instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0003_1 : DiscreteTopology integerLattice := by
  unfold integerLattice
  infer_instance

instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0003_2 : IsZLattice ℝ integerLattice := by
  unfold integerLattice
  infer_instance


end


end


end CubicEisenstein

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.EisensteinTheta
section
namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace SevenEighths.EisensteinTheta
open ThetaProduct

def normForm (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2

def shearEquiv : (ℤ × (ℤ × Fin 2)) ≃ (Fin 2 × (ℤ × ℤ)) where
  toFun n := (n.2.2, (n.1 - n.2.1, n.2.1))
  invFun p := (p.2.1 + p.2.2, (p.2.2, p.1))
  left_inv n := by simp
  right_inv p := by simp

def parityEquiv : (ℤ × ℤ) ≃ (Fin 2 × (ℤ × ℤ)) :=
  (Equiv.prodCongr (Equiv.refl ℤ) (Int.divModEquiv 2)).trans shearEquiv


theorem normForm_parity (a b L : ℝ) (hL : L ≠ 0) (e : Fin 2) (i j : ℤ) :
    normForm (a + L * (i + j)) (b + L * (2 * j + e)) =
      L ^ 2 * (i + xShift a b L e) ^ 2 +
        (3 * L ^ 2) * (j + yShift b L e) ^ 2 := by
  unfold normForm xShift yShift
  field_simp
  ring


theorem cosetTheta_hasSum (a b L : ℝ) (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * normForm (a + L * n.1) (b + L * n.2) * t) : ℂ))
      (∑ e : Fin 2, (parityPair a b L hL e).f t) := by
  let F : Fin 2 × (ℤ × ℤ) → ℝ := fun p =>
    Real.exp (-Real.pi * (L ^ 2 * (p.2.1 + xShift a b L p.1) ^ 2 +
      (3 * L ^ 2) * (p.2.2 + yShift b L p.1) ^ 2) * t)
  have hsum (e : Fin 2) : HasSum (fun n : ℤ × ℤ => (F (e, n) : ℂ))
      ((parityPair a b L hL e).f t) :=
    rectangularPair_hasSum (xShift a b L e) (yShift b L e) (L ^ 2) (3 * L ^ 2) (sq_pos_of_pos hL)
      (mul_pos (by norm_num) (sq_pos_of_pos hL)) ht
  have hreal (e : Fin 2) : Summable (fun n : ℤ × ℤ => F (e, n)) :=
    Complex.summable_ofReal.mp (hsum e).summable
  have hF : Summable F :=
    (summable_prod_of_nonneg (fun _ => (Real.exp_pos _).le)).2
      ⟨hreal, (hasSum_fintype _).summable⟩
  have hFC : Summable (fun p => (F p : ℂ)) := Complex.summable_ofReal.mpr hF
  have hid (p : Fin 2 × (ℤ × ℤ)) :
      Real.exp (-Real.pi * normForm
        (a + L * (parityEquiv.symm p).1) (b + L * (parityEquiv.symm p).2) * t) = F p := by
    change Real.exp (-Real.pi * normForm
      (a + L * ((p.2.1 + p.2.2 : ℤ) : ℝ))
      (b + L * ((p.2.2 * 2 + (p.1 : ℕ) : ℤ) : ℝ)) * t) = _
    push_cast
    rw [show (p.2.2 : ℝ) * 2 = 2 * p.2.2 from mul_comm _ _]
    rw [normForm_parity a b L hL.ne']
  apply parityEquiv.symm.hasSum_iff.mp
  change HasSum (fun p : Fin 2 × (ℤ × ℤ) =>
    (Real.exp (-Real.pi * normForm (a + L * (parityEquiv.symm p).1)
      (b + L * (parityEquiv.symm p).2) * t) : ℂ)) _
  simp_rw [hid]
  convert! hFC.hasSum using 1
  rw [hFC.tsum_prod, tsum_fintype]
  exact (Finset.sum_congr rfl (fun e _ => (hsum e).tsum_eq)).symm


def cosetConstant (a b L : ℝ) (hL : 0 < L) : ℂ :=
  ∑ e : Fin 2, (parityPair a b L hL e).f₀

theorem parityPair_f₀ (a b L : ℝ) (hL : 0 < L) (e : Fin 2) :
    (parityPair a b L hL e).f₀ =
      (if (xShift a b L e : UnitAddCircle) = 0 then 1 else 0) *
      (if (yShift b L e : UnitAddCircle) = 0 then 1 else 0) := rfl

theorem cosetConstant_eq (a b L : ℝ) (hL : 0 < L)
    (ha₀ : 0 ≤ a) (haL : a < L) (hb₀ : 0 ≤ b) (hbL : b < L) :
    cosetConstant a b L hL = if a = 0 ∧ b = 0 then 1 else 0 := by
  have htwo : 0 < 2 * L := by positivity
  have hy1 : yShift b L 1 ∈ Set.Ico (0 : ℝ) 1 := by
    simp only [yShift, Fin.val_one, Nat.cast_one, mul_one, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_one htwo).2
      linarith
  have hy1pos : 0 < yShift b L 1 := by
    simp only [yShift, Fin.val_one, Nat.cast_one, mul_one]
    exact div_pos (by linarith) htwo
  have hy1ne : (yShift b L 1 : UnitAddCircle) ≠ 0 := by
    intro h
    have := (AddCircle.coe_eq_zero_iff_of_mem_Ico hy1).mp h
    linarith
  have hy0 : yShift b L 0 ∈ Set.Ico (0 : ℝ) 1 := by
    simp only [yShift, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_one htwo).2
      linarith
  have hy0iff : (yShift b L 0 : UnitAddCircle) = 0 ↔ b = 0 := by
    rw [AddCircle.coe_eq_zero_iff_of_mem_Ico hy0]
    simp [yShift, div_eq_zero_iff, hL.ne']
  rw [cosetConstant, Fin.sum_univ_two, parityPair_f₀, parityPair_f₀,
    if_neg hy1ne, mul_zero, add_zero]
  by_cases hb : b = 0
  · subst b
    rw [if_pos (hy0iff.mpr rfl), mul_one]
    have hx : xShift a 0 L 0 = a / L := by
      simp only [xShift, sub_zero, Fin.val_zero, Nat.cast_zero, mul_zero]
      field_simp
    have hxmem : a / L ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨div_nonneg ha₀ hL.le, (div_lt_one hL).2 haL⟩
    have hxiff : (xShift a 0 L 0 : UnitAddCircle) = 0 ↔ a = 0 := by
      rw [hx, AddCircle.coe_eq_zero_iff_of_mem_Ico hxmem]
      simp [div_eq_zero_iff, hL.ne']
    simp only [hxiff, and_true]
  · rw [if_neg (fun h => hb (hy0iff.mp h)), mul_zero, if_neg (fun h => hb h.2)]


end SevenEighths.EisensteinTheta

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Mellin.LocalNonvanishing
section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar

open Filter Asymptotics


open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter

namespace ShortDraftHeckeBridge

abbrev O := ActualEisensteinSieve.O

noncomputable def normFiberCoeff (weight : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset, weight I

noncomputable def pairInverseCoeff
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ℕ → ℂ :=
  (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) ⍟
    (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ))

theorem normFiber_LSeries_eq_pair_inverse
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (s : ℂ) :
    LSeries (normFiberCoeff weight) s = LSeries (pairInverseCoeff χ ψ) s := by
  exact LSeries_congr (fun {n} hn => hcoeff n hn) s

theorem pair_inverse_euler_identity
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (s : ℂ) (hs : 1 < s.re) :
    χ.LFunction s * ψ.LFunction s * LSeries (pairInverseCoeff χ ψ) s = 1 := by
  have hχsum : LSeriesSummable (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s := by
    exact DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hψsum : LSeriesSummable (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s := by
    exact DirichletCharacter.LSeriesSummable_mul ψ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  rw [pairInverseCoeff, LSeries_convolution' hχsum hψsum,
    χ.LFunction_eq_LSeries hs, ψ.LFunction_eq_LSeries hs]
  have hχ := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hψ := DirichletCharacter.LSeries.mul_mu_eq_one ψ hs
  change LSeries (χ ·) s * LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s = 1 at hχ
  change LSeries (ψ ·) s * LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s = 1 at hψ
  calc
    LSeries (χ ·) s * LSeries (ψ ·) s *
      (LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s *
        LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s) =
      (LSeries (χ ·) s * LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s) *
      (LSeries (ψ ·) s * LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s) := by ring
    _ = 1 := by rw [hχ, hψ]; ring


end ShortDraftHeckeBridge


end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson


section
open scoped RealInnerProductSpace

def basisMap (w : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM +
    w • (Complex.ofRealCLM.comp Complex.imCLM)

@[simp] theorem basisMap_apply (w z : ℂ) :
    basisMap w z = (z.re : ℂ) + w * (z.im : ℂ) := rfl

def basisEquiv (w : ℂ) (hw : w.im ≠ 0) : ℂ ≃L[ℝ] ℂ where
  toLinearEquiv :=
    { toLinearMap := (basisMap w).toLinearMap
      invFun z := complexPoint (z.re - z.im * w.re / w.im) (z.im / w.im)
      left_inv z := by
        change complexPoint ((basisMap w z).re - (basisMap w z).im * w.re / w.im)
          ((basisMap w z).im / w.im) = z
        apply Complex.ext
        · simp only [basisMap_apply, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
            Complex.add_im, Complex.mul_im,  zero_add, complexPoint]
          field_simp [hw]
          ring
        · simp [basisMap_apply, complexPoint, hw]
      right_inv z := by
        change basisMap w (complexPoint (z.re - z.im * w.re / w.im)
          (z.im / w.im)) = z
        apply Complex.ext
        · simp only [basisMap_apply, complexPoint, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
          field_simp [hw]
          ring
        · simp only [basisMap_apply, complexPoint, Complex.add_im,
            Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero, zero_add]
          field_simp [hw] }
  continuous_toFun := (basisMap w).continuous
  continuous_invFun := by
    simp only [complexPoint_eq]
    fun_prop


def complexMulEquiv (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ) (Units.mk0 c hc)


def scaledBasisEquiv (w : ℂ) (hw : w.im ≠ 0) (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  (basisEquiv w hw).trans (complexMulEquiv c hc)


end

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace


def eisensteinLatticeMap (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  scaledBasisEquiv omega3 omega3_im_ne_zero c hc


end


end EisensteinSchwartzPoisson


end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Arithmetic.NormFiberMellin
section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar


open MulChar AddChar


namespace ShortDraftHeckeBridge

noncomputable def chiMinusThree : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

noncomputable def baseChangeWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * χ (Ideal.absNorm I)

theorem baseChangeWeight_prime {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ P = -χ (Ideal.absNorm P) := by
  rw [baseChangeWeight, hP.irreducible.moebius_eq]
  norm_num

noncomputable def invCharAF {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  (toArithmeticFunction (χ ·)).pmul (ArithmeticFunction.moebius : ArithmeticFunction ℂ)

theorem invCharAF_apply {q : ℕ} (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : n ≠ 0) :
    invCharAF χ n = χ n * (ArithmeticFunction.moebius n : ℂ) := by
  change ((toArithmeticFunction (χ ·)).pmul
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) n = _
  rw [ArithmeticFunction.pmul_apply]
  simp [toArithmeticFunction, hn]

private theorem invCharAF_mult {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (invCharAF χ).IsMultiplicative := by
  exact (χ.isMultiplicative_toArithmeticFunction).pmul
    (ArithmeticFunction.isMultiplicative_moebius.intCast)

noncomputable def pairAF {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  invCharAF χ * invCharAF ψ

theorem pairAF_mult {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    (pairAF χ ψ).IsMultiplicative :=
  (invCharAF_mult χ).mul (invCharAF_mult ψ)

theorem pairAF_eq_pairInverseCoeff {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (n : ℕ) : pairAF χ ψ n = pairInverseCoeff χ ψ n := by
  rw [pairAF, ← ArithmeticFunction.coe_mul]
  apply congrFun
  exact (LSeries.convolution_congr
    (fun {k} hk => invCharAF_apply χ hk)
    (fun {k} hk => invCharAF_apply ψ hk))

theorem normFiber_eq_pair_of_prime_powers
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hb : (toArithmeticFunction (normFiberCoeff weight)).IsMultiplicative)
    (hlocal : ∀ p k : ℕ, p.Prime →
      (toArithmeticFunction (normFiberCoeff weight)) (p ^ k) =
        pairAF χ ψ (p ^ k))
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff weight n = pairInverseCoeff χ ψ n := by
  have heq : toArithmeticFunction (normFiberCoeff weight) = pairAF χ ψ :=
    (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      _ hb _ (pairAF_mult χ ψ)).2 hlocal
  have h := congrFun (congrArg DFunLike.coe heq) n
  calc
    normFiberCoeff weight n = (toArithmeticFunction (normFiberCoeff weight)) n := by
      simp [toArithmeticFunction, hn]
    _ = pairAF χ ψ n := h
    _ = pairInverseCoeff χ ψ n := pairAF_eq_pairInverseCoeff χ ψ n

theorem pairAF_prime {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) {p : ℕ} (hp : p.Prime) :
    pairAF χ ψ p = -(χ p + ψ p) := by
  have h1χ : invCharAF χ 1 = 1 := (invCharAF_mult χ).map_one
  have h1ψ : invCharAF ψ 1 = 1 := (invCharAF_mult ψ).map_one
  have hpχ : invCharAF χ p = -χ p := by
    rw [invCharAF_apply χ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hpψ : invCharAF ψ p = -ψ p := by
    rw [invCharAF_apply ψ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [hp.divisors]
  have hnot : 1 ∉ ({p} : Finset ℕ) := by simpa using hp.ne_one.symm
  rw [Finset.sum_insert hnot, Finset.sum_singleton]
  simp [Nat.div_one, Nat.div_self hp.pos, h1χ, h1ψ, hpχ, hpψ]

theorem pairAF_prime_sq {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) {p : ℕ} (hp : p.Prime) :
    pairAF χ ψ (p ^ 2) = χ p * ψ p := by
  have h1χ : invCharAF χ 1 = 1 := (invCharAF_mult χ).map_one
  have h1ψ : invCharAF ψ 1 = 1 := (invCharAF_mult ψ).map_one
  have hpχ : invCharAF χ p = -χ p := by
    rw [invCharAF_apply χ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hpψ : invCharAF ψ p = -ψ p := by
    rw [invCharAF_apply ψ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hp2χ : invCharAF χ (p ^ 2) = 0 := by
    rw [invCharAF_apply χ (pow_ne_zero 2 hp.ne_zero),
      ArithmeticFunction.moebius_apply_prime_pow hp (by decide)]
    simp
  have hp2ψ : invCharAF ψ (p ^ 2) = 0 := by
    rw [invCharAF_apply ψ (pow_ne_zero 2 hp.ne_zero),
      ArithmeticFunction.moebius_apply_prime_pow hp (by decide)]
    simp
  have hdiv : (p ^ 2).divisors = ({1, p, p ^ 2} : Finset ℕ) := by
    ext x
    rw [Nat.mem_divisors_prime_pow hp 2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj, rfl⟩
      interval_cases j <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by decide, by simp⟩
      · exact ⟨1, by decide, by simp⟩
      · exact ⟨2, by decide, by simp⟩
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [hdiv]
  have hpge : 2 ≤ p := hp.two_le
  have h1p2 : 1 ≠ p ^ 2 := by nlinarith
  have hpp2 : p ≠ p ^ 2 := by nlinarith
  have hnot1 : 1 ∉ ({p, p ^ 2} : Finset ℕ) := by
    simp [hp.ne_one.symm, h1p2]
  have hnotp : p ∉ ({p ^ 2} : Finset ℕ) := by
    simp [hpp2]
  rw [Finset.sum_insert hnot1, Finset.sum_insert hnotp, Finset.sum_singleton]
  have hdivp : p ^ 2 / p = p := by simp [pow_two, hp.pos]
  simp [Nat.div_one, hdivp, h1χ,  hpχ, hpψ, hp2χ, hp2ψ]

theorem chiMinusThree_two : chiMinusThree (2 : ℕ) = -1 := by
  have h3 : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  change ((quadraticChar (ZMod 3) (2 : ZMod 3) : ℤ) : ℂ) = -1
  rw [quadraticChar_eq_pow_of_char_ne_two h3 h2]
  simp [h21]


end ShortDraftHeckeBridge


end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs
section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap


open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT UniqueFactorizationMonoid CompletedGauss


abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}


end CubicEisenstein

end

end OAI

end


