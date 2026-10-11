-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0146_parallel1
-- name    : PNT_ZeroFree_433_0146_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:34:59.726402+00:00
-- url     : https://prove2.me/theorems/fb12f9e1-0175-4c6f-ac2f-5449d3aee168
-- title:
--   Zero-free region foundations: CubicSieve.CubeBlocks [0146_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.CubeBlocks
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CubeBlocks.lean#L368-L564

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0050
import Definitions.Def_PNT_ZeroFree_433_0056_1
import Definitions.Def_PNT_ZeroFree_433_0058
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0079_1_1_1
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0143_parallel1
import Definitions.Def_PNT_ZeroFree_433_0145_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel2
import Definitions.Def_PNT_ZeroFree_433_0242_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CubeBlocks.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
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
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius supportConjugateSum)
open ConcreteTraceCRT (eisEmbedding)

def conjugateMonoid (Ψ : O→*ℂ) : O→*ℂ where
  toFun x := star (Ψ x)
  map_one' := by simp
  map_mul' x y := by simp [map_mul]

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

def mobiusRow (F : Finset ι) (Ψ : O→*ℂ) (m : O) (H : Finset ι→ℂ) (z : O) : ℂ :=
  ∑S∈F.powerset,supportMobius (fun i => Ideal.span {p i}) S*
    inputColumn p Ψ m 1 H S*finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S z

lemma star_mobiusRow (F : Finset ι) (Ψ : O→*ℂ) (m : O) (H : Finset ι→ℂ) (z : O) :
    star (mobiusRow p hg F Ψ m H z)=
      inputConjugateRow p hg F (conjugateMonoid Ψ) m 1 1 (fun S => star (H S)) z := by
  unfold mobiusRow inputConjugateRow supportConjugateSum
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hm : star (rowCoprimeMask (fun i => Ideal.span {p i}) S m)=rowCoprimeMask (fun i => Ideal.span {p i}) S m := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  simp only [star_mul,FirstCauchyArithmetic.star_supportMobius,
    inputColumn,secondInputCoefficient,conjugateMonoid,MonoidHom.coe_mk,OneHom.coe_mk,
    mul_one,hm]
  simp only [finiteSquarefreeRow,Finset.prod_const_one,one_pow,map_one,mul_one]
  ring

lemma mobiusRow_norm (F : Finset ι) (Ψ : O→*ℂ) (m : O) (H : Finset ι→ℂ) (z : O) :
    ‖mobiusRow p hg F Ψ m H z‖=
      ‖inputConjugateRow p hg F (conjugateMonoid Ψ) m 1 1 (fun S => star (H S)) z‖ := by
  rw [←star_mobiusRow p hg F Ψ m H z,norm_star]

variable (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
include hc

theorem mobiusRow_smoothed_source (F : Finset ι) (Ψ : O→*ℂ) (m : O)
    (H : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y)
    (K : Finset ι→Finset ι→Finset O) :
    (∑'z:O,W (‖eisEmbedding z‖^2/Y)*(‖mobiusRow p hg F Ψ m H z‖^2:ℝ))=
      truncatedSecondSource p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y (fun G E => (K G E).erase 0)+
      truncatedSecondZero p hg F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y K+
      secondSourceTail p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y K := by
  simp_rw [mobiusRow_norm p hg]
  rw [inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F
    (conjugateMonoid Ψ) m 1 1 (fun S => star (H S)) W Y hY K]
  rw [truncatedSecondSource_eq_nonzero_add_zero p hp hg hinj]

theorem mobiusRow_finite_source (F : Finset ι) (Ψ : O→*ℂ) (m : O)
    (H : Finset ι→ℂ) (Y : ℝ) (hY : 0<Y) (T : Finset O)
    (hT : ∀z∈T,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Y) (hT0 : ∀z∈T,z≠0)
    (K : Finset ι→Finset ι→Finset O) :
    (∑z∈T,‖mobiusRow p hg F Ψ m H z‖^2)≤
      ‖truncatedSecondSource p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) rowMajorant Y (fun G E => (K G E).erase 0)‖+
      (truncatedSecondZero p hg F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) rowMajorant Y K).re+
      ‖secondSourceTail p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) rowMajorant Y K‖-‖H ∅‖^2 := by
  have hb := finite_nonzero_row_energy_le_majorant
    (inputConjugateRow p hg F (conjugateMonoid Ψ) m 1 1 (fun S => star (H S))) T Y hY hT hT0
  rw [inputConjugateRow_nonzero_correction p hg F (conjugateMonoid Ψ) m 1 1
    (fun S => star (H S)) Y hY] at hb
  have he := mobiusRow_smoothed_source p hg hp hinj hc F Ψ m H rowMajorant Y hY K
  simp_rw [mobiusRow_norm p hg] at he ⊢
  change (∑'z:O,rowMajorant (‖eisEmbedding z‖^2/Y)*
    (‖inputConjugateRow p hg F (conjugateMonoid Ψ) m 1 1 (fun S => star (H S)) z‖^2:ℝ))=_ at he
  rw [he,Complex.sub_re,Complex.add_re,Complex.add_re,Complex.ofReal_re,norm_star] at hb
  exact hb.trans (by gcongr <;> exact Complex.re_le_norm _)

end InitialMeanSquare

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid

def PowerfulIdeal (I : Ideal O) : Prop :=
  I≠0 ∧ ∀P∈normalizedFactors I, 2≤(normalizedFactors I).count P

theorem powerful_squarefree_dvd_squarePart (I : Ideal O) (hI : PowerfulIdeal I) :
    squarefreePart I ∣ squarePart I := by
  have ha := squarePart_ne_zero hI.1
  have hb := (squarefree_squarefreePart I).ne_zero
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hb ha).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  have he := congrArg normalizedFactors (squarePart_sq_mul_squarefreePart I)
  rw [normalizedFactors_mul (pow_ne_zero _ ha) hb,normalizedFactors_pow] at he
  have hc := congrArg (Multiset.count P) he
  simp only [Multiset.count_add,Multiset.count_nsmul] at hc
  have hsf := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hb).mp (squarefree_squarefreePart I)) P
  by_cases hzero : (normalizedFactors (squarefreePart I)).count P=0
  · omega
  · have hm : P∈normalizedFactors I := Multiset.count_pos.mp (by omega)
    have hp := hI.2 P hm
    omega

theorem powerful_exists_square_cube (I : Ideal O) (hI : PowerfulIdeal I) :
    ∃A : Ideal O, A≠0 ∧ A^2*squarefreePart I^3=I := by
  obtain ⟨A,hA⟩ := powerful_squarefree_dvd_squarePart I hI
  have ha : A≠0 := by
    intro hz
    have h := squarePart_ne_zero hI.1
    apply h
    rw [hA,hz,mul_zero]
  refine ⟨A,ha,?_⟩
  calc
    _ = (squarefreePart I*A)^2*squarefreePart I := by ring
    _ = squarePart I^2*squarefreePart I := by rw [←hA]
    _ = I := squarePart_sq_mul_squarefreePart I

def powerfulBase (I : Ideal O) : Ideal O :=
  if hI : PowerfulIdeal I then (powerful_exists_square_cube I hI).choose else 0

theorem powerfulBase_spec (I : Ideal O) (hI : PowerfulIdeal I) :
    powerfulBase I≠0 ∧ powerfulBase I^2*squarefreePart I^3=I := by
  rw [powerfulBase,dif_pos hI]
  exact (powerful_exists_square_cube I hI).choose_spec

theorem powerfulBase_injective_on_fiber (I J : Ideal O)
    (hI : PowerfulIdeal I) (hJ : PowerfulIdeal J)
    (hb : squarefreePart I=squarefreePart J) (ha : powerfulBase I=powerfulBase J) : I=J := by
  rw [←(powerfulBase_spec I hI).2,←(powerfulBase_spec J hJ).2,ha,hb]

theorem powerfulBase_norm_bound (I : Ideal O) (hI : PowerfulIdeal I) (X : ℝ)
    (hX : (Ideal.absNorm I:ℝ)≤X) :
    1≤(Ideal.absNorm (squarefreePart I):ℝ) ∧
    (Ideal.absNorm (squarefreePart I):ℝ)≤X ∧
    (Ideal.absNorm (powerfulBase I):ℝ)≤Real.sqrt X/(Ideal.absNorm (squarefreePart I):ℝ) := by
  have ha := (powerfulBase_spec I hI).1
  have hb := (squarefree_squarefreePart I).ne_zero
  have ha1 : 1≤(Ideal.absNorm (powerfulBase I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => ha (Ideal.absNorm_eq_zero_iff.mp hz))
  have hb1 : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hb (Ideal.absNorm_eq_zero_iff.mp hz))
  have hnorm : (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3=(Ideal.absNorm I:ℝ) := by
    have h := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (powerfulBase_spec I hI).2
    simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using h
  have hX0 : 0≤X := (Nat.cast_nonneg _).trans hX
  have hb2 : (Ideal.absNorm (squarefreePart I):ℝ)≤(Ideal.absNorm (squarefreePart I):ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show (1:ℕ)≤3 by decide)
  have hab : ((Ideal.absNorm (powerfulBase I):ℝ)*(Ideal.absNorm (squarefreePart I):ℝ))^2≤X := by
    calc
      _ = (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^2 := by ring
      _ ≤ (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by decide)) (sq_nonneg _)
      _ ≤ X := hnorm.trans_le hX
  have hbX : (Ideal.absNorm (squarefreePart I):ℝ)≤X := by
    calc
      _ ≤ (Ideal.absNorm (squarefreePart I):ℝ)^3 := hb2
      _ ≤ (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3 :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ ha1)
      _ ≤ X := hnorm.trans_le hX
  refine ⟨hb1,hbX,?_⟩
  apply (le_div_iff₀ (by linarith : 0<(Ideal.absNorm (squarefreePart I):ℝ))).mpr
  nlinarith [Real.sq_sqrt hX0,Real.sqrt_nonneg X]

end

open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel

theorem powerful_fiber_count (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X)
    (B : Ideal O) (hB : B∈S.image squarefreePart) :
    ((S.filter (fun I => squarefreePart I=B)).card:ℝ)≤128*Real.sqrt X/(Ideal.absNorm B:ℝ) := by
  obtain ⟨I,hI,hIB⟩ := Finset.mem_image.mp hB
  have hi := hS I hI
  have hnorm := powerfulBase_norm_bound I hi.1 X hi.2
  rw [hIB] at hnorm
  have hAb : 1≤(Ideal.absNorm (powerfulBase I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => (powerfulBase_spec I hi.1).1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤Real.sqrt X/(Ideal.absNorm B:ℝ) := hAb.trans hnorm.2.2
  let T := S.filter (fun I => squarefreePart I=B)
  have hinj : Set.InjOn powerfulBase T := by
    intro J hJ lengthScale hL he
    exact powerfulBase_injective_on_fiber J lengthScale (hS J (Finset.mem_filter.mp hJ).1).1
      (hS lengthScale (Finset.mem_filter.mp hL).1).1
      ((Finset.mem_filter.mp hJ).2.trans (Finset.mem_filter.mp hL).2.symm) he
  have hcard : (T.image powerfulBase).card=T.card := Finset.card_image_iff.mpr hinj
  have hcount := DescentFiberCost.finite_ideal_count_real (T.image powerfulBase)
    (Real.sqrt X/(Ideal.absNorm B:ℝ)) hscale (fun J hJ => by
      obtain ⟨lengthScale,hL,rfl⟩ := Finset.mem_image.mp hJ
      exact (powerfulBase_spec lengthScale (hS lengthScale (Finset.mem_filter.mp hL).1).1).1) (fun J hJ => by
      obtain ⟨lengthScale,hL,rfl⟩ := Finset.mem_image.mp hJ
      have hp := powerfulBase_norm_bound lengthScale (hS lengthScale (Finset.mem_filter.mp hL).1).1 X
        (hS lengthScale (Finset.mem_filter.mp hL).1).2
      simpa only [(Finset.mem_filter.mp hL).2] using hp.2.2)
  rw [hcard] at hcount
  simpa only [mul_div_assoc] using hcount


end CompletedGauss

end

end OAI

end


