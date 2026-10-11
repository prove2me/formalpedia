-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0143_parallel1
-- name    : PNT_ZeroFree_433_0143_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:15:01.247983+00:00
-- url     : https://prove2.me/theorems/21a9f56c-0d83-4a4e-b318-c7cbf405fadb
-- title:
--   Zero-free region foundations: MeanSquare.TransformedColumns [0143_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.TransformedColumns
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/TransformedColumns.lean#L85-L583

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0050
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0056_1
import Definitions.Def_PNT_ZeroFree_433_0058
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0090
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0144_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel1
import Definitions.Def_PNT_ZeroFree_433_0192_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/TransformedColumns.lean
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

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open MixedCrossSeparation (columnCoefficient)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def inputColumn (Ψ : O→*ℂ) (b d : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏i∈S,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*H S

def transformedColumn (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S*Ψ (∏i∈S,p i)*
    rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d)*
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h*H S

omit [DecidableEq ι] in
lemma inputColumn_eq (Ψ : O→*ℂ) (b d : O) (H : Finset ι→ℂ) (S : Finset ι) :
    inputColumn p Ψ b d H S=secondInputCoefficient p hg Ψ (b*d) 1 1 H S := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simp only [inputColumn,secondInputCoefficient,hr,one_pow,mul_one]

lemma transformedColumn_eq (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    transformedColumn p hp hcop hg Ψ b d h H S=
      secondPreColumn p hp hcop hg Ψ (b*d) 1 1 d h H S := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simp only [transformedColumn,secondPreColumn,hr,one_pow,mul_one]

theorem transformedColumn_union (hpr : ∀i,lambda^2∣p i-1)
    (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ)
    (V N : Finset ι) (hVN : Disjoint V N) :
    transformedColumn p hp hcop hg Ψ b d h H (V∪N)=
      transformedColumn p hp hcop hg Ψ b d h (fun _ => 1) V *
      secondChildColumn p hp hcop hg Ψ b (d*∏i∈V,p i) (d*h)
        (fun U => H (V∪U)) N := by
  simp_rw [transformedColumn_eq p hp hcop hg]
  simpa only [mul_one,one_mul] using secondPreColumn_union p hp hcop hg hpr
    Ψ b 1 1 1 d h H V N hVN

def initialPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) : ℂ :=
  ∑S∈F.powerset,∑T∈F.powerset,if Disjoint S T then
    star (supportMobius (fun i => Ideal.span {p i}) S*inputColumn p Ψ₁ b d H₁ S)*
      (supportMobius (fun i => Ideal.span {p i}) T*inputColumn p Ψ₂ b d H₂ T)*
      activeGaussRowFactor p hp hinj hg T S d h else 0

lemma initialPair_eq (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) :
    initialPair p hp hg hinj F Ψ₁ Ψ₂ b d h H₁ H₂=
      secondActualPair p hp hg hinj F Ψ₁ Ψ₂ b 1 1 1 d h H₁ H₂ := by
  simp only [initialPair,secondActualPair,inputColumn_eq p hg,mul_one]

def childSum (F V : Finset ι) (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) : ℂ :=
  ∑N∈F.powerset,secondChildColumn p hp hcop hg Ψ b (d*∏i∈V,p i) (d*h)
    (fun U => H (V∪U)) N

lemma childSum_eq (F V : Finset ι) (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) :
    childSum p hp hcop hg F V Ψ b d h H=
      secondChildSum p hp hcop hg F V Ψ b 1 1 1 d h H := by
  rw [secondChildSum_fixed_pool]
  simp only [childSum,mul_one,one_mul]

theorem initialPair_eq_children (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr : ∀i,lambda^2∣p i-1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) :
    initialPair p hp hg hinj F Ψ₁ Ψ₂ b d h H₁ H₂=
      ∑z : SecondRayIndex,∑V∈F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ b 1 1 1 d h (z,V)*
        star (childSum p hp hcop hg F V (secondRayMinus Ψ₁ z) b d h H₁)*
        childSum p hp hcop hg F V (secondRayPlus Ψ₂ z) b d (-h) H₂ := by
  simp_rw [initialPair_eq p hp hg,childSum_eq p hp hcop hg]
  exact secondActualPair_eq_children p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ b 1 1 1 d h H₁ H₂

end InitialMeanSquare


open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic


theorem ideal_reciprocal_cauchy (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (v : Ideal O → ℂ) :
    ‖∑I∈S,v I‖^2≤(∑I∈S,1/(Ideal.absNorm I:ℝ))*
      (∑I∈S,(Ideal.absNorm I:ℝ)*‖v I‖^2) := by
  have hpos (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S v) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun I hI => by positivity) (fun I hI => by positivity)
  intro I hI
  exact le_of_eq (by field_simp [(hpos I hI).ne'])

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

def columnSquareFiber (S : Finset (Ideal O)) (A : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => squarePart I=A)

theorem columnSquareFiber_injective (S : Finset (Ideal O)) (A : Ideal O) :
    Function.Injective (fun I : columnSquareFiber S A => squarefreePart I.val) := by
  intro I J he
  change squarefreePart I.val=squarefreePart J.val at he
  apply Subtype.ext
  have hi := (Finset.mem_filter.mp I.property).2
  have hj := (Finset.mem_filter.mp J.property).2
  calc
    I.val = A^2*squarefreePart I.val := by simpa only [hi] using (squarePart_sq_mul_squarefreePart I.val).symm
    _ = A^2*squarefreePart J.val := by rw [he]
    _ = J.val := by simpa only [hj] using squarePart_sq_mul_squarefreePart J.val

theorem columnSquareFiber_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (I : columnSquareFiber S A) :
    Admissible (squarefreePart I.val) ∧
      (Ideal.absNorm (squarefreePart I.val):ℝ)≤X/(Ideal.absNorm A:ℝ)^2 := by
  have hi := hS I.val (Finset.mem_filter.mp I.property).1
  have hp := (supported_square_parts I.val).mp hi.1
  have ha := (Finset.mem_filter.mp I.property).2
  have hAz : A≠0 := by rw [←ha]; exact hp.1.1
  have hAn : 0<(Ideal.absNorm A:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  refine ⟨hp.2,(le_div_iff₀ (sq_pos_of_pos hAn)).mpr ?_⟩
  have hn : (Ideal.absNorm A:ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
    have hh : (Ideal.absNorm (squarePart I.val):ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
      exact_mod_cast norm_decomposition I.val
    simpa only [ha] using hh
  nlinarith

theorem columnSquareFiber_card (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hscale : 1≤X/(Ideal.absNorm A:ℝ)^2) :
    ((columnSquareFiber S A).card:ℝ)≤128*(X/(Ideal.absNorm A:ℝ)^2) := by
  let T := (columnSquareFiber S A).image squarefreePart
  have hcard : T.card=(columnSquareFiber S A).card := Finset.card_image_iff.mpr (by
    intro I hI J hJ he
    have hh : (⟨I,hI⟩:columnSquareFiber S A)=(⟨J,hJ⟩:columnSquareFiber S A) :=
      columnSquareFiber_injective S A he
    exact congrArg Subtype.val hh)
  rw [←hcard]
  apply DescentFiberCost.finite_ideal_count_real T _ hscale
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).1.1
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).2

theorem columnSquareFiber_energy (S : Finset (Ideal O)) (X K : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X)
    (A : Ideal O) (a : Ideal O → ℂ) :
    (∑k : idealRange K, ‖∑I∈columnSquareFiber S A,
      quadraticRow k.val (primaryGenerator I)*a I‖^2) ≤
      sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K *
        ∑I∈columnSquareFiber S A,‖a I‖^2 := by
  let T := columnSquareFiber S A
  let B : Matrix T (idealRange K) ℂ := fun I k => quadraticRow k.val (primaryGenerator (squarefreePart I.val))
  have hB : ‖FiniteSieveOperator.operator B‖^2≤sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K := by
    apply family_squared_norm_le (fun I : T => squarefreePart I.val) (fun k : idealRange K => k.val)
      (columnSquareFiber_injective S A) Subtype.val_injective
    · intro I
      exact columnSquareFiber_bounds S X hS A I
    · intro k
      exact mem_idealRange.mp k.property
  have hBT : B.conjTranspose=(fun k I => quadraticRow k.val (primaryGenerator (squarefreePart I.val))) := by
    ext k I
    exact canonical_quadraticRow_star k.val (mem_idealRange.mp k.property).1 _
  have he := FiniteSieveOperator.energy_bound B.conjTranspose (fun I : T => a I.val)
  rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
  have hm (k : idealRange K) :
      ‖∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val‖^2 ≤
        ‖∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val‖^2 := by
    have hrow : (∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val)=
        idealZeroMask k.val (primaryGenerator A)*
        ∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      have hi := (Finset.mem_filter.mp I.property).2
      have hq : quadraticRow k.val (primaryGenerator I.val)=
          idealZeroMask k.val (primaryGenerator A)*quadraticRow k.val (primaryGenerator (squarefreePart I.val)) := by
        have hh := canonical_quadraticRow_primary_squarefree k.val (mem_idealRange.mp k.property).1
          (squarePart I.val) (squarefreePart I.val)
        rw [squarePart_sq_mul_squarefreePart,hi] at hh
        exact hh
      rw [hq]
      ring
    rw [hrow,norm_mul,mul_pow]
    have hmask : ‖idealZeroMask k.val (primaryGenerator A)‖^2≤1 := by
      unfold idealZeroMask
      split_ifs <;> norm_num
    exact mul_le_of_le_one_left (sq_nonneg _) hmask
  have hr (k : idealRange K) :
      (∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val :=
    (Finset.sum_coe_sort T _).symm
  simp_rw [hr]
  rw [←Finset.sum_coe_sort T (fun I => ‖a I‖^2)]
  exact (Finset.sum_le_sum (fun k _ => hm k)).trans
    (he.trans (mul_le_mul_of_nonneg_right hB (by positivity)))

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

theorem columnSquareParts_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hA : A∈S.image squarePart) :
    A≠0 ∧ 1≤(Ideal.absNorm A:ℝ) ∧ (Ideal.absNorm A:ℝ)≤X ∧ 1≤X/(Ideal.absNorm A:ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  have hi := hS I hI
  have hp := (supported_square_parts I).mp hi.1
  have ha : 1≤(Ideal.absNorm (squarePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hp.1.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hd : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hp.2.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn : (Ideal.absNorm (squarePart I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)=(Ideal.absNorm I:ℝ) := by
    exact_mod_cast norm_decomposition I
  refine ⟨hp.1.1,ha,by nlinarith,?_⟩
  apply (le_div_iff₀ (by positivity : 0<(Ideal.absNorm (squarePart I):ℝ)^2)).mpr
  nlinarith


end CanonicalQuadraticSieve

end

end OAI

end


