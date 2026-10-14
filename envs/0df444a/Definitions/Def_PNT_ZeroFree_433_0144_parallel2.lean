-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0144_parallel2
-- name    : PNT_ZeroFree_433_0144_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:41:30.124317+00:00
-- url     : https://prove2.me/theorems/78f5e20c-08a3-44e5-bf0e-5ae817599be6
-- title:
--   Zero-free region foundations: QuadraticSieve.ProductColumns [0144_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.ProductColumns
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/ProductColumns.lean#L432-L588

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0056_1
import Definitions.Def_PNT_ZeroFree_433_0058
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0090
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel1
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel2_1
import Definitions.Def_PNT_ZeroFree_433_0143_parallel1
import Definitions.Def_PNT_ZeroFree_433_0168_parallel1
import Definitions.Def_PNT_ZeroFree_433_0181_parallel1
import Definitions.Def_PNT_ZeroFree_433_0195_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/ProductColumns.lean
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


namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

theorem squarefree_all_column_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hinj : Function.Injective cols) (X K : ℝ)
    (hcols : ∀j,Squarefree (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤X) (a : n → ℂ) :
    (∑k : idealRange K,‖∑j,quadraticRow k.val (primaryGenerator (cols j))*a j‖^2)≤
      4*sieveNorm X K*∑j,‖a j‖^2 := by
  classical
  let sector (E : fixedBadPrimes.powerset) := {j : n // badPrimeSector (cols j)=E}
  have hsector (E : fixedBadPrimes.powerset) :
      (∑k : idealRange K,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2)≤
        sieveNorm X K*∑j : sector E,‖a j.val‖^2 := by
    let good : sector E → Ideal O := fun j => goodSquarefreePart (cols j.val)
    have hg : Function.Injective good := by
      intro i j hij
      apply Subtype.ext
      apply hinj
      exact goodSquarefreePart_injective_on_sector _ _ (hcols i.val).1 (hcols j.val).1
        (i.property.trans j.property.symm) hij
    have hgood (j : sector E) : Admissible (good j) ∧ (Ideal.absNorm (good j):ℝ)≤X :=
      mem_idealRange.mp (goodSquarefreePart_mem_idealRange _ (hcols j.val).1 X (hcols j.val).2)
    let B : Matrix (sector E) (idealRange K) ℂ := fun j k => quadraticRow k.val (primaryGenerator (good j))
    have hB := family_squared_norm_le good (fun k : idealRange K => k.val) hg Subtype.val_injective X K
      hgood (fun k => mem_idealRange.mp k.property)
    change ‖FiniteSieveOperator.operator B‖^2≤sieveNorm X K at hB
    have hBT : B.conjTranspose=(fun k j => quadraticRow k.val (primaryGenerator (good j))) := by
      ext k j
      exact canonical_quadraticRow_star _ (mem_idealRange.mp k.property).1 _
    have he := FiniteSieveOperator.energy_bound B.conjTranspose (fun j : sector E => a j.val)
    rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
    have hrow (k : idealRange K) :
        (∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val)=
          quadraticRow k.val (primaryGenerator (sectorBadIdeal E))*
          ∑j : sector E,quadraticRow k.val (primaryGenerator (good j))*a j.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hj := sector_bad_good_product (cols j.val) (hcols j.val).1 E j.property
      have hq : quadraticRow k.val (primaryGenerator (cols j.val))=
          quadraticRow k.val (primaryGenerator (sectorBadIdeal E))*quadraticRow k.val (primaryGenerator (good j)) := by
        conv_lhs => rw [←hj]
        rw [primaryGenerator_mul,canonical_quadraticRow_argument_mul _ (mem_idealRange.mp k.property).1]
      rw [hq]
      ring
    have hpoint (k : idealRange K) :
        ‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2≤
          ‖∑j : sector E,quadraticRow k.val (primaryGenerator (good j))*a j.val‖^2 := by
      rw [hrow,norm_mul]
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    exact (Finset.sum_le_sum (fun k _ => hpoint k)).trans
      (he.trans (mul_le_mul_of_nonneg_right hB (by positivity)))
  have hpoint (k : idealRange K) :
      ‖∑j,quadraticRow k.val (primaryGenerator (cols j))*a j‖^2≤
        4*∑E : fixedBadPrimes.powerset,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 := by
    rw [←Fintype.sum_fiberwise (fun j => badPrimeSector (cols j))]
    have hn := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sum_le Finset.univ (fun E : fixedBadPrimes.powerset =>
        ∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val)) 2
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : fixedBadPrimes.powerset => (1:ℝ))
      (fun E : fixedBadPrimes.powerset => ‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖)
    have hcard : Fintype.card fixedBadPrimes.powerset=4 := by
      rw [Fintype.card_coe,fixedBadPrimes_powerset_card]
    apply hn.trans
    simpa [hcard,fixedBadPrimes_card] using hc
  calc
    _ ≤ ∑k : idealRange K,4*∑E : fixedBadPrimes.powerset,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = 4*∑E : fixedBadPrimes.powerset,∑k : idealRange K,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ 4*∑E : fixedBadPrimes.powerset,sieveNorm X K*∑j : sector E,‖a j.val‖^2 := by
      gcongr with E
      exact hsector E
    _ = _ := by
      have he : (∑E : fixedBadPrimes.powerset,∑j : sector E,‖a j.val‖^2)=∑j,‖a j‖^2 :=
        Fintype.sum_fiberwise (fun j => badPrimeSector (cols j)) (fun j => ‖a j‖^2)
      rw [←Finset.mul_sum,he]
      ring

theorem columnSquareFiber_nonzero_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (I : columnSquareFiber S A) :
    Squarefree (squarefreePart I.val) ∧
      (Ideal.absNorm (squarefreePart I.val):ℝ)≤X/(Ideal.absNorm A:ℝ)^2 := by
  have hi := hS I.val (Finset.mem_filter.mp I.property).1
  have hp := squarePart_ne_zero hi.1
  have ha := (Finset.mem_filter.mp I.property).2
  have hAz : A≠0 := by rw [←ha]; exact hp
  have hAn : 0<(Ideal.absNorm A:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  refine ⟨squarefree_squarefreePart _,(le_div_iff₀ (sq_pos_of_pos hAn)).mpr ?_⟩
  have hn : (Ideal.absNorm A:ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
    have hh : (Ideal.absNorm (squarePart I.val):ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
      exact_mod_cast norm_decomposition I.val
    simpa only [ha] using hh
  nlinarith

theorem columnSquareFiber_nonzero_card (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
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
    exact (columnSquareFiber_nonzero_bounds S X hS A ⟨J,hJ⟩).1.ne_zero
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_nonzero_bounds S X hS A ⟨J,hJ⟩).2

theorem columnSquareFiber_all_energy (S : Finset (Ideal O)) (X K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X)
    (A : Ideal O) (a : Ideal O → ℂ) :
    (∑k : idealRange K, ‖∑I∈columnSquareFiber S A,
      quadraticRow k.val (primaryGenerator I)*a I‖^2) ≤
      4*sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K *
        ∑I∈columnSquareFiber S A,‖a I‖^2 := by
  let T := columnSquareFiber S A
  have he := squarefree_all_column_energy
    (fun I : T => squarefreePart I.val) (columnSquareFiber_injective S A)
    (X/(Ideal.absNorm A:ℝ)^2) K (fun I => columnSquareFiber_nonzero_bounds S X hS A I)
    (fun I : T => a I.val)
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
    he


end CanonicalQuadraticSieve

end

end OAI

end


