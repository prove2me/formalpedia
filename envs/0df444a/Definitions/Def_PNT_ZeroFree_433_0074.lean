-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0074
-- name    : PNT_ZeroFree_433_0074
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T21:20:16.545098+00:00
-- url     : https://prove2.me/theorems/8bfa6f53-dbf7-4c43-9d0e-a4520ce81c86
-- title:
--   Zero-free region foundations: Eisenstein.Rows [0074]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.Rows
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/Rows.lean#L78-L619

import Definitions.Def_PNT_ZeroFree_433_0071

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/Rows.lean#L78-L619
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

section
open scoped BigOperators Classical MatrixGroups

section
abbrev K := ActualEisensteinCubic.K
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def row (M : levelThree) : Fin 2 → O := (M : SL(2,O)) 1

lemma row_mul (M N : levelThree) :
    row (M*N) = Matrix.vecMul (row M) (N : SL(2,O)) := by
  funext j
  simp only [row, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]

lemma row_ne_zero (M : levelThree) : row M ≠ 0 := by
  intro hz
  have hc : (M : SL(2,O)) 1 0 = 0 := congrFun hz 0
  have hd : (M : SL(2,O)) 1 1 = 0 := congrFun hz 1
  have h : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  simp only [hc, hd, mul_zero, sub_zero] at h
  exact zero_ne_one h

lemma character_eq_of_row_eq (M N : levelThree) (hr : row M = row N) :
    complexCharacter M = complexCharacter N := by
  have hrow : row (M*N⁻¹) = row 1 := by
    rw [row_mul, hr, ← row_mul]
    simp
  have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0 = 0 := by
    simpa [row, Matrix.one_apply] using congrFun hrow 0
  have hchar : complexCharacter (M*N⁻¹) = 1 := by
    change eisEmbedding (value (M*N⁻¹)) = 1
    rw [value_zero_lower_left _ hc, map_one]
  calc
    complexCharacter M = complexCharacter ((M*N⁻¹)*N) := by congr 1; group
    _ = complexCharacter (M*N⁻¹) * complexCharacter N := map_mul _ _ _
    _ = complexCharacter N := by rw [hchar, one_mul]

lemma row_eq_one_of_lower_left_zero (M : levelThree)
    (hc : (M : SL(2,O)) 1 0 = 0) : row M = row 1 := by
  have hdet : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 = 1 := by
    have hd : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
        (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
    simpa only [hc, mul_zero, sub_zero] using hd
  have ha := A3_primary_unit_eq_one _ (IsUnit.of_mul_eq_one _ hdet)
    (levelThree_primary M)
  have hd : (M : SL(2,O)) 1 1 = 1 := by simpa only [ha, one_mul] using hdet
  funext j
  fin_cases j <;> simp [row, hc, hd]

def cuspStabilizer : Subgroup levelThree where
  carrier := {M | row M = row 1}
  one_mem' := rfl
  mul_mem' := by
    intro M N hM hN
    change row (M*N) = row 1
    rw [row_mul, hM, ← row_mul]
    simpa using hN
  inv_mem' := by
    intro M hM
    have h : row (M*M⁻¹) = row 1 := by simp
    rw [row_mul, hM, ← row_mul] at h
    simpa using h

lemma mem_cuspStabilizer_iff (M : levelThree) :
    M ∈ cuspStabilizer ↔ (M : SL(2,O)) 1 0 = 0 := by
  constructor
  · intro h
    simpa [row, Matrix.one_apply] using congrFun h 0
  · exact row_eq_one_of_lower_left_zero M

lemma row_eq_iff_left_cusp (M N : levelThree) : row M = row N ↔
    ∃ T : levelThree, T ∈ cuspStabilizer ∧ M = T*N := by
  constructor
  · intro h
    refine ⟨M*N⁻¹, ?_, by group⟩
    change row (M*N⁻¹) = row 1
    rw [row_mul, h, ← row_mul]
    simp
  · rintro ⟨T,hT,rfl⟩
    change row T = row 1 at hT
    rw [row_mul, hT, ← row_mul, one_mul]

def cuspRelation : Setoid levelThree := Setoid.ker row

abbrev CuspCosets := Quotient cuspRelation

def cosetOf (M : levelThree) : CuspCosets := Quotient.mk _ M

lemma cosetOf_eq_iff (M N : levelThree) : cosetOf M = cosetOf N ↔
    ∃ T : levelThree, T ∈ cuspStabilizer ∧ M = T*N := by
  rw [← row_eq_iff_left_cusp]
  exact Quotient.eq

def cosetRow : CuspCosets → (Fin 2 → O) :=
  Quotient.lift row (fun _ _ h => h)

@[simp] lemma cosetRow_cosetOf (M : levelThree) : cosetRow (cosetOf M) = row M := rfl

lemma cosetRow_injective : Function.Injective cosetRow := by
  intro x y
  induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
      intro h
      exact Quotient.sound h

lemma cosetRow_ne_zero (x : CuspCosets) : cosetRow x ≠ 0 := by
  induction x using Quotient.inductionOn with | _ M => exact row_ne_zero M

def cosetCharacter : CuspCosets → ℂ :=
  Quotient.lift complexCharacter (fun M N h => character_eq_of_row_eq M N h)

@[simp] lemma cosetCharacter_cosetOf (M : levelThree) :
    cosetCharacter (cosetOf M) = complexCharacter M := rfl

lemma norm_cosetCharacter (x : CuspCosets) : ‖cosetCharacter x‖ = 1 := by
  induction x using Quotient.inductionOn with | _ M => exact norm_complexCharacter M

def rightTranslate (M : levelThree) : CuspCosets → CuspCosets :=
  Quotient.map (fun N => N*M) (by
    intro A B h
    change row (A*M) = row (B*M)
    rw [row_mul, row_mul, show row A = row B from h])

@[simp] lemma rightTranslate_cosetOf (M N : levelThree) :
    rightTranslate M (cosetOf N) = cosetOf (N*M) := rfl

lemma rightTranslate_mul (M N : levelThree) (x : CuspCosets) :
    rightTranslate N (rightTranslate M x) = rightTranslate (M*N) x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf ((A*M)*N) = cosetOf (A*(M*N))
    rw [mul_assoc]

@[simp] lemma rightTranslate_one (x : CuspCosets) : rightTranslate 1 x = x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf (A*1) = cosetOf A
    rw [mul_one]

def rightEquiv (M : levelThree) : CuspCosets ≃ CuspCosets where
  toFun := rightTranslate M
  invFun := rightTranslate M⁻¹
  left_inv x := by rw [rightTranslate_mul]; simp
  right_inv x := by rw [rightTranslate_mul]; simp

lemma cosetRow_rightEquiv (M : levelThree) (x : CuspCosets) :
    cosetRow (rightEquiv M x) = Matrix.vecMul (cosetRow x) (M : SL(2,O)) := by
  induction x using Quotient.inductionOn with | _ N => exact row_mul N M

lemma cosetCharacter_rightEquiv (M : levelThree) (x : CuspCosets) :
    cosetCharacter (rightEquiv M x) = cosetCharacter x * complexCharacter M := by
  induction x using Quotient.inductionOn with | _ N => exact map_mul _ _ _

def complexMatrix : levelThree →* SL(2,ℂ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) eisEmbedding).comp levelThree.subtype

lemma complexMatrix_apply (M : levelThree) (i j : Fin 2) :
    complexMatrix M i j = eisEmbedding ((M : SL(2,O)) i j) := rfl

def embeddedRow (x : CuspCosets) : Fin 2 → ℂ := eisEmbedding ∘ cosetRow x

lemma embeddedRow_ne_zero (x : CuspCosets) : embeddedRow x ≠ 0 := by
  intro hz
  apply cosetRow_ne_zero x
  funext i
  apply eisEmbedding_injective
  simpa only [embeddedRow, Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hz i

lemma embeddedRow_rightEquiv (M : levelThree) (x : CuspCosets) :
    embeddedRow (rightEquiv M x) = Matrix.vecMul (embeddedRow x) (complexMatrix M : SL(2,ℂ)) := by
  funext j
  simp only [embeddedRow, Function.comp_apply, cosetRow_rightEquiv,
    Matrix.vecMul, dotProduct, map_sum, map_mul, complexMatrix_apply]

end

section
open ActualEisensteinCubic ConcreteTraceCRT

def integerLattice : Submodule ℤ ((Fin 2 × Fin 2) → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2 × Fin 2)))

instance : DiscreteTopology integerLattice := by
  unfold integerLattice
  infer_instance

instance : IsZLattice ℝ integerLattice := by
  unfold integerLattice
  infer_instance

def integerPoint (n : (Fin 2 × Fin 2) → ℤ) : integerLattice :=
  ⟨fun i => (n i : ℝ), by
    rw [integerLattice, (Pi.basisFun ℝ (Fin 2 × Fin 2)).mem_span_iff_repr_mem ℤ]
    intro i
    exact ⟨n i, by simp⟩⟩

lemma integerPoint_injective : Function.Injective integerPoint := by
  intro a b hab
  funext i
  have h := congrArg (fun x : integerLattice => (x : (Fin 2 × Fin 2) → ℝ) i) hab
  change (a i : ℝ) = (b i : ℝ) at h
  exact_mod_cast h

lemma integerPoint_norm (n : (Fin 2 × Fin 2) → ℤ) : ‖integerPoint n‖ = ‖n‖ := by
  change ‖fun i => (n i : ℝ)‖ = ‖n‖
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← Int.norm_eq_abs] using norm_le_pi_norm n i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← Int.norm_eq_abs] using norm_le_pi_norm (fun i => (n i : ℝ)) i

lemma summable_integer_four_rpow (k : ℝ) (hk : 4 < k) :
    Summable (fun n : (Fin 2 × Fin 2) → ℤ => ‖n‖ ^ (-k)) := by
  have hf : Module.finrank ℤ integerLattice = 4 := by
    rw [ZLattice.rank ℝ integerLattice]
    simp
  have hs := ZLattice.summable_norm_rpow integerLattice (-k) (by rw [hf]; norm_num; linarith)
  apply (hs.comp_injective integerPoint_injective).congr
  intro n
  change ‖integerPoint n‖ ^ (-k) = ‖n‖ ^ (-k)
  rw [integerPoint_norm]

def rowCoordinates (v : Fin 2 → O) : (Fin 2 × Fin 2) → ℤ :=
  fun i => if i.2 = 0 then (ActualEisensteinCoordinates.coords (v i.1)).1
    else (ActualEisensteinCoordinates.coords (v i.1)).2

lemma rowCoordinates_injective : Function.Injective rowCoordinates := by
  intro v w hvw
  funext i
  apply latticeCoordEquiv.injective
  apply Prod.ext
  · exact congrFun hvw (i,0)
  · exact congrFun hvw (i,1)

lemma coordinates_norm_bound (v : Fin 2 → O) :
    ‖rowCoordinates v‖ ≤ 2 * ‖fun i => eisEmbedding (v i)‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hi := norm_le_pi_norm (fun j => eisEmbedding (v j)) i.1
  have hq := eisEmbedding_eval_norm_sq
    (ActualEisensteinCoordinates.coords (v i.1)).1
    (ActualEisensteinCoordinates.coords (v i.1)).2
  rw [ActualEisensteinCoordinates.eval_coords] at hq
  push_cast at hq
  have hcoord (a b : ℝ) (t : ℝ) (ht : 0 ≤ t)
      (heq : t ^ 2 = a*a-a*b+b*b) : |a| ≤ 2*t ∧ |b| ≤ 2*t := by
    constructor <;> apply (abs_le).mpr <;> constructor <;>
      nlinarith [sq_nonneg (a-b), sq_nonneg (a+b), sq_nonneg (a-2*b), sq_nonneg (b-2*a)]
  have hh := hcoord _ _ ‖eisEmbedding (v i.1)‖ (norm_nonneg _) hq
  dsimp only [rowCoordinates]
  split_ifs
  · simpa only [Int.norm_eq_abs] using hh.1.trans (mul_le_mul_of_nonneg_left hi (by norm_num))
  · simpa only [Int.norm_eq_abs] using hh.2.trans (mul_le_mul_of_nonneg_left hi (by norm_num))

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def rowEnergy (v : Fin 2 → ℂ) : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2

lemma rowEnergy_nonneg (v : Fin 2 → ℂ) : 0 ≤ rowEnergy v := by
  unfold rowEnergy; positivity

lemma norm_le_sqrt_rowEnergy (v : Fin 2 → ℂ) : ‖v‖ ≤ Real.sqrt (rowEnergy v) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply Real.le_sqrt_of_sq_le
  fin_cases i <;> dsimp [rowEnergy] <;> nlinarith [sq_nonneg ‖v 0‖, sq_nonneg ‖v 1‖]

lemma rowEnergy_pos (v : Fin 2 → ℂ) (hv : v ≠ 0) : 0 < rowEnergy v := by
  have h := norm_le_sqrt_rowEnergy v
  have hn := norm_pos_iff.mpr hv
  exact Real.sqrt_pos.mp (lt_of_lt_of_le hn h)

def rowOperator (g : SL(2,ℂ)) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLinearMapRight' (g : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap

@[simp] lemma rowOperator_apply (g : SL(2,ℂ)) (v : Fin 2 → ℂ) :
    rowOperator g v = Matrix.vecMul v (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl

lemma rowOperator_mul (g h : SL(2,ℂ)) (v : Fin 2 → ℂ) :
    rowOperator h (rowOperator g v) = rowOperator (g*h) v := by
  simp only [rowOperator_apply, Matrix.vecMul_vecMul, Matrix.SpecialLinearGroup.coe_mul]

@[simp] lemma rowOperator_one (v : Fin 2 → ℂ) : rowOperator 1 v = v := by
  simp only [rowOperator_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

lemma rowOperator_ne_zero (g : SL(2,ℂ)) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    rowOperator g v ≠ 0 := by
  intro hz
  have h := congrArg (rowOperator g⁻¹) hz
  rw [rowOperator_mul, mul_inv_cancel, rowOperator_one, map_zero] at h
  exact hv h

def rowBound (g : SL(2,ℂ)) : ℝ := 2 * (1 + ‖rowOperator g⁻¹‖)

lemma rowBound_pos (g : SL(2,ℂ)) : 0 < rowBound g := by unfold rowBound; positivity

lemma coordinates_le_transformed_energy (g : SL(2,ℂ)) (v : Fin 2 → O) :
    ‖rowCoordinates v‖ ≤ rowBound g *
      Real.sqrt (rowEnergy (rowOperator g (fun i => eisEmbedding (v i)))) := by
  have hi := (rowOperator g⁻¹).le_opNorm (rowOperator g (fun i => eisEmbedding (v i)))
  rw [rowOperator_mul, mul_inv_cancel, rowOperator_one] at hi
  have hb := coordinates_norm_bound v
  have he := norm_le_sqrt_rowEnergy (rowOperator g (fun i => eisEmbedding (v i)))
  have hm := mul_le_mul_of_nonneg_left he (norm_nonneg (rowOperator g⁻¹))
  dsimp only [rowBound]
  nlinarith [Real.sqrt_nonneg (rowEnergy (rowOperator g (fun i => eisEmbedding (v i))))]

lemma norm_coordinates_ne_zero (x : CuspCosets) : 0 < ‖rowCoordinates (cosetRow x)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  apply cosetRow_ne_zero x
  apply rowCoordinates_injective
  have hz0 : rowCoordinates (0 : Fin 2 → O) = 0 := by
    apply norm_le_zero_iff.mp
    have he : (fun i : Fin 2 => eisEmbedding ((0 : Fin 2 → O) i)) =
        (0 : Fin 2 → ℂ) := by
      funext i
      exact map_zero _
    have hh := coordinates_norm_bound (0 : Fin 2 → O)
    rw [he, norm_zero, mul_zero] at hh
    exact hh
  rw [hz0]
  exact hz

def summand (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) : ℂ :=
  (cosetCharacter x)⁻¹ *
    (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s)

lemma norm_summand (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    ‖summand g s x‖ = rowEnergy (rowOperator g (embeddedRow x)) ^ (-s.re) := by
  rw [summand, norm_mul, norm_inv, norm_cosetCharacter, inv_one, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x)))]
  rfl

lemma norm_summand_bound (g : SL(2,ℂ)) (s : ℂ) (hs : 0 < s.re) (x : CuspCosets) :
    ‖summand g s x‖ ≤ (rowBound g) ^ (2*s.re) *
      ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re)) := by
  rw [norm_summand]
  have hn := norm_coordinates_ne_zero x
  have hb := rowBound_pos g
  have he := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  have hbd := coordinates_le_transformed_energy g (cosetRow x)
  change ‖rowCoordinates (cosetRow x)‖ ≤ rowBound g *
    Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) at hbd
  have hle : (‖rowCoordinates (cosetRow x)‖ / rowBound g) ^ 2 ≤
      rowEnergy (rowOperator g (embeddedRow x)) := by
    have hd : ‖rowCoordinates (cosetRow x)‖ / rowBound g ≤
        Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) :=
      (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hbd)
    have hsq := Real.sq_sqrt he.le
    nlinarith [div_pos hn hb, Real.sqrt_nonneg (rowEnergy (rowOperator g (embeddedRow x)))]
  have hp := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (div_pos hn hb)) hle (by linarith : -s.re ≤ 0)
  convert! hp using 1
  rw [← Real.rpow_natCast_mul (div_nonneg hn.le hb.le) 2 (-s.re),
    Real.div_rpow hn.le hb.le]
  simp only [Nat.cast_ofNat, mul_neg, Real.rpow_neg hb.le, div_eq_mul_inv, inv_inv]
  exact mul_comm _ _

theorem summable_norm_summand (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun x : CuspCosets => ‖summand g s x‖) := by
  have hsum := summable_integer_four_rpow (2*s.re) (by linarith)
  have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
    rowCoordinates_injective.comp cosetRow_injective
  have hcomp : Summable (fun x : CuspCosets => ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re))) := by
    apply (hsum.comp_injective hinj).congr
    intro x
    rfl
  exact (hcomp.mul_left ((rowBound g) ^ (2*s.re))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun x => norm_summand_bound g s (by linarith) x)

theorem summable_summand (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    Summable (summand g s) := (summable_norm_summand g s hs).of_norm

def eisenstein (g : SL(2,ℂ)) (s : ℂ) : ℂ := ∑' x : CuspCosets, summand g s x

lemma transformedRow_rightEquiv (M : levelThree) (g : SL(2,ℂ)) (x : CuspCosets) :
    rowOperator g (embeddedRow (rightEquiv M x)) =
      rowOperator (complexMatrix M * g) (embeddedRow x) := by
  rw [embeddedRow_rightEquiv, ← rowOperator_apply, rowOperator_mul]

lemma summand_automorphy (M : levelThree) (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    summand (complexMatrix M * g) s x =
      complexCharacter M * summand g s (rightEquiv M x) := by
  have hM : complexCharacter M ≠ 0 := by
    intro h
    have hn := norm_complexCharacter M
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  simp only [summand, cosetCharacter_rightEquiv, transformedRow_rightEquiv,
    mul_inv_rev]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hM, one_mul]

theorem eisenstein_automorphy (M : levelThree) (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    eisenstein (complexMatrix M * g) s = complexCharacter M * eisenstein g s := by
  have hleft := summable_summand (complexMatrix M * g) s hs
  have hright := summable_summand g s hs
  have hreindex : HasSum (fun x : CuspCosets => summand g s (rightEquiv M x))
      (eisenstein g s) := (rightEquiv M).hasSum_iff.mpr hright.hasSum
  have hscale := hreindex.mul_left (complexCharacter M)
  exact hleft.hasSum.unique (hscale.congr_fun (fun x => summand_automorphy M g s x))

lemma summand_differentiable (g : SL(2,ℂ)) (x : CuspCosets) :
    Differentiable ℂ (fun s : ℂ => summand g s x) := by
  have hq : (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))).ne'
  exact ((differentiable_id.neg).const_cpow (Or.inl hq)).const_mul _

lemma norm_summand_strip (g : SL(2,ℂ)) (a b : ℝ) (s : ℂ)
    (ha : a ≤ s.re) (hb : s.re ≤ b) (x : CuspCosets) :
    ‖summand g s x‖ ≤ ‖summand g (a : ℂ) x‖ + ‖summand g (b : ℂ) x‖ := by
  simp only [norm_summand, Complex.ofReal_re]
  have hq := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  by_cases hq1 : 1 ≤ rowEnergy (rowOperator g (embeddedRow x))
  · exact (Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg ha)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hq.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hq (le_of_not_ge hq1)
        (neg_le_neg hb)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hq.le _))

theorem eisenstein_differentiableOn_strip (g : SL(2,ℂ)) (a b : ℝ)
    (ha : 2 < a) (hab : a < b) :
    DifferentiableOn ℂ (eisenstein g) {s : ℂ | a < s.re ∧ s.re < b} := by
  have hsa := summable_norm_summand g (a : ℂ) (by simpa using ha)
  have hsb := summable_norm_summand g (b : ℂ) (by simpa using lt_trans ha hab)
  apply Complex.differentiableOn_tsum_of_summable_norm (hsa.add hsb)
    (fun x => (summand_differentiable g x).differentiableOn)
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  · intro x s hs
    exact norm_summand_strip g a b s hs.1.le hs.2.le x

theorem eisenstein_differentiableAt (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    DifferentiableAt ℂ (eisenstein g) s := by
  let a := (2+s.re)/2
  let b := s.re+1
  have ha : 2 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hsU : s ∈ {z : ℂ | a < z.re ∧ z.re < b} := by
    constructor <;> dsimp [a,b] <;> linarith
  exact (eisenstein_differentiableOn_strip g a b ha hab s hsU).differentiableAt
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hsU)

theorem eisenstein_differentiableOn (g : SL(2,ℂ)) :
    DifferentiableOn ℂ (eisenstein g) {s : ℂ | 2 < s.re} := by
  intro s hs
  exact (eisenstein_differentiableAt g s hs).differentiableWithinAt

end

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) : SL(2,ℂ) :=
  ⟨!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹], by
    have hr : (Real.sqrt v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
    simp [Matrix.det_fin_two, hr]⟩

lemma rowOperator_upperSection_zero (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowOperator (upperSection z v hv) u 0 = u 0 * (Real.sqrt v : ℂ) := by
  change Matrix.vecMul u (!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) _ = _
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma rowOperator_upperSection_one (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowOperator (upperSection z v hv) u 1 = (u 0*z + u 1) / (Real.sqrt v : ℂ) := by
  change Matrix.vecMul u (!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) _ = _
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

def heightDenominator (z : ℂ) (v : ℝ) (u : Fin 2 → ℂ) : ℝ :=
  ‖u 0*z + u 1‖ ^ 2 + ‖u 0‖ ^ 2 * v ^ 2

lemma rowEnergy_upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowEnergy (rowOperator (upperSection z v hv) u) = heightDenominator z v u / v := by
  rw [rowEnergy, rowOperator_upperSection_zero, rowOperator_upperSection_one,
    norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg v),
    mul_pow, div_pow, Real.sq_sqrt hv.le]
  unfold heightDenominator
  field_simp
  ring

lemma heightDenominator_pos (z : ℂ) (v : ℝ) (hv : 0 < v)
    (u : Fin 2 → ℂ) (hu : u ≠ 0) : 0 < heightDenominator z v u := by
  have h := rowEnergy_pos _ (rowOperator_ne_zero (upperSection z v hv) u hu)
  rw [rowEnergy_upperSection] at h
  exact ((div_pos_iff.mp h).resolve_right (by rintro ⟨_,hneg⟩; linarith)).1

def transformedHeight (z : ℂ) (v : ℝ) (u : Fin 2 → ℂ) : ℝ :=
  v / heightDenominator z v u

lemma summand_upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (x : CuspCosets) :
    summand (upperSection z v hv) s x = (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s := by
  rw [summand, rowEnergy_upperSection]
  congr 1
  have hq := heightDenominator_pos z v hv (embeddedRow x) (embeddedRow_ne_zero x)
  have hinv : (transformedHeight z v (embeddedRow x) : ℂ) =
      ((heightDenominator z v (embeddedRow x) / v : ℝ) : ℂ)⁻¹ := by
    simp only [transformedHeight, Complex.ofReal_div, inv_div]
  rw [hinv, Complex.inv_cpow_ofReal_nonneg (div_nonneg hq.le hv.le), Complex.cpow_neg]

def upperEisenstein (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) : ℂ :=
  eisenstein (upperSection z v hv) s

theorem upperEisenstein_eq_source_series (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    upperEisenstein z v hv s = ∑' x : CuspCosets, (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s :=
  tsum_congr (summand_upperSection z v hv s)

theorem source_series_summable (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun x : CuspCosets => (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s) :=
  (summable_summand (upperSection z v hv) s hs).congr (summand_upperSection z v hv s)

lemma ofReal_rowEnergy (u : Fin 2 → ℂ) :
    (rowEnergy u : ℂ) = dotProduct u (star u) := by
  simp only [rowEnergy, Complex.ofReal_add, ← Complex.normSq_eq_norm_sq, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, Complex.mul_conj]

lemma rowEnergy_unitary (k : SL(2,ℂ))
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (u : Fin 2 → ℂ) : rowEnergy (rowOperator k u) = rowEnergy u := by
  apply Complex.ofReal_injective
  rw [ofReal_rowEnergy, ofReal_rowEnergy, rowOperator_apply, Matrix.star_vecMul,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have hu := Matrix.mem_unitaryGroup_iff.mp hk
  change (k : Matrix (Fin 2) (Fin 2) ℂ) *
    Matrix.conjTranspose (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 at hu
  rw [hu, Matrix.vecMul_one]

theorem eisenstein_right_unitary (g k : SL(2,ℂ)) (s : ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    eisenstein (g*k) s = eisenstein g s := by
  apply tsum_congr
  intro x
  simp only [summand, ← rowOperator_mul, rowEnergy_unitary k hk]

end CubicEisenstein

end

end OAI

end


