-- Prove2me | Definitions.Def_OAIQWRHT000
-- name    : OAIQWRHT000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T22:15:35.646073+00:00
-- url     : https://prove2.me/theorems/0676c288-99d8-4748-84d8-21c45ef645f4
-- title:
--   OpenAI rational hitting lists split: definitions bundle OAIQWRHT000
-- statement:
--   One of the five definitions bundles (`OAIQWRHT000` to `OAIQWRHT004`) of the split of OpenAI's proof that one deterministic Turing machine writes, in polynomial time, a polynomial-size list of rational matrix tuples hitting every admissible nonzero noncommutative rational formula of size at most $s$ (`OAI.RationalHitting.main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Computability/RationalHitting` (OpenAI, *Polynomial Hitting Lists for Noncommutative Rational Formulas*, OpenAI Math Release, September 24, 2026, result family 116, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. Among them are the cyclotomic grid construction of the list (`Generator.list`, `ExecutableGenerator.list`), the pencil certificates, the binary arithmetic procedures, the stack language with its time bounds, and the compiler to `Turing.TM0` machines. The bundles split the material only to keep each one within the platform's compile limits.
--
--   The definitions of the published statement (`Formula`, `Evaluates`, `Admissible`, `Nonzero`, `Output`, `encodeOutput`, `Machine`, `run`, `OutputsWithin`, `Hits`, `MainStatement` and the rest) are not repeated: the bundles import them from the published bundle `Def_RationalHitting`. It imports no other bundle of this split.
--
--   Modules (some only in part): `Affine`, `BinaryAddition`, `BinaryBinomial`, `BinaryDivision`, `BinaryFactorial`, `BinaryGcd`, `BinaryMultiply`, `BinarySubtract`, `BinomialBounds`, `BlockDivision`, `Certificates`, `Compiler`, `CyclotomicGrid`, `Deformation`, `Determinant`, `EncodingBounds`, `Evaluation`, `Executable`, `Generator`, `IntegralLift`, `LaurentReduction`, `PaddedRank`, `QuantumMatrices`, `QuantumSeries`, `RationalBinary`, `Rectangular`, `SmallExpansion`, `StackLanguage`, `StackWords`, `Tabulation`, `Wronskian`.
--
--   The theorems the definitions do not need are proved in the three solutions of this split. One proves the published intermediate statement `OAI.RationalHitting.Generator.list_hits` (the paper's Proposition 5.1), one proves `OAI.RationalHitting.ExecutableGenerator.implementation` (Proposition 5.3) using it, and the third proves `OAI.RationalHitting.main` from both. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Polynomial Hitting Lists for Noncommutative Rational Formulas, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 116; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability/RationalHitting at commit adc7f12

import Mathlib
import Definitions.Def_RationalHitting

section
-- module Solutions.OAIQW_RationalHitting.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Evaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.NoncommBlocks
open Matrix
variable {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

abbrev matMul {l m n : Type*} [Fintype m] (A : Matrix l m R) (B : Matrix m n R) :
    Matrix l n R := A * B

end RationalHitting.NoncommBlocks

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Affine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting
open Matrix
namespace Affine
variable {n : ℕ}
abbrev Form (n : ℕ) := ℚ × (Fin n → ℚ)
def constant (a : ℚ) : Form n := (a,0)
def varForm (i : Fin n) : Form n := (0,Pi.single i 1)
variable {R : Type*} [Ring R]
def eval (c : ℚ →+* R) (X : Fin n → R) : Form n →+ R where
  toFun := fun a => c a.1 + ∑ i, c (a.2 i) * X i
  map_zero' := by simp
  map_add' := by
    intro a b
    simp [map_add, add_mul, Finset.sum_add_distrib]
    abel
@[simp] lemma eval_constant (c : ℚ →+* R) (X : Fin n → R) (a : ℚ) :
    eval c X (constant a) = c a := by simp [eval,constant]
@[simp] lemma eval_variable (c : ℚ →+* R) (X : Fin n → R) (i : Fin n) :
    eval c X (varForm i) = X i := by
  simp [eval,varForm,Pi.single_apply, apply_ite]
def constMatrix {ι κ : Type*} (A : Matrix ι κ ℚ) : Matrix ι κ (Form n) := A.map constant
@[simp] lemma eval_constMatrix {ι κ : Type*} (c : ℚ →+* R) (X : Fin n → R)
    (A : Matrix ι κ ℚ) : (constMatrix A).map (eval c X) = A.map c := by
  ext i j
  exact eval_constant c X (A i j)
end Affine

namespace Formula
noncomputable section
variable {n : ℕ}

@[reducible] def Index : Formula n → Type
  | .var _ | .const _ => Unit ⊕ Unit
  | .add f g | .mul f g => Index f ⊕ Index g
  | .inv f => Index f ⊕ Unit

@[reducible] instance indexFintype : (h : Formula n) → Fintype (Index h)
  | .var _ | .const _ => inferInstanceAs (Fintype (Unit ⊕ Unit))
  | .add f g | .mul f g => letI := indexFintype f; letI := indexFintype g; inferInstanceAs (Fintype (Index f ⊕ Index g))
  | .inv f => letI := indexFintype f; inferInstanceAs (Fintype (Index f ⊕ Unit))

@[reducible] instance indexDecidableEq : (h : Formula n) → DecidableEq (Index h)
  | .var _ | .const _ => inferInstanceAs (DecidableEq (Unit ⊕ Unit))
  | .add f g | .mul f g => letI := indexDecidableEq f; letI := indexDecidableEq g; inferInstanceAs (DecidableEq (Index f ⊕ Index g))
  | .inv f => letI := indexDecidableEq f; inferInstanceAs (DecidableEq (Index f ⊕ Unit))

def row : (f : Formula n) → Matrix Unit f.Index ℚ
  | .var _ | .const _ => fromCols 1 0
  | .add f g => fromCols (row f) (row g)
  | .mul f _g => fromCols (row f) 0
  | .inv _f => fromCols 0 (-1)
def col : (f : Formula n) → Matrix f.Index Unit ℚ
  | .var _ | .const _ => fromRows 0 1
  | .add f g => fromRows (col f) (col g)
  | .mul _f g => fromRows 0 (col g)
  | .inv _f => fromRows 0 1

def pencil : (f : Formula n) → Matrix f.Index f.Index (Affine.Form n)
  | .var i => fromBlocks (Affine.constMatrix 1) (Matrix.of (fun _ _ => -Affine.varForm i)) 0 (Affine.constMatrix 1)
  | .const a => fromBlocks (Affine.constMatrix 1) (Matrix.of (fun _ _ => -Affine.constant a)) 0 (Affine.constMatrix 1)
  | .add f g => fromBlocks (pencil f) 0 0 (pencil g)
  | .mul f g => fromBlocks (pencil f) (-Affine.constMatrix (col f * row g)) 0 (pencil g)
  | .inv f => fromBlocks (pencil f) (Affine.constMatrix (col f)) (Affine.constMatrix (row f)) 0

variable {R : Type*} [Ring R] (c : ℚ →+* R) (X : Fin n → R)
abbrev realized (f : Formula n) := (pencil f).map (Affine.eval c X)
abbrev rowR (f : Formula n) := (row f).map c
abbrev colR (f : Formula n) := (col f).map c
abbrev scalar (a : R) : Matrix Unit Unit R := (Matrix.uniqueRingEquiv (m := Unit)).symm a

@[simp] lemma realized_add (f g : Formula n) : realized c X (.add f g) =
    fromBlocks (realized c X f) 0 0 (realized c X g) := by
  change (fromBlocks (pencil f) 0 0 (pencil g)).map (Affine.eval c X) = _
  rw [fromBlocks_map]
  simp
@[simp] lemma realized_mul (f g : Formula n) : realized c X (.mul f g) =
    fromBlocks (realized c X f) (-colR c f * rowR c g) 0 (realized c X g) := by
  change (fromBlocks (pencil f) (-Affine.constMatrix (col f * row g)) 0 (pencil g)).map (Affine.eval c X) = _
  rw [fromBlocks_map]
  rw [Matrix.map_neg _ (map_neg _)]
  simp [Matrix.map_mul,Matrix.neg_mul,rowR,colR]
@[simp] lemma realized_inv (f : Formula n) : realized c X (.inv f) =
    fromBlocks (realized c X f) (colR c f) (rowR c f) 0 := by
  change (fromBlocks (pencil f) (Affine.constMatrix (col f)) (Affine.constMatrix (row f)) 0).map (Affine.eval c X) = _
  rw [fromBlocks_map]
  simp [rowR,colR]

@[simp] lemma rowR_add (f g : Formula n) : rowR c (.add f g) = fromCols (rowR c f) (rowR c g) := by
  change (fromCols (row f) (row g)).map c = _
  exact fromCols_map _ _ _
@[simp] lemma colR_add (f g : Formula n) : colR c (.add f g) = fromRows (colR c f) (colR c g) := by
  change (fromRows (col f) (col g)).map c = _
  exact fromRows_map _ _ _
@[simp] lemma rowR_mul (f g : Formula n) : rowR c (.mul f g) = fromCols (rowR c f) 0 := by
  change (fromCols (row f) 0).map c = _
  rw [fromCols_map]
  simp
@[simp] lemma colR_mul (f g : Formula n) : colR c (.mul f g) = fromRows 0 (colR c g) := by
  change (fromRows 0 (col g)).map c = _
  rw [fromRows_map]
  simp
@[simp] lemma rowR_inv (f : Formula n) : rowR c (.inv f) = fromCols 0 (-1) := by
  change (fromCols (0 : Matrix Unit (Index f) ℚ) (-1)).map c = _
  rw [fromCols_map, Matrix.map_neg _ (map_neg _)]
  simp
@[simp] lemma colR_inv (f : Formula n) : colR c (.inv f) = fromRows 0 1 := by
  change (fromRows (0 : Matrix (Index f) Unit ℚ) 1).map c = _
  rw [fromRows_map]
  simp

end
end Formula
end RationalHitting

namespace RationalHitting.Formula
open Matrix
noncomputable section
variable {n : ℕ} {R : Type*} [Ring R]
variable (c : ℚ →+* R) (X : Fin n → R)

/-- The list retains occurrences, not just distinct subexpressions. -/
def inverseNodes : Formula n → List (Formula n)
  | .var _ | .const _ => []
  | .add f g | .mul f g => inverseNodes f ++ inverseNodes g
  | .inv f => .inv f :: inverseNodes f

/-- `.inv f` here denotes the root augmentation pencil, not a new counted gate. -/
def certificates (f : Formula n) := inverseNodes f ++ [.inv f]

end
end RationalHitting.Formula

namespace RationalHitting.Affine
open Matrix
open scoped BigOperators
noncomputable section
variable {n : ℕ} {R : Type*} [Ring R]

def coeff (a : Form n) : Fin (n+1) → ℚ := Fin.cases a.1 a.2

def homogeneous (c : ℚ →+* R) (Z : Fin (n+1) → R) (a : Form n) : R :=
  ∑ i, c (coeff a i) * Z i

end
end RationalHitting.Affine

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Wronskian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.Expansion
open Polynomial Module
open scoped BigOperators Polynomial

noncomputable section

/-- The Wronskian with derivative orders 0, ..., h - 1. -/
def wronskian {K : Type*} [CommRing K] {h : ℕ} (f : Fin h → K[X]) : K[X] :=
  Matrix.det (Matrix.of fun i j : Fin h => derivative^[i.val] (f j))


/-- Fixed-length coefficient reversal is linear, unlike degree-dependent
polynomial reversal. -/
def reflectLinearEquiv (K : Type*) [Field K] (N : ℕ) : K[X] ≃ₗ[K] K[X] where
  toFun := reflect N
  invFun := reflect N
  left_inv := fun _ => reflect_reflect
  right_inv := fun _ => reflect_reflect
  map_add' := fun f g => reflect_add f g N
  map_smul' := by
    intro c f
    simpa only [smul_eq_C_mul, RingHom.id_apply] using reflect_C_mul f c N


/-- The exact vanishing filtration, expressed by low Taylor coefficients. -/
def vanishingFiltration {K : Type*} [Field K] (V : Submodule K K[X])
    (a : K) (r : ℕ) : Submodule K K[X] where
  carrier := {f | f ∈ V ∧ ∀ m < r, (taylor a f).coeff m = 0}
  zero_mem' := ⟨V.zero_mem, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hf0⟩ ⟨hg, hg0⟩
    refine ⟨V.add_mem hf hg, ?_⟩
    intro m hm
    simp [hf0 m hm, hg0 m hm]
  smul_mem' := by
    rintro c f ⟨hf, hf0⟩
    refine ⟨V.smul_mem c hf, ?_⟩
    intro m hm
    simp [hf0 m hm]

end
end RationalHitting.Expansion


/-! An integral frame records integral coordinate functionals, making
saturation explicit. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.LaurentReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.LaurentReduction
open Module
open scoped BigOperators LaurentSeries PowerSeries
noncomputable section

variable {K : Type*} [Field K]
abbrev F (K : Type*) [Field K] := LaurentSeries K

/-- Membership in K[[t]], inside K((t)). -/
def Integral (x : F K) : Prop := ∃ p : PowerSeries K, HahnSeries.ofPowerSeries ℤ K p = x

def reduction (x : F K) : K := x.coeff 0

def reduce {ι : Type*} (x : ι → F K) : ι → K := fun i => reduction (x i)

@[simp] lemma reduction_zero : reduction (0 : F K) = 0 := by simp [reduction]
@[simp] lemma reduction_one : reduction (1 : F K) = 1 := by simp [reduction]

/-- Coefficientwise integrality, not an arbitrary sublattice. -/
def IntegralVector {ι : Type*} (x : ι → F K) : Prop := ∀ i, Integral (x i)

/-- A coordinate functional which is defined integrally on the full ambient
integral lattice. -/
def IntegralFunctional {ι : Type*} (f : (ι → F K) →ₗ[F K] F K) : Prop :=
  ∀ x, IntegralVector x → Integral (f x)

structure IntegralFrame {ι : Type*} (U : Submodule (F K) (ι → F K)) where
  length : ℕ
  vector : Fin length → (ι → F K)
  coordinate : Fin length → ((ι → F K) →ₗ[F K] F K)
  span_eq : Submodule.span (F K) (Set.range vector) = U
  vector_integral : ∀ j, IntegralVector (vector j)
  coordinate_integral : ∀ j, IntegralFunctional (coordinate j)
  pairing : ∀ i j, coordinate i (vector j) = if i = j then 1 else 0
  reduced_independent : LinearIndependent K (fun j => reduce (vector j))


@[simp] lemma reduction_C (a : K) : reduction (HahnSeries.C a : F K) = a := by
  simp [reduction, HahnSeries.C_apply]

/-- The reduction uses every integral member of U. -/
def ReducedSet {ι : Type*} (U : Submodule (F K) (ι → F K)) : Set (ι → K) :=
  { y | ∃ x ∈ U, IntegralVector x ∧ reduce x = y }

def reducedSubspace {ι : Type*} (U : Submodule (F K) (ι → F K)) : Submodule K (ι → K) :=
  Submodule.span K (ReducedSet U)

/-- Multiplication by t^a, written as its identical Laurent monomial. -/
def weightMap {ι : Type*} (w : ι → ℕ) : (ι → F K) →ₗ[F K] (ι → F K) where
  toFun x i := HahnSeries.single (w i : ℤ) 1 * x i
  map_add' := by intros; ext; simp [mul_add]
  map_smul' := by intros; ext; simp [mul_left_comm]

def IntegralFrame.subframe {ι : Type*} {U : Submodule (F K) (ι → F K)}
    (b : IntegralFrame U) {k : ℕ} (a : Fin k → Fin b.length)
    (ha : Function.Injective a) :
    IntegralFrame (Submodule.span (F K) (Set.range (b.vector ∘ a))) where
  length := k
  vector := b.vector ∘ a
  coordinate := b.coordinate ∘ a
  span_eq := rfl
  vector_integral := fun j => b.vector_integral (a j)
  coordinate_integral := fun j => b.coordinate_integral (a j)
  pairing := by
    intro i j
    simp only [Function.comp_apply, b.pairing, ha.eq_iff]
  reduced_independent := b.reduced_independent.comp a ha

/-- Low coordinate projection and its complementary support subspace. -/
def lowProjection {ι : Type*} (w : ι → ℕ) (A : ℕ) :
    (ι → K) →ₗ[K] ({i : ι // w i ≤ A} → K) where
  toFun x i := x i
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def lowSupported {ι : Type*} (w : ι → ℕ) (A : ℕ) : Submodule K (ι → K) where
  carrier := {x | ∀ i, A < w i → x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]


section ConstantChanges
variable {ι κ τ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]

def liftMap (P : (ι → K) →ₗ[K] (κ → K)) : (ι → F K) →ₗ[F K] (κ → F K) :=
  Matrix.toLin' ((LinearMap.toMatrix' P).map HahnSeries.C)

lemma liftMap_comp.{v_1, v_2, v_3, v_4} {K : Type v_1} [Field K]
  {ι : Type v_2} {κ : Type v_3} {τ : Type v_4} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] [Fintype τ] [DecidableEq τ] (P : (κ → K) →ₗ[K] τ → K)
  (Q : (ι → K) →ₗ[K] κ → K) :
  RationalHitting.LaurentReduction.liftMap (P ∘ₗ Q) =
    RationalHitting.LaurentReduction.liftMap P ∘ₗ RationalHitting.LaurentReduction.liftMap Q := by
  simp only [liftMap, LinearMap.toMatrix'_comp, Matrix.map_mul, Matrix.toLin'_mul]

lemma liftMap_id : liftMap (LinearMap.id : (ι → K) →ₗ[K] (ι → K)) = LinearMap.id := by
  simp only [liftMap, LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.toLin'_one]

def liftEquiv (E : (ι → K) ≃ₗ[K] (κ → K)) : (ι → F K) ≃ₗ[F K] (κ → F K) :=
  { liftMap E.toLinearMap with
    invFun := liftMap E.symm.toLinearMap
    left_inv := by
      intro x
      have he := liftMap_comp E.symm.toLinearMap E.toLinearMap
      have hh : E.symm.toLinearMap.comp E.toLinearMap = LinearMap.id := by ext x; simp
      rw [hh, liftMap_id] at he
      exact (LinearMap.congr_fun he x).symm
    right_inv := by
      intro x
      have he := liftMap_comp E.toLinearMap E.symm.toLinearMap
      have hh : E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id := by ext x; simp
      rw [hh, liftMap_id] at he
      exact (LinearMap.congr_fun he x).symm }

@[simp] lemma liftEquiv_toLinearMap (E : (ι → K) ≃ₗ[K] (κ → K)) :
    (liftEquiv E).toLinearMap = liftMap E.toLinearMap := rfl

end ConstantChanges


/-- Constant coordinates on the input and output may differ (Taylor on the
input, reverse Taylor on the output in the application). -/
def conjugatedWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ein Eout : (ι → K) ≃ₗ[K] (ι → K)) (w : ι → ℕ) :
    (ι → F K) →ₗ[F K] (ι → F K) :=
  (liftEquiv Eout).symm.toLinearMap.comp
    ((weightMap w).comp (liftEquiv Ein).toLinearMap)

end
end RationalHitting.LaurentReduction

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.SmallExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.SmallExpansion
open Module Polynomial
open scoped BigOperators
open LaurentReduction Expansion
noncomputable section
variable {K : Type*} [Field K]

/-- The coefficient realization of P_M(K), with its exact degree bound. -/
def polynomialMap (M : ℕ) : (Fin M → K) →ₗ[K] K[X] :=
  (Polynomial.degreeLT K M).subtype.comp (Polynomial.degreeLTEquiv K M).symm.toLinearMap

@[simp] lemma polynomialMap_coeff (M : ℕ) (x : Fin M → K) (j : Fin M) :
    (polynomialMap M x).coeff j = x j := by
  exact congrFun ((Polynomial.degreeLTEquiv K M).apply_symm_apply x) j

def polynomialSpace {M : ℕ} (V : Submodule K (Fin M → K)) : Submodule K K[X] :=
  V.map (polynomialMap M)

def taylorCoordinates (M : ℕ) (a : K) : (Fin M → K) ≃ₗ[K] (Fin M → K) :=
  (Polynomial.degreeLTEquiv K M).symm.trans
    ((Polynomial.taylorLinearEquiv a M).trans (Polynomial.degreeLTEquiv K M))

def reverseCoordinates (M : ℕ) : (Fin M → K) ≃ₗ[K] (Fin M → K) where
  toFun x j := x j.rev
  invFun x j := x j.rev
  left_inv := by intro x; funext j; simp
  right_inv := by intro x; funext j; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def reverseTaylorCoordinates (M : ℕ) (a : K) : (Fin M → K) ≃ₗ[K] (Fin M → K) :=
  (taylorCoordinates M a).trans (reverseCoordinates M)

/-- The reverse-Taylor test on bounded-degree polynomials multiplies each
Taylor coefficient by t^a and places it in output degree M-1-a. -/
def testMap (M : ℕ) (a : K) : (Fin M → F K) →ₗ[F K] (Fin M → F K) :=
  conjugatedWeight (taylorCoordinates M a) (reverseTaylorCoordinates M a) Fin.val

end
end RationalHitting.SmallExpansion

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Rectangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.Rectangular
open Module Matrix
open scoped BigOperators Kronecker
noncomputable section
variable {F : Type*} [Field F]

/-- The ordinary Kronecker evaluation, with the two vector indices curried in
reverse order. This is only a coordinate convention. -/
def blockEval {w q e : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) :
    (Fin e → Fin q → F) →ₗ[F] (Fin e → Fin q → F) where
  toFun v β := ∑ i, ∑ δ, X i β δ • (A i).mulVec (v δ)
  map_add' v u := by
    funext β
    simp only [Pi.add_apply, Matrix.mulVec_add, smul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext β
    simp only [Pi.smul_apply, RingHom.id_apply, Matrix.mulVec_smul,
      Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro δ _
    rw [mul_comm]


variable {P Q : Type*} [AddCommGroup P] [Module F P]
  [AddCommGroup Q] [Module F Q]

def componentSpace {q : ℕ} (f : Fin q → P) : Submodule F P :=
  Submodule.span F (Set.range f)

def component {q : ℕ} (f : Fin q → P) (α : Fin q) : componentSpace (F := F) f :=
  ⟨f α, Submodule.subset_span ⟨α, rfl⟩⟩

def coefficientMatrix {q k : ℕ} (f : Fin q → P)
    (b : Basis (Fin k) F (componentSpace (F := F) f)) : Matrix (Fin q) (Fin k) F :=
  fun α => b.equivFun (component (F := F) f α)

/-- The output map of the wk possible component images. -/
def imageCombination {w k : ℕ} (T : Fin w → P →ₗ[F] Q) (u : Fin k → P) :
    (Fin w × Fin k → F) →ₗ[F] Q :=
  Fintype.linearCombination F (fun ij => T ij.1 (u ij.2))

/-- The concatenated coefficient matrix. -/
def concatMatrix {w q k : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (P : Matrix (Fin q) (Fin k) F) : Matrix (Fin q) (Fin w × Fin k) F :=
  fun α ij => (A ij.1 * P) α ij.2


def blockMatrix {w q e : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) :
    Matrix (Fin q × Fin e) (Fin q × Fin e) F := ∑ i, A i ⊗ₖ X i

end
end RationalHitting.Rectangular


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.PaddedRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TestPolynomial
open Polynomial Matrix Module
open LaurentReduction SmallExpansion Rectangular
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

/-- The reverse-Taylor test matrix over the univariate polynomial ring in t.
Summation over all M Taylor coordinates appends only zero terms. -/
def full (M : ℕ) (a : K) : Matrix (Fin M) (Fin M) K[X] := fun i j =>
  ∑ r : Fin M, C ((((X+C (-a))^r.rev.val : K[X]).coeff i.val) *
    (((X+C a)^j.val : K[X]).coeff r.val)) * X^r.val

def padded (M N : ℕ) (a : K) : Matrix (Fin M) (Fin M) K[X] :=
  fun i j => if j.val < N then full M a i j else 0

end
end RationalHitting.TestPolynomial

namespace RationalHitting.PaddedRank
open Matrix Module
open TestPolynomial LaurentReduction SmallExpansion Rectangular
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def raw {w q M : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) (F K))
    (R : Fin w → Matrix (Fin M) (Fin M) (F K)) :
    Matrix (Fin q × Fin M) (Fin q × Fin M) (F K) :=
  fun a b => ∑ i, A i a.1 b.1 * R i a.2 b.2

def extend (q M N : ℕ) : (Fin q × Fin N → F K) →ₗ[F K] (Fin q × Fin M → F K) where
  toFun f a := if h : a.2.val < N then f (a.1,⟨a.2.val,h⟩) else 0
  map_add' f g := by ext a; dsimp; split_ifs <;> simp
  map_smul' c f := by ext a; dsimp; split_ifs <;> simp

end
end RationalHitting.PaddedRank

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.QuantumSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.QuantumSeries
open HahnSeries Module
open scoped BigOperators
noncomputable section
variable {Γ K R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [Ring R] [Algebra K R] [Nontrivial R]

/-- Each exponent has the one-dimensional coefficient line of its ordered
quantum monomial. Lexicographic leading terms do not require a domain
matrix coefficient ring. -/
def line (B : Γ → Rˣ) (g : Γ) : Submodule K R := K ∙ (B g : R)

lemma line_mul.{v_1, v_2, v_3} {Γ : Type v_1} {K : Type v_2}
  {R : Type v_3} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K] [Ring R]
  [Algebra K R] [Nontrivial R] (B : Γ → Rˣ)
  (hB : ∀ (g h : Γ), ∃ c : K, (B g : R) * (B h : R) = c • (B (g + h) : R))
  {g h : Γ} {x y : R}
  (hx : x ∈ RationalHitting.QuantumSeries.line (K := K) B g)
  (hy : y ∈ RationalHitting.QuantumSeries.line (K := K) B h) :
  x * y ∈ RationalHitting.QuantumSeries.line (K := K) B (g + h) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨c, hc⟩ := hB g h
  rw [smul_mul_assoc, mul_smul_comm, hc, smul_smul, smul_smul]
  exact Submodule.mem_span_singleton.mpr ⟨a*b*c, rfl⟩

lemma line_isUnit.{v_1, v_2, v_3} {Γ : Type v_1} {K : Type v_2}
  {R : Type v_3} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K] [Ring R]
  [Algebra K R] [Nontrivial R] (B : Γ → Rˣ) {g : Γ} {x : R}
  (hx : x ∈ RationalHitting.QuantumSeries.line (K := K) B g) (hne : x ≠ 0) : IsUnit x := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have ha : a ≠ 0 := by intro h; simp [h] at hne
  rw [Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.mpr ha).map (algebraMap K R)).mul (B g).isUnit

def coefficientRing (B : Γ → Rˣ) (h0 : B 0 = 1)
    (hB : ∀ g h, ∃ c : K, (B g : R)*(B h : R) = c • (B (g+h) : R)) :
    Subring (HahnSeries Γ R) where
  carrier := {x | ∀ g, x.coeff g ∈ line (K := K) B g}
  zero_mem' := fun g => (line (K := K) B g).zero_mem
  one_mem' := by
    intro g
    by_cases hg : g = 0
    · subst g
      simp only [HahnSeries.coeff_one, line, h0, Units.val_one]
      exact Submodule.subset_span (Set.mem_singleton _)
    · simp [HahnSeries.coeff_one, hg]
  add_mem' := by
    intro x y hx hy g
    exact (line (K := K) B g).add_mem (hx g) (hy g)
  neg_mem' := by
    intro x hx g
    exact (line (K := K) B g).neg_mem (hx g)
  mul_mem' := by
    intro x y hx hy g
    rw [HahnSeries.coeff_mul]
    apply (line (K := K) B g).sum_mem
    intro ij hij
    have heq := (Finset.mem_antidiagonal.mp hij).2.2
    rw [← heq]
    exact line_mul B hB (hx ij.1) (hy ij.2)

lemma coefficientRing_noZeroDivisors (B : Γ → Rˣ) (h0 : B 0 = 1)
    (hB : ∀ g h, ∃ c : K, (B g : R)*(B h : R) = c • (B (g+h) : R)) :
    NoZeroDivisors (coefficientRing B h0 hB) := by
  constructor
  intro x y hxy
  by_contra hn
  have hx : x ≠ 0 := fun hx => hn (Or.inl hx)
  have hy : y ≠ 0 := fun hy => hn (Or.inr hy)
  have hx' : (x : HahnSeries Γ R) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : HahnSeries Γ R) ≠ 0 := by exact_mod_cast hy
  have hxu : IsUnit (x : HahnSeries Γ R).leadingCoeff :=
    line_isUnit B (by rw [HahnSeries.leadingCoeff_eq]; exact x.property _)
      (HahnSeries.leadingCoeff_ne_zero.mpr hx')
  have hyu : IsUnit (y : HahnSeries Γ R).leadingCoeff :=
    line_isUnit B (by rw [HahnSeries.leadingCoeff_eq]; exact y.property _)
      (HahnSeries.leadingCoeff_ne_zero.mpr hy')
  have hh := congrArg (fun z : coefficientRing B h0 hB =>
    (z : HahnSeries Γ R).coeff ((x : HahnSeries Γ R).order + (y : HahnSeries Γ R).order)) hxy
  change ((x : HahnSeries Γ R)*(y : HahnSeries Γ R)).coeff _ = 0 at hh
  rw [HahnSeries.coeff_mul_order_add_order] at hh
  exact (hxu.mul hyu).ne_zero hh

end
end RationalHitting.QuantumSeries


/- Noncommutative version of the geometric Hahn-series argument used for the
   quantum division lift in the main hitting-list construction. -/
namespace RationalHitting.HahnGeometric
open HahnSeries HahnSeries.SummableFamily Finset Function
noncomputable section
variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Ring R]

theorem power_finite_co_support {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (g : Γ) :
    Set.Finite {a | ((fun n ↦ x ^ n) a).coeff g ≠ 0} := by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) :=
    isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt hx)
  by_cases h0 : x = 0; · exact h0 ▸ Set.Finite.subset (Set.finite_singleton 0) (co_support_zero g)
  by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  apply hpwo.isWF.induction hg
  intro y ys hy
  refine ((((antidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion
    fun ij hij => hy ij.snd (Finset.mem_antidiagonal.1 (mem_coe.1 hij)).2.1 ?_).image Nat.succ).union
      (Set.finite_singleton 0)).subset ?_
  · obtain ⟨hi, _, rfl⟩ := Finset.mem_antidiagonal.1 (mem_coe.1 hij)
    exact lt_add_of_pos_left ij.2 <| lt_of_lt_of_le ((zero_lt_orderTop_iff h0).mp hx) <|
      order_le_of_coeff_ne_zero <| Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hn
      refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
      simp only [mem_coe, Finset.mem_antidiagonal, HahnSeries.mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

/-- A summable family of geometricPowers of a Hahn series `x`. If `x` has non-positive `orderTop`, then
return a junk value given by pretending `x = 0`. -/
@[simps]
def geometricPowers (x : R⟦Γ⟧) : SummableFamily Γ R ℕ where
  toFun n := (if 0 < x.orderTop then x else 0) ^ n
  isPWO_iUnion_support' := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt h)
    · simp only [h, ↓reduceIte]
      apply isPWO_iUnion_support_powers
      rw [order_zero]
  finite_co_support' g := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact power_finite_co_support h g
    · simp only [h, ↓reduceIte]
      exact power_finite_co_support (orderTop_zero (R := R) (Γ := Γ) ▸ WithTop.top_pos) g

theorem geometricPowers_of_orderTop_pos {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (n : ℕ) :
    geometricPowers x n = x ^ n := by
  simp [hx]

@[simp]
theorem geometricPowers_zero : geometricPowers (0 : R⟦Γ⟧) = .single 0 1 := by
  ext n
  rw [geometricPowers_of_orderTop_pos (by simp)]
  obtain rfl | ha := eq_or_ne n 0 <;> simp [*]

variable {x : R⟦Γ⟧} (hx : 0 < x.orderTop)

include hx in
@[simp]
theorem coe_geometricPowers : ⇑(geometricPowers x) = HPow.hPow x := by
  ext1 n
  simp [hx]

include hx in
theorem embDomain_succ_smul_geometricPowers :
    (x • geometricPowers x).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      geometricPowers x - SummableFamily.ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · simp [hx]
  · -- FIXME: smul_eq_mul introduces type confusion between HahnModule and HahnSeries.
    simp [embDomain_apply, of_symm_smul_of_eq_mul, geometricPowers_of_orderTop_pos hx, pow_succ',
      -smul_eq_mul]

include hx in
theorem one_sub_self_mul_hsum_geometricPowers : (1 - x) * (geometricPowers x).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (geometricPowers x), one_smul, hsum_sub, ←
    hsum_embDomain (x • geometricPowers x) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_geometricPowers hx]
  simp

/-- A unit leading coefficient permits the usual normalization, without any
commutativity assumption on the coefficient ring. -/
lemma normalized_pos (x : HahnSeries Γ R) (u : Rˣ)
    (hu : x.leadingCoeff = (u : R)) :
    0 < (1 - single (-x.order) (↑u⁻¹ : R) * x).orderTop := by
  let y := x - single x.order x.leadingCoeff
  have hi : (↑u⁻¹ : R) * x.leadingCoeff = 1 := by rw [hu]; simp
  by_cases hy : y = 0
  · have hx : x = single x.order x.leadingCoeff := sub_eq_zero.mp hy
    have hh : single (-x.order) (↑u⁻¹ : R) * x = 1 := by
      calc
        _ = single (-x.order) (↑u⁻¹ : R) * single x.order x.leadingCoeff :=
          congrArg (fun z => single (-x.order) (↑u⁻¹ : R) * z) hx
        _ = 1 := by rw [single_mul_single, hi, neg_add_cancel, single_zero_one]
    simp [hh]
  · have hy' : 0 < (single (-x.order) (↑u⁻¹ : R) * y).order := by
      rw [order_single_mul_of_isRegular (u⁻¹).isUnit.isRegular hy]
      have : x.order < y.order :=
        order_lt_order_of_eq_add_single (sub_add_cancel x _).symm hy
      simpa using add_lt_add_left this (-x.order)
    have heq : 1 - single (-x.order) (↑u⁻¹ : R) * x =
        -(single (-x.order) (↑u⁻¹ : R) * y) := by
      calc
        _ = 1 - single (-x.order) (↑u⁻¹ : R) * (y + single x.order x.leadingCoeff) :=
          congrArg (fun z => 1 - single (-x.order) (↑u⁻¹ : R) * z) (sub_add_cancel x _).symm
        _ = _ := by rw [mul_add, single_mul_single, hi, neg_add_cancel, single_zero_one]; abel
    rw [heq, orderTop_neg]
    exact zero_lt_orderTop_of_order hy'

lemma normalized_right_inverse (x : HahnSeries Γ R) (u : Rˣ)
    (hu : x.leadingCoeff = (u : R)) :
    x * ((geometricPowers (1-single (-x.order) (↑u⁻¹ : R)*x)).hsum *
      single (-x.order) (↑u⁻¹ : R)) = 1 := by
  let v : HahnSeries Γ R := single (-x.order) (↑u⁻¹ : R)
  let v' : HahnSeries Γ R := single x.order (u : R)
  have hv : v' * v = 1 := by simp [v', v, single_mul_single]
  have hh := one_sub_self_mul_hsum_geometricPowers (normalized_pos x u hu)
  rw [sub_sub_cancel] at hh
  change (v*x)*(geometricPowers (1-v*x)).hsum = 1 at hh
  calc
    _ = (v'*((v*x)*(geometricPowers (1-v*x)).hsum))*v := by simp only [← mul_assoc, hv, one_mul]; rfl
    _ = 1 := by rw [hh, mul_one, hv]

end
end RationalHitting.HahnGeometric


namespace RationalHitting.QuantumSeries
open HahnSeries HahnSeries.SummableFamily
open RationalHitting.HahnGeometric
open scoped BigOperators
noncomputable section
variable {Γ K R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [Ring R] [Algebra K R] [Nontrivial R]
variable (B : Γ → Rˣ) (h0 : B 0 = 1)
  (hB : ∀ g h, ∃ c : K, (B g : R)*(B h : R) = c • (B (g+h) : R))

lemma line_inv_unit.{v_1, v_2, v_3} {Γ : Type v_1} {K : Type v_2}
  {R : Type v_3} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K] [Ring R]
  [Algebra K R] [Nontrivial R] (B : Γ → Rˣ) (h0 : B 0 = 1)
  (hB : ∀ (g h : Γ), ∃ c : K, (B g : R) * (B h : R) = c • (B (g + h) : R))
  {g : Γ} (u : Rˣ)
  (hu : ↑u ∈ RationalHitting.QuantumSeries.line (K := K) B g) :
  ↑u⁻¹ ∈ RationalHitting.QuantumSeries.line (K := K) B (-g) := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨c, hc⟩ := hB g (-g)
  rw [add_neg_cancel, h0, Units.val_one] at hc
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha; exact u.ne_zero ha.symm
  have hc0 : c ≠ 0 := by
    intro h
    simp only [h, zero_smul] at hc
    exact ((B g).isUnit.mul (B (-g)).isUnit).ne_zero hc
  have hy : (u : R) * ((a*c)⁻¹ • (B (-g) : R)) = 1 := by
    rw [← ha, smul_mul_assoc, mul_smul_comm, hc, smul_smul, smul_smul]
    rw [show a*(a*c)⁻¹*c = 1 by field_simp, one_smul]
  have heq : (↑u⁻¹ : R) = (a*c)⁻¹ • (B (-g) : R) := by
    calc
      _ = (↑u⁻¹ : R) * 1 := (mul_one _).symm
      _ = (↑u⁻¹ : R) * ((u : R) * ((a*c)⁻¹ • (B (-g) : R))) := by rw [hy]
      _ = _ := by rw [← mul_assoc]; simp
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

lemma single_mem {g : Γ} {r : R} (hr : r ∈ line (K := K) B g) :
    single g r ∈ coefficientRing B h0 hB := by
  intro a
  by_cases h : g = a
  · subst a; simpa using hr
  · simp [Ne.symm h]

lemma hsum_mem {α : Type*} (x : SummableFamily Γ R α)
    (hx : ∀ i, x i ∈ coefficientRing B h0 hB) :
    x.hsum ∈ coefficientRing B h0 hB := by
  intro g
  rw [coeff_hsum_eq_sum]
  apply Submodule.sum_mem
  intro i hi
  exact hx i g

lemma inverse_candidate_mem (x : HahnSeries Γ R)
    (hx : x ∈ coefficientRing B h0 hB) (u : Rˣ) (hu : x.leadingCoeff = (u : R)) :
    (geometricPowers (1-single (-x.order) (↑u⁻¹ : R)*x)).hsum *
      single (-x.order) (↑u⁻¹ : R) ∈ coefficientRing B h0 hB := by
  have hline : x.leadingCoeff ∈ line (K := K) B x.order := by
    rw [leadingCoeff_eq]; exact hx _
  let v : HahnSeries Γ R := single (-x.order) (↑u⁻¹ : R)
  have hv : v ∈ coefficientRing B h0 hB :=
    single_mem B h0 hB (line_inv_unit B h0 hB u (hu ▸ hline))
  let z : HahnSeries Γ R := 1-v*x
  have hz : z ∈ coefficientRing B h0 hB :=
    (coefficientRing B h0 hB).sub_mem (coefficientRing B h0 hB).one_mem
      ((coefficientRing B h0 hB).mul_mem hv hx)
  have hz0 : 0 < z.orderTop := normalized_pos x u hu
  have hpow : ∀ i, geometricPowers z i ∈ coefficientRing B h0 hB := by
    intro i
    rw [geometricPowers_of_orderTop_pos hz0]
    exact (coefficientRing B h0 hB).pow_mem hz i
  exact (coefficientRing B h0 hB).mul_mem (hsum_mem B h0 hB _ hpow) hv

lemma inverse_exists (x : coefficientRing B h0 hB) (hx : x ≠ 0) :
    ∃ y : coefficientRing B h0 hB, x*y = 1 := by
  have hx' : (x : HahnSeries Γ R) ≠ 0 := by
    intro h; apply hx; exact Subtype.ext h
  have hline : (x : HahnSeries Γ R).leadingCoeff ∈
      line (K := K) B (x : HahnSeries Γ R).order := by
    rw [leadingCoeff_eq]; exact x.property _
  obtain ⟨u, hu⟩ := line_isUnit (K := K) B hline (leadingCoeff_ne_zero.mpr hx')
  let y : HahnSeries Γ R := (geometricPowers
    (1-single (-(x : HahnSeries Γ R).order) (↑u⁻¹ : R)*(x : HahnSeries Γ R))).hsum *
      single (-(x : HahnSeries Γ R).order) (↑u⁻¹ : R)
  have hy : y ∈ coefficientRing B h0 hB :=
    inverse_candidate_mem B h0 hB x x.property u hu.symm
  have heq := normalized_right_inverse (x : HahnSeries Γ R) u hu.symm
  refine ⟨⟨y, hy⟩, ?_⟩
  exact Subtype.ext heq

lemma coefficientRing_isUnit_or_eq_zero (x : coefficientRing B h0 hB) :
    IsUnit x ∨ x = 0 := by
  by_cases hx : x = 0
  · exact Or.inr hx
  left
  let := coefficientRing_noZeroDivisors B h0 hB
  obtain ⟨y, hy⟩ := inverse_exists B h0 hB x hx
  have hh : y*x = 1 := by
    have hz : x*(y*x-1) = 0 := by rw [mul_sub, ← mul_assoc, hy, one_mul, mul_one, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hx)
  exact ⟨⟨x,y,hy,hh⟩,rfl⟩

/-- An actual division ring containing all ordered quantum-monomial series;
no finite-dimensional-domain or external division-algebra theorem is assumed. -/
noncomputable abbrev divisionRing : DivisionRing (coefficientRing B h0 hB) :=
  DivisionRing.ofIsUnitOrEqZero (coefficientRing_isUnit_or_eq_zero B h0 hB)

end
end RationalHitting.QuantumSeries

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.QuantumMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.HahnMatrix
open HahnSeries Matrix
open scoped BigOperators
noncomputable section
variable {Γ R S : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Ring R] [Ring S]

lemma coeff_mul_support_superset (x y : HahnSeries Γ R) (a : Γ)
    (s t : Set Γ) (hs : s.IsPWO) (ht : t.IsPWO)
    (hxs : x.support ⊆ s) (hyt : y.support ⊆ t) :
    (x*y).coeff a = ∑ ij ∈ Finset.antidiagonal hs ht a,
      x.coeff ij.1 * y.coeff ij.2 := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_subset
  · intro ij hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    exact ⟨hxs hij.1, hyt hij.2.1, hij.2.2⟩
  · intro ij hij hnot
    rw [Finset.mem_antidiagonal] at hij
    by_cases hx : x.coeff ij.1 = 0
    · simp [hx]
    by_cases hy : y.coeff ij.2 = 0
    · simp [hy]
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr ⟨hx,hy,hij.2.2⟩))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def entry (x : HahnSeries Γ (Matrix ι ι R)) (i j : ι) : HahnSeries Γ R :=
  x.map (⟨fun A => A i j, rfl⟩ : ZeroHom (Matrix ι ι R) R)

@[simp] lemma entry_coeff.{v_1, v_2, v_4} {Γ : Type v_1} {R : Type v_2}
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Ring R] {ι : Type v_4} [Fintype ι]
  [DecidableEq ι] (x : HahnSeries Γ (Matrix ι ι R)) (i j : ι) (a : Γ) :
  (RationalHitting.HahnMatrix.entry x i j).coeff a = x.coeff a i j := rfl

lemma entry_support.{v_1, v_2, v_4} {Γ : Type v_1} {R : Type v_2}
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Ring R] {ι : Type v_4} [Fintype ι]
  [DecidableEq ι] (x : HahnSeries Γ (Matrix ι ι R)) (i j : ι) :
  (RationalHitting.HahnMatrix.entry x i j).support ⊆ x.support := by
  intro a ha
  change x.coeff a ≠ 0
  intro h
  exact ha (by change x.coeff a i j = 0; rw [h]; rfl)

def split : HahnSeries Γ (Matrix ι ι R) →+* Matrix ι ι (HahnSeries Γ R) where
  toFun x := entry x
  map_zero' := by ext i j a; rfl
  map_one' := by
    ext i j a
    change (1 : HahnSeries Γ (Matrix ι ι R)).coeff a i j =
      (if i = j then (1 : HahnSeries Γ R) else 0).coeff a
    by_cases hi : i = j <;> by_cases ha : a = 0 <;> simp [hi,ha]
  map_add' x y := by ext i j a; rfl
  map_mul' x y := by
    ext i j a
    change (x*y).coeff a i j = (∑ k, entry x i k * entry y k j).coeff a
    rw [HahnSeries.coeff_mul, Matrix.sum_apply, HahnSeries.coeff_sum]
    simp_rw [coeff_mul_support_superset _ _ a x.support y.support
      x.isPWO_support y.isPWO_support (entry_support x i _) (entry_support y _ j)]
    rw [Finset.sum_comm]
    rfl

end
end RationalHitting.HahnMatrix


namespace RationalHitting.QuantumMatrices
open Matrix
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- The Weyl monomial D^a S^b. -/
def weyl (a b : ZMod d) : Matrix (ZMod d) (ZMod d) K :=
  fun i j => if i = j+b then χ (a*i) else 0

@[simp] lemma weyl_zero.{v_1} {K : Type v_1} [Field K] {d : ℕ} [NeZero d]
  (χ : AddChar (ZMod d) K) : RationalHitting.QuantumMatrices.weyl χ 0 0 = 1 := by
  ext i j
  simp [weyl, Matrix.one_apply]

lemma weyl_mul (a b c e : ZMod d) :
    weyl χ a b * weyl χ c e = χ (-c*b) • weyl χ (a+c) (b+e) := by
  classical
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (i-b)]
  · simp only [weyl, sub_add_cancel, ite_true, Matrix.smul_apply, smul_eq_mul]
    have heq : i-b = j+e ↔ i = j+(b+e) := by constructor <;> intro h <;> linear_combination h
    by_cases h : i = j+(b+e)
    · simp only [ite_eq_left (heq.mpr h), ite_eq_left h]
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    · simp [heq, h]
  · intro k hk hne
    have h : i ≠ k+b := by intro heq; apply hne; rw [heq]; ring
    simp [weyl, h]
  · simp

lemma weyl_inverse_right (a b : ZMod d) :
    weyl χ a b * (χ (-a*b) • weyl χ (-a) (-b)) = 1 := by
  rw [Matrix.mul_smul, weyl_mul, add_neg_cancel, add_neg_cancel, weyl_zero, smul_smul,
    ← AddChar.map_add_eq_mul]
  have h : -a*b + -(-a)*b = 0 := by ring
  rw [h, AddChar.map_zero_eq_one, one_smul]

lemma weyl_inverse_left (a b : ZMod d) :
    (χ (-a*b) • weyl χ (-a) (-b)) * weyl χ a b = 1 := by
  rw [Matrix.smul_mul, weyl_mul, neg_add_cancel, neg_add_cancel, weyl_zero, smul_smul,
    ← AddChar.map_add_eq_mul]
  have h : -a*b + -a*(-b) = 0 := by ring
  rw [h, AddChar.map_zero_eq_one, one_smul]

def weylUnit (a b : ZMod d) : (Matrix (ZMod d) (ZMod d) K)ˣ :=
  ⟨weyl χ a b, χ (-a*b) • weyl χ (-a) (-b),
    weyl_inverse_right χ a b, weyl_inverse_left χ a b⟩

@[simp] lemma weylUnit_val (a b : ZMod d) : (weylUnit χ a b : Matrix _ _ K) = weyl χ a b := rfl

@[simp] lemma weylUnit_zero : weylUnit χ 0 0 = 1 := by
  apply Units.ext
  exact weyl_zero χ

end
end RationalHitting.QuantumMatrices

namespace RationalHitting.QuantumMatrices
open Matrix
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K) (hχ : χ.IsPrimitive)

def fourierCoeff (R : Matrix (ZMod d) (ZMod d) K) (a b : ZMod d) : K :=
  (d : K)⁻¹ * ∑ j, χ (-a*j) * R j (j-b)

end
end RationalHitting.QuantumMatrices


namespace RationalHitting.QuantumLift
open HahnSeries Matrix
open RationalHitting.QuantumSeries RationalHitting.QuantumMatrices
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

abbrev Exponents := ℤ ×ₗ ℤ
abbrev Ambient := HahnSeries Exponents (Matrix (ZMod d) (ZMod d) K)

def monomialUnit (g : Exponents) : (Matrix (ZMod d) (ZMod d) K)ˣ :=
  weylUnit χ (ofLex g).1 (ofLex g).2

lemma monomialUnit_zero.{v_1} {K : Type v_1} [Field K] [CharZero K] {d : ℕ}
  [NeZero d] (χ : AddChar (ZMod d) K) : RationalHitting.QuantumLift.monomialUnit χ 0 = 1 := by
  simp [monomialUnit]

lemma monomialUnit_mul.{v_1} {K : Type v_1} [Field K] [CharZero K] {d : ℕ}
  [NeZero d] (χ : AddChar (ZMod d) K) (g h : RationalHitting.QuantumLift.Exponents) :
  ∃ c : K,
    (RationalHitting.QuantumLift.monomialUnit χ g : Matrix (ZMod d) (ZMod d) K) *
        (RationalHitting.QuantumLift.monomialUnit χ h : Matrix (ZMod d) (ZMod d) K) =
      c • (RationalHitting.QuantumLift.monomialUnit χ (g + h) : Matrix (ZMod d) (ZMod d) K) := by
  refine ⟨χ (-((ofLex h).1 : ZMod d) * ((ofLex g).2 : ZMod d)), ?_⟩
  simp [monomialUnit, weyl_mul]

abbrev DivisionSubring := coefficientRing (monomialUnit χ) (monomialUnit_zero χ) (monomialUnit_mul χ)

noncomputable instance instDivisionRingSubtypeHahnSeriesExponentsMatrixZModMemSubringDivisionSubring : DivisionRing (DivisionSubring χ) :=
  divisionRing (monomialUnit χ) (monomialUnit_zero χ) (monomialUnit_mul χ)

/-- The Fourier lift as a finite Hahn series. -/
def lift (R : Matrix (ZMod d) (ZMod d) K) : Ambient (K := K) (d := d) :=
  ∑ a : ZMod d, ∑ b : ZMod d,
    single (toLex ((a.val : ℤ), (b.val : ℤ))) (fourierCoeff χ R a b • weyl χ a b)

lemma lift_mem (R : Matrix (ZMod d) (ZMod d) K) : lift χ R ∈ DivisionSubring χ := by
  apply Subring.sum_mem
  intro a ha
  apply Subring.sum_mem
  intro b hb
  apply single_mem (monomialUnit χ) (monomialUnit_zero χ) (monomialUnit_mul χ)
  apply Submodule.mem_span_singleton.mpr
  refine ⟨fourierCoeff χ R a b, ?_⟩
  simp [monomialUnit]

def liftD (R : Matrix (ZMod d) (ZMod d) K) : DivisionSubring χ := ⟨lift χ R, lift_mem χ R⟩

/-- The representation used in the rank-gap argument. Its coefficient field
is a commutative Hahn field; all inversion takes place inside the division
subring, never by adjoining arbitrary matrix-field scalars. -/
def representation : DivisionSubring χ →+* Matrix (ZMod d) (ZMod d) (HahnSeries Exponents K) :=
  (RationalHitting.HahnMatrix.split (Γ := Exponents)).comp (DivisionSubring χ).subtype

end
end RationalHitting.QuantumLift

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BlockDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.PolynomialHahn
open HahnSeries MvPolynomial
open scoped BigOperators
noncomputable section
abbrev Exponents := ℤ ×ₗ ℤ
variable {K : Type*} [Field K]

def exponent (m : Fin 2 →₀ ℕ) : Exponents := toLex ((m 0 : ℤ), (m 1 : ℤ))

def variableSeries (i : Fin 2) : HahnSeries Exponents K :=
  single (if i = 0 then toLex (1,0) else toLex (0,1)) 1

def embed : MvPolynomial (Fin 2) K →+* HahnSeries Exponents K :=
  eval₂Hom (algebraMap K _) variableSeries

end
end RationalHitting.PolynomialHahn


namespace RationalHitting.BlockDivision
open Module Matrix
open scoped BigOperators
noncomputable section
variable {D E : Type*} [DivisionRing D] [Field E]
variable {m κ : Type*} [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]

def blockEmbedding (φ : D →+* Matrix (κ) (κ) E) :
    Matrix (m) (m) D →+* Matrix (m × κ) (m × κ) E where
  toFun A i j := φ (A i.1 j.1) i.2 j.2
  map_zero' := by ext i j; simp
  map_one' := by
    ext ⟨i,α⟩ ⟨j,β⟩
    simp only [Matrix.one_apply, Prod.mk.injEq]
    by_cases hij : i = j <;> by_cases hab : α = β <;> simp [hij, hab]
  map_add' A B := by
    ext i j
    change φ (A i.1 j.1 + B i.1 j.1) i.2 j.2 = _ + _
    simp
  map_mul' A B := by
    ext ⟨i,α⟩ ⟨j,β⟩
    change φ (∑ k, A i k * B k j) α β =
      ∑ k : m × κ, φ (A i k.1) α k.2 * φ (B k.1 j) k.2 β
    simp only [map_sum, map_mul, Matrix.sum_apply, Matrix.mul_apply,
      Fintype.sum_prod_type]

/-- A nonzero row of a division-ring kernel expands into d independent ordinary
kernel rows after a faithful d-dimensional representation. -/
def kernelRows (φ : D →+* Matrix (κ) (κ) E) (v : m → D) :
    (κ → E) →ₗ[E] (m × κ → E) where
  toFun x j := (x ᵥ* φ (v j.1)) j.2
  map_add' x y := by ext j; simp [Matrix.add_vecMul]
  map_smul' c x := by ext j; simp [Matrix.smul_vecMul]

end
end RationalHitting.BlockDivision


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Deformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.QuantumLift
open HahnSeries Matrix MvPolynomial
open RationalHitting.QuantumMatrices RationalHitting.PolynomialHahn
open RationalHitting.BlockDivision
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- The two-parameter polynomial lift. -/
def polynomialLift (R : Matrix (ZMod d) (ZMod d) K) :
    Matrix (ZMod d) (ZMod d) (MvPolynomial (Fin 2) K) := fun i j =>
  ∑ a : ZMod d, ∑ b : ZMod d,
    monomial (Finsupp.single 0 a.val + Finsupp.single 1 b.val)
      (fourierCoeff χ R a b * weyl χ a b i j)

variable {m : Type*} [Fintype m] [DecidableEq m]

def blockPolynomial (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    Matrix (m × ZMod d) (m × ZMod d) (MvPolynomial (Fin 2) K) :=
  fun i j => polynomialLift χ (A i.1 j.1) i.2 j.2

def blockOriginal (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    Matrix (m × ZMod d) (m × ZMod d) K := fun i j => A i.1 j.1 i.2 j.2

end
end RationalHitting.QuantumLift

namespace RationalHitting.ThreeLift
open Matrix Polynomial MvPolynomial
open QuantumMatrices QuantumLift
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [Field E] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- Coefficient polynomials for the exact cyclic-diagonal Fourier transform. -/
def coeffP (R : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) : K[X] :=
  Polynomial.C ((d : K)⁻¹) * ∑ j, Polynomial.C (χ (-a*j)) * R j (j-b)

def uni : K[X] →+* MvPolynomial (Fin 3) K :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

/-- The three-parameter polynomial lift, before specialization. -/
def lift (R : Matrix (ZMod d) (ZMod d) K[X]) :
    Matrix (ZMod d) (ZMod d) (MvPolynomial (Fin 3) K) := fun i j =>
  ∑ a : ZMod d, ∑ b : ZMod d,
    uni (coeffP χ R a b) * MvPolynomial.C (weyl χ a b i j) *
      MvPolynomial.X 1 ^ a.val * MvPolynomial.X 2 ^ b.val

end
end RationalHitting.ThreeLift

namespace RationalHitting.PencilDeformation
open Matrix Polynomial MvPolynomial
open TestPolynomial LaurentReduction
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
variable {w q M N : ℕ} [NeZero M]

def test (M N : ℕ) [NeZero M] (a : K) : Matrix (ZMod M) (ZMod M) K[X] :=
  (padded M N a).reindex (ZMod.finEquiv M).toEquiv (ZMod.finEquiv M).toEquiv

def polyBlocks (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
    Matrix (Fin q) (Fin q) (Matrix (ZMod M) (ZMod M) K[X]) :=
  fun α β => ∑ i, A i α β • test M N (points i)

def polynomial (χ : AddChar (ZMod M) K)
    (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
    Matrix (Fin q × ZMod M) (Fin q × ZMod M) (MvPolynomial (Fin 3) K) :=
  fun a b => ThreeLift.lift χ (polyBlocks (M := M) (N := N) A points a.1 b.1) a.2 b.2

end
end RationalHitting.PencilDeformation


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.CyclotomicGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.CyclotomicRing
open Polynomial Matrix Module
noncomputable section

def modulus (e : ℕ) : ℚ[X] := X^(2^e)+1

def degree (e : ℕ) : ℕ := 2^e

def dimension (e : ℕ) : ℕ := 2^(e+1)

lemma modulus_eq_cyclotomic (e : ℕ) : modulus e = cyclotomic (dimension e) ℚ := by
  rw [dimension,cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [modulus,Finset.sum_range_succ,add_comm]

instance modulus_irreducible (e : ℕ) : Fact (Irreducible (modulus e)) :=
  ⟨by rw [modulus_eq_cyclotomic]; exact cyclotomic.irreducible_rat (by unfold dimension; positivity)⟩

abbrev R (e : ℕ) := AdjoinRoot (modulus e)

lemma degree_pos (e : ℕ) : 0 < degree e := by unfold degree; positivity
lemma dimension_pos (e : ℕ) : 0 < dimension e := by unfold dimension; positivity

lemma modulus_monic (e : ℕ) : (modulus e).Monic := by
  simpa [modulus] using monic_X_pow_add_C (1 : ℚ) (pow_ne_zero e (by norm_num : (2 : ℕ) ≠ 0))

lemma modulus_natDegree (e : ℕ) : (modulus e).natDegree = degree e := by
  rw [modulus, degree, ← Polynomial.C_1, Polynomial.natDegree_X_pow_add_C]

def powerBasis (e : ℕ) : PowerBasis ℚ (R e) := AdjoinRoot.powerBasis' (modulus_monic e)

def basis (e : ℕ) : Basis (Fin (degree e)) ℚ (R e) :=
  (powerBasis e).basis.reindex (finCongr (modulus_natDegree e))

instance dimension_neZero (e : ℕ) : NeZero (dimension e) := ⟨(dimension_pos e).ne'⟩

instance charZero (e : ℕ) : CharZero (R e) :=
  CharZero.of_addMonoidHom (algebraMap ℚ (R e)).toAddMonoidHom
    (map_one (algebraMap ℚ (R e))) (algebraMap ℚ (R e)).injective

instance finite (e : ℕ) : Module.Finite ℚ (R e) :=
  (modulus_monic e).finite_adjoinRoot

def intoComplex (e : ℕ) : R e →ₐ[ℚ] ℂ := IsAlgClosed.lift

/-- The cyclotomic quotient is a field for the chosen powers of two.
Irreducibility allows regular-representation invertibility to be proved
at a single primitive root. -/
lemma root_primitive (e : ℕ) : IsPrimitiveRoot (AdjoinRoot.root (modulus e)) (dimension e) := by
  apply (Polynomial.isRoot_cyclotomic_iff).mp
  have hh := AdjoinRoot.isRoot_root (modulus e)
  rw [← Polynomial.map_cyclotomic (dimension e) (algebraMap ℚ (R e)),
    ← modulus_eq_cyclotomic e]
  exact hh

def character (e : ℕ) : AddChar (ZMod (dimension e)) (R e) :=
  AddChar.zmodChar (dimension e) (root_primitive e).pow_eq_one

def rho (e : ℕ) : R e →ₐ[ℚ] Matrix (Fin (degree e)) (Fin (degree e)) ℚ :=
  Algebra.leftMulMatrix (basis e)

end
end RationalHitting.CyclotomicRing


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Certificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.LocalSpecialization
open IsLocalization Matrix
noncomputable section
variable {P K E : Type*} [CommRing P] [Field K] [Field E]

def denominators (ev : P →+* K) : Submonoid P where
  carrier := {p | ev p ≠ 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change ev (x*y) ≠ 0
    rw [map_mul]
    exact mul_ne_zero hx hy

abbrev Regular (ev : P →+* K) := Localization (denominators ev)

def evaluate (ev : P →+* K) : Regular ev →+* K :=
  IsLocalization.lift (fun y : denominators ev => isUnit_iff_ne_zero.mpr y.property)

@[simp] lemma evaluate_algebraMap (ev : P →+* K) (p : P) :
    evaluate ev (algebraMap P (Regular ev) p) = ev p := IsLocalization.lift_eq _ _

def intoField (ev : P →+* K) (j : P →+* E) (hj : Function.Injective j) :
    Regular ev →+* E :=
  IsLocalization.lift (fun y : denominators ev => isUnit_iff_ne_zero.mpr (by
    intro hz
    have hy : (y : P) = 0 := hj (hz.trans (map_zero j).symm)
    exact y.property (by rw [hy,map_zero])))

@[simp] lemma intoField_algebraMap (ev : P →+* K) (j : P →+* E)
    (hj : Function.Injective j) (p : P) :
    intoField ev j hj (algebraMap P (Regular ev) p) = j p := IsLocalization.lift_eq _ _

end
end RationalHitting.LocalSpecialization

namespace RationalHitting.PencilCertificates
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
instance laurentCharZero {E : Type*} [Field E] [CharZero E] : CharZero (LaurentReduction.F E) :=
  CharZero.of_addMonoidHom (HahnSeries.C : E →+* LaurentReduction.F E).toAddMonoidHom
    (map_one (HahnSeries.C : E →+* LaurentReduction.F E)) HahnSeries.C_injective

variable {n q M N : ℕ} [NeZero M]

def coefficients (L : Matrix (Fin q) (Fin q) (Affine.Form n)) :
    Fin (n+1) → Matrix (Fin q) (Fin q) K :=
  fun i a b => (algebraMap ℚ K) (Affine.coeff (L a b) i)

def lifts (χ : AddChar (ZMod M) K) (N n : ℕ) :
    Fin (n+1) → Matrix (ZMod M) (ZMod M) (MvPolynomial (Fin 3) K) :=
  fun i => ThreeLift.lift χ (PencilDeformation.test M N (i.val : K))

def polynomial (χ : AddChar (ZMod M) K) (N : ℕ)
    (L : Matrix (Fin q) (Fin q) (Affine.Form n)) :=
  PencilDeformation.polynomial (N := N) χ (coefficients (K := K) L) (fun i => (i.val : K))

def determinant (χ : AddChar (ZMod M) K) (N : ℕ)
    (L : Matrix (Fin q) (Fin q) (Affine.Form n)) := (polynomial χ N L).det

end
end RationalHitting.PencilCertificates

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.Generator
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section

def D (e : ℕ) : ℕ := CyclotomicRing.dimension e * CyclotomicRing.degree e

/-- Entrywise regular representation, flattening and fixed row-major reindexing. -/
def regular (e : ℕ) : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
    (CyclotomicRing.R e) →+* Mat (D e) :=
  (Matrix.reindexRingEquiv ℚ ((Equiv.prodCongr (ZMod.finEquiv (CyclotomicRing.dimension e)).symm.toEquiv
    (Equiv.refl (Fin (CyclotomicRing.degree e)))).trans finProdFinEquiv)).toRingHom.comp
    ((Matrix.compRingEquiv _ _ ℚ).toRingHom.comp (CyclotomicRing.rho e).toRingHom.mapMatrix)

/-- The fixed lexicographic three-dimensional integer grid, encoded by Fin H. -/
def grid (H : ℕ) : List (Fin 3 → Fin H) :=
  (List.finRange H).flatMap fun t => (List.finRange H).flatMap fun p =>
    (List.finRange H).map fun r => ![t,p,r]

/-- The polynomial lift is evaluated over the exact rational quotient. -/
def Zring (n N e : ℕ) (x : Fin 3 → ℕ) (i : Fin (n+1)) :
    Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e)) (CyclotomicRing.R e) :=
  (eval₂Hom (RingHom.id _) (fun j => (x j : CyclotomicRing.R e))).mapMatrix
    (PencilCertificates.lifts (CyclotomicRing.character e) N n i)

def Z (n N e : ℕ) (x : Fin 3 → ℕ) (i : Fin (n+1)) : Mat (D e) := regular e (Zring n N e x i)

def tupleAt (n N e : ℕ) (x : Fin 3 → ℕ) : Tuple n (D e) :=
  fun i => (Z n N e x 0)⁻¹ * Z n N e x i.succ

/-- The filtering step tests only Z_0, and receives no formula. -/
def atPoint (n N e : ℕ) (x : Fin 3 → ℕ) : Option (Tuple n (D e)) :=
  if (Z n N e x 0).det = 0 then none else some (tupleAt n N e x)

def output (n N e H : ℕ) : Output n where
  dimension := D e
  dimension_pos := Nat.mul_pos (CyclotomicRing.dimension_pos e) (CyclotomicRing.degree_pos e)
  tuples := (grid H).filterMap (fun x => atPoint n N e (fun i => (x i).val+1))

end
end RationalHitting.Generator

namespace RationalHitting.Generator
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section

abbrev WitnessField := HahnSeries QuantumLift.Exponents ℂ
instance witnessCharZero : CharZero WitnessField :=
  CharZero.of_addMonoidHom (HahnSeries.C : ℂ →+* WitnessField).toAddMonoidHom
    (map_one (HahnSeries.C : ℂ →+* WitnessField)) HahnSeries.C_injective

def witnessEmbedding (e : ℕ) : CyclotomicRing.R e →+* WitnessField :=
  (HahnSeries.C : ℂ →+* WitnessField).comp (CyclotomicRing.intoComplex e).toRingHom

def finPencil {n : ℕ} (f : Formula n) :
    Matrix (Fin (Fintype.card f.Index)) (Fin (Fintype.card f.Index)) (Affine.Form n) :=
  (Formula.pencil f).reindex (Fintype.equivFin f.Index) (Fintype.equivFin f.Index)

def onePencil (n : ℕ) : Matrix (Fin 1) (Fin 1) (Affine.Form n) := fun _ _ => Affine.constant 1

def conditions {n : ℕ} (N e : ℕ) (f : Formula n) : List (MvPolynomial (Fin 3) (CyclotomicRing.R e)) :=
  PencilCertificates.determinant (CyclotomicRing.character e) N (onePencil n) ::
    f.certificates.map (fun h => PencilCertificates.determinant (CyclotomicRing.character e) N (finPencil h))

end
end RationalHitting.Generator

namespace RationalHitting.Parameters

/-- The parameters, with M the least power of two strictly above BΔ. -/
def w (n : ℕ) := n+1
def B (s : ℕ) := 2*s+1
def delta (n s : ℕ) := 2*(w n)^3*B s
def exponent (n s : ℕ) := Nat.log 2 (B s * delta n s)
def M (n s : ℕ) := 2^(exponent n s+1)
def N (n s : ℕ) := M n s-delta n s
def H (n s : ℕ) := 1+3*(s+2)*B s*(M n s)^3

end RationalHitting.Parameters

namespace RationalHitting.Generator
noncomputable section

/-- The list with all parameters fixed by the unary inputs. -/
def list (n s : ℕ) : Output n :=
  output n (Parameters.N n s) (Parameters.exponent n s) (Parameters.H n s)

end
end RationalHitting.Generator

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.IntegralLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.CyclotomicRing
open Polynomial Matrix Module
noncomputable section

def signedEntry (e : ℕ) (a : ZMod (dimension e)) (i j : Fin (degree e)) : ℤ :=
  if (a.val+j.val) % degree e = i.val then (-1 : ℤ)^((a.val+j.val)/degree e) else 0

end
end RationalHitting.CyclotomicRing


namespace RationalHitting.IntegralTest
open Polynomial Matrix
open scoped BigOperators

/-- Integer computation of the exact expanded Taylor-reversal matrix at t. -/
def full (M : ℕ) (a t : ℤ) : Matrix (Fin M) (Fin M) ℤ := fun i j =>
  ∑ r : Fin M, ((-a)^(r.rev.val-i.val)*(r.rev.val.choose i.val : ℤ)) *
    (a^(j.val-r.val)*(j.val.choose r.val : ℤ)) * t^r.val

def padded (M N : ℕ) (a t : ℤ) : Matrix (Fin M) (Fin M) ℤ :=
  fun i j => if j.val < N then full M a t i j else 0

end RationalHitting.IntegralTest


namespace RationalHitting.IntegralLift
open _root_.OAI.RationalHitting.CyclotomicRing Matrix
open scoped BigOperators
noncomputable section

/-- The fixed signed-monomial integer formula for M times a regular lift entry. -/
def entry (e : ℕ) (T : Matrix (ZMod (dimension e)) (ZMod (dimension e)) ℤ)
    (p r : ℤ) (u v : ZMod (dimension e)) (i j : Fin (degree e)) : ℤ :=
  ∑ a : ZMod (dimension e), ∑ b : ZMod (dimension e), ∑ k : ZMod (dimension e),
    if u = v+b then T k (k-b)*signedEntry e (-a*k+a*u) i j*p^a.val*r^b.val else 0

end
end RationalHitting.IntegralLift

namespace RationalHitting.Generator
open Matrix
open scoped BigOperators
noncomputable section

/-- Fixed row-major block coordinate. -/
def coordinate (e : ℕ) : ZMod (CyclotomicRing.dimension e) × Fin (CyclotomicRing.degree e) ≃ Fin (D e) :=
  (Equiv.prodCongr (ZMod.finEquiv (CyclotomicRing.dimension e)).symm.toEquiv
    (Equiv.refl (Fin (CyclotomicRing.degree e)))).trans finProdFinEquiv

/-- Exact integer Taylor matrices, with the same fixed order of residues. -/
def integerTest (N e : ℕ) (a t : ℤ) :
    Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e)) ℤ :=
  (IntegralTest.padded (CyclotomicRing.dimension e) N a t).reindex
    (ZMod.finEquiv (CyclotomicRing.dimension e)).toEquiv
    (ZMod.finEquiv (CyclotomicRing.dimension e)).toEquiv

/-- The common-denominator-cleared regular matrices used in exact arithmetic. -/
def U (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n+1)) : Matrix (Fin (D e)) (Fin (D e)) ℤ :=
  fun i j => IntegralLift.entry e (integerTest N e (a.val : ℤ) (x 0 : ℤ))
    (x 1 : ℤ) (x 2 : ℤ) ((coordinate e).symm i).1 ((coordinate e).symm j).1
      ((coordinate e).symm i).2 ((coordinate e).symm j).2

end
end RationalHitting.Generator

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.EncodingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.EncodingBounds
open Matrix
open scoped BigOperators

lemma encodeNat_length (a : ℕ) : (encodeNat a).length = 2*(Nat.digits 2 a).length+1 := by
  simp [encodeNat]
  omega

lemma encodeNat_le (a L : ℕ) (ha : a < 2^L) : (encodeNat a).length ≤ 2*L+1 := by
  rw [encodeNat_length]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 ((Nat.digits_length_le_iff (by omega) a).mpr ha)) 1

lemma ratio_num_le (a b : ℤ) (hb : b ≠ 0) : (Rat.divInt a b).num.natAbs ≤ a.natAbs := by
  by_cases ha : a = 0
  · simp [ha]
  · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd a hb) ha

lemma ratio_den_le (a b : ℤ) (hb : b ≠ 0) : (Rat.divInt a b).den ≤ b.natAbs := by
  simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero (Rat.den_dvd a b) hb

lemma encodeRat_ratio_le (a b : ℤ) (hb : b ≠ 0) (L : ℕ)
    (ha : a.natAbs < 2^L) (hb' : b.natAbs < 2^L) :
    (encodeRat (Rat.divInt a b)).length ≤ 4*L+3 := by
  have hn := encodeNat_le _ L (lt_of_le_of_lt (ratio_num_le a b hb) ha)
  have hd := encodeNat_le _ L (lt_of_le_of_lt (ratio_den_le a b hb) hb')
  simp only [encodeRat,List.length_append,List.length_singleton]
  omega

end RationalHitting.EncodingBounds


namespace RationalHitting.PolynomialBounds

/-- Exponent bounding all denominator-cleared matrix entries by a power of 2. -/
def logarithmic (n s : ℕ) : ℕ :=
  4*Parameters.M n s + 4*Parameters.M n s*(n+1) + 3*Parameters.M n s*Parameters.H n s

def logConstant : ℕ := 64+64+3*16*24577

def bitConstant : ℕ := 4*(256*256+256*logConstant+1)+3

def outputConstant : ℕ := (2*256+3) + (2*24577^3+3) + 24577^3*256*256*bitConstant

end RationalHitting.PolynomialBounds


/-! A staged division-free determinant computation for integer matrices.
Explicit dense tables prevent recursive matrix-entry recomputation. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.DeterminantAlgorithm
open Matrix
open scoped BigOperators

abbrev Table (n : ℕ) := Vector (Vector ℤ n) n

def denote {n : ℕ} (A : Table n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (A.get i).get j

def tabulate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Table n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

@[simp] lemma denote_tabulate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    denote (tabulate A) = A := by ext i j; simp [denote,tabulate]

def step {n : ℕ} (A F : Table n) : Table n :=
  tabulate (BirdDet.Spec.stepEntry (denote A) (denote F))

def stages {n : ℕ} (A : Table n) : ℕ → Table n
  | 0 => A
  | k+1 => step A (stages A k)

def determinant : {n : ℕ} → Table n → ℤ
  | 0, _ => 1
  | k+1,A => (-1 : ℤ)^k * denote (stages A k) 0 0

/- Bridges between the matrix specification and the array determinant. -/

end RationalHitting.DeterminantAlgorithm

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Executable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.ExecutableGenerator
open Matrix DeterminantAlgorithm

/-- Dense, staged integer input tables. No quotient-field element is computed. -/
def inputTables (n N e : ℕ) (x : Fin 3 → ℕ) : Vector (Table (Generator.D e)) (n+1) :=
  Vector.ofFn fun a => tabulate (Generator.U n N e x a)

@[simp] lemma inputTables_denote (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n+1)) :
    denote ((inputTables n N e x).get a) = Generator.U n N e x a := by
  simp [inputTables]

/-- Cramer's numerators are computed by the staged division-free algorithm. -/
def normalizedEntry {d : ℕ} (A B : Table d) (den : ℤ) (i j : Fin d) : ℚ :=
  Rat.divInt (determinant (tabulate ((denote A).updateCol i (fun r => denote B r j)))) den

abbrev RationalTable (n d : ℕ) := Vector (Vector (Vector ℚ d) d) n

def tuple {n d : ℕ} (T : RationalTable n d) : Tuple n d :=
  fun a i j => ((T.get a).get i).get j

def normalized {n d : ℕ} (A : Vector (Table d) (n+1)) (den : ℤ) : RationalTable n d :=
  Vector.ofFn fun a => Vector.ofFn fun i => Vector.ofFn fun j =>
    normalizedEntry (A.get 0) (A.get a.succ) den i j

@[simp] lemma tuple_normalized {n d : ℕ} (A : Vector (Table d) (n+1)) (den : ℤ)
    (a : Fin n) (i j : Fin d) :
    tuple (normalized A den) a i j = normalizedEntry (A.get 0) (A.get a.succ) den i j := by
  simp [tuple,normalized]

/-- The only singularity test; all repeated algebra is materialized in dense tables. -/
def atPoint (n N e : ℕ) (x : Fin 3 → ℕ) : Option (Tuple n (Generator.D e)) :=
  let A := inputTables n N e x
  let den := determinant (A.get 0)
  if den = 0 then none else some (tuple (normalized A den))

/-- A computable generator preserving the list and its order. -/
def output (n N e H : ℕ) : Output n where
  dimension := Generator.D e
  dimension_pos := Nat.mul_pos (CyclotomicRing.dimension_pos e) (CyclotomicRing.degree_pos e)
  tuples := (Generator.grid H).filterMap fun x => atPoint n N e (fun i => (x i).val+1)

def list (n s : ℕ) : Output n :=
  output n (Parameters.N n s) (Parameters.exponent n s) (Parameters.H n s)

def encoded (n s : ℕ) : List Bool := encodeOutput (list n s)

end RationalHitting.ExecutableGenerator


namespace RationalHitting.ExecutableGenerator

/-- A finite-state implementation with polynomial transition count. -/


def Implementation : Prop :=
  ∃ (m : ℕ) (G : Machine m) (C k : ℕ), 0 < C ∧ 0 < k ∧
    ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → OutputsWithin G s (C*(n+s+1)^k) (list n s)

end RationalHitting.ExecutableGenerator


/-! Quantitative compilation measured in ordinary TM0 transitions. -/

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.StackLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite structured binary-stack language. Every primitive is a push,
pop, or transfer. -/
namespace RationalHitting.StackLanguage
open Turing
variable {K : Type} [DecidableEq K]

inductive Program (K : Type) where
  | skip : Program K
  | push : K → Bool → Program K
  | drop : K → Program K
  | transfer : K → K → Program K
  | seq : Program K → Program K → Program K
  | branch : K → Program K → Program K → Program K → Program K
  | loop : K → Program K → Program K
  deriving DecidableEq

abbrev Store (K : Type) := K → List Bool
abbrev Labels (K : Type) := Option (List (Program K))

/-- Move one head symbol if present, popping the first register before
updating the second, including when both registers coincide. -/
def transfer (a b : K) (s : Store K) : Store K :=
  match (s a).head? with
  | none => s
  | some x => Function.update (Function.update s a (s a).tail) b
      (x :: (Function.update s a (s a).tail) b)

inductive Eval : Program K → Store K → Store K → ℕ → Prop where
  | skip (s : Store K) : Eval .skip s s 1
  | push (k : K) (b : Bool) (s : Store K) :
    Eval (.push k b) s (Function.update s k (b::s k)) 1
  | drop (k : K) (s : Store K) : Eval (.drop k) s (Function.update s k (s k).tail) 1
  | transfer (a b : K) (s : Store K) : Eval (.transfer a b) s (transfer a b s) 1
  | seq {p q : Program K} {s u v : Store K} {t w : ℕ} :
    Eval p s u t → Eval q u v w → Eval (.seq p q) s v (1+t+w)
  | branchNone {k : K} {p q r : Program K} {s v : Store K} {t : ℕ} :
    s k = [] → Eval p s v t → Eval (.branch k p q r) s v (1+t)
  | branchFalse {k : K} {p q r : Program K} {s v : Store K} {t : ℕ} {ls : List Bool} :
    s k = false::ls → Eval q s v t → Eval (.branch k p q r) s v (1+t)
  | branchTrue {k : K} {p q r : Program K} {s v : Store K} {t : ℕ} {ls : List Bool} :
    s k = true::ls → Eval r s v t → Eval (.branch k p q r) s v (1+t)
  | whileNil {k : K} {p : Program K} {s : Store K} :
    s k = [] → Eval (.loop k p) s s 1
  | whileCons {k : K} {p : Program K} {s u v : Store K} {t w : ℕ} :
    s k ≠ [] → Eval p s u t → Eval (.loop k p) u v w → Eval (.loop k p) s v (1+t+w)

variable (K) in
abbrev Stmt := TM2.Stmt (fun _ : K => Bool) (Labels K) (Option Bool)

def jump (ps : List (Program K)) : Stmt K :=
  .load (fun _ => none) (.goto (fun _ => some ps))

def cfg (ps : List (Program K)) (s : Store K) : TM2.Cfg (fun _ : K => Bool) (Labels K) (Option Bool) :=
  ⟨some (some ps),none,s⟩

@[simp] theorem jump_eval (ps : List (Program K)) (v : Option Bool) (s : Store K) :
    TM2.stepAux (jump ps) v s = cfg ps s := rfl

/-- Finite control locations, computed structurally, despite unbounded loop
iteration counts. -/
def locations : Program K → List (Program K) → Finset (List (Program K))
  | p@(.skip),ps | p@(.push ..),ps | p@(.drop ..),ps | p@(.transfer ..),ps => {p::ps,ps}
  | p@(.seq a b),ps => insert (p::ps) (locations a (b::ps) ∪ locations b ps)
  | p@(.branch _ a b c),ps => insert (p::ps) (locations a ps ∪ locations b ps ∪ locations c ps)
  | p@(.loop _ a),ps => insert (p::ps) (insert ps (locations a (p::ps)))

@[simp] theorem entry_mem (p : Program K) (ps : List (Program K)) : p::ps ∈ locations p ps := by
  cases p <;> simp [locations]

@[simp] theorem exit_mem (p : Program K) (ps : List (Program K)) : ps ∈ locations p ps := by
  induction p generalizing ps <;> simp_all [locations]

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Compiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.ExecutableGenerator
open Turing StackLanguage

/-- A fixed finite stack program with literal unary input and exact
canonical output, bounded by a fixed polynomial in the input length. -/

def unaryWord (n s : ℕ) : List Bool :=
  List.replicate n true ++ [false] ++ List.replicate s true

def StackImplementation : Prop :=
  ∃ (r : ℕ) (p : Program (Fin (r+1))) (ki ko : Fin (r+1)) (C k : ℕ),
    0<C ∧ 0<k ∧ ∀ n s : ℕ, 1 ≤ n → 1 ≤ s →
      ∃ t≤C*(n+s+1)^k,
        Eval p (Function.update (fun _ => []) ki (unaryWord n s))
          (Function.update (fun _ => []) ko (encoded n s).reverse) t

end RationalHitting.ExecutableGenerator

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.StackWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

def clear (a : K) : Program K := .loop a (.drop a)
def reverse (a b : K) : Program K := .loop a (.transfer a b)

lemma eval_clear (a : K) (s : Store K) :
    Eval (clear a) s (update s a []) (2*(s a).length+1) := by
  generalize he : s a = l
  induction l generalizing s with
  | nil =>
    have hh : update s a [] = s := by ext k; by_cases hk : k=a <;> simp_all
    simpa [clear,he,hh] using (Eval.whileNil (p:=Program.drop a) he)
  | cons b l ih =>
    let s₁ := update s a l
    have h₁ : Eval (Program.drop a) s s₁ 1 := by simpa [s₁,he] using Eval.drop a s
    have h₂ := ih s₁ (by simp [s₁])
    have hh : update s₁ a [] = update s a [] := by simp [s₁]
    have h := Eval.whileCons (by simp [he]) h₁ h₂
    convert h using 1 <;> simp_all [clear,s₁,Nat.mul_add,Nat.add_assoc] ; omega

lemma transfer_cons {a b : K} (hab : a ≠ b) (s : Store K) (x : Bool) (l : List Bool)
    (hs : s a = x::l) : transfer a b s = update (update s a l) b (x::s b) := by
  simp [transfer,hs,Ne.symm hab]

lemma eval_reverse {a b : K} (hab : a ≠ b) (s : Store K) :
    Eval (reverse a b) s (update (update s a []) b ((s a).reverse ++ s b))
      (2*(s a).length+1) := by
  generalize he : s a = l
  induction l generalizing s with
  | nil =>
    have hh : update (update s a []) b (s b) = s := by
      ext k
      by_cases hka : k=a <;> by_cases hkb : k=b <;> simp_all
    simpa [reverse,he,hh] using (Eval.whileNil (p:=Program.transfer a b) he)
  | cons x l ih =>
    let s₁ := update (update s a l) b (x::s b)
    have ha : s₁ a = l := by simp [s₁,hab]
    have hb : s₁ b = x::s b := by simp [s₁]
    have h₁ : Eval (Program.transfer a b) s s₁ 1 := by
      simpa [transfer_cons hab s x l he,s₁] using Eval.transfer a b s
    have h₂ := ih s₁ ha
    have hh : update (update s₁ a []) b (l.reverse++s₁ b) =
        update (update s a []) b ((x::l).reverse++s b) := by
      ext k
      by_cases hka : k=a <;> by_cases hkb : k=b <;>
        simp_all [s₁,List.reverse_cons,List.append_assoc]
    have h := Eval.whileCons (by simp [he]) h₁ h₂
    convert h using 1 <;> simp_all [reverse,Nat.mul_add,Nat.add_assoc] ; omega

/-- Copy a nonempty head to another register without consuming it. -/
def copyHead (a b : K) : Program K := .branch a .skip (.push b false) (.push b true)

lemma eval_copyHead {a b : K} (s : Store K) (x : Bool) (l : List Bool) (hs : s a = x::l) :
    Eval (copyHead a b) s (update s b (x::s b)) 2 := by
  cases x with
  | false => exact Eval.branchFalse hs (Eval.push b false s)
  | true => exact Eval.branchTrue hs (Eval.push b true s)

/-- Two simultaneous reversed copies of a word, consuming the operand. -/
def duplicateReverse (a b c : K) : Program K :=
  .loop a (.seq (.transfer a b) (copyHead b c))

lemma eval_duplicateReverse {a b c : K} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : Store K) :
    Eval (duplicateReverse a b c) s
      (update (update (update s a []) b ((s a).reverse++s b)) c ((s a).reverse++s c))
      (5*(s a).length+1) := by
  generalize he : s a = l
  induction l generalizing s with
  | nil =>
    have hh : update (update (update s a []) b (s b)) c (s c) = s := by
      ext k
      by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hkc : k=c <;> simp_all
    simpa [duplicateReverse,he,hh] using
      (Eval.whileNil (p:=Program.seq (.transfer a b) (copyHead b c)) he)
  | cons x l ih =>
    let s₁ := update (update s a l) b (x::s b)
    let s₂ := update s₁ c (x::s c)
    have h₁ : Eval (Program.transfer a b) s s₁ 1 := by
      simpa [transfer_cons hab s x l he,s₁] using Eval.transfer a b s
    have h₂ : Eval (copyHead b c) s₁ s₂ 2 := by
      simpa [s₂,s₁,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc] using
        eval_copyHead (a:=b) (b:=c) s₁ x (s b) (by simp [s₁])
    have ha : s₂ a = l := by simp [s₂,s₁,hab,hac,]
    have ht := ih s₂ ha
    have hh : update (update (update s₂ a []) b (l.reverse++s₂ b)) c (l.reverse++s₂ c) =
        update (update (update s a []) b ((x::l).reverse++s b)) c ((x::l).reverse++s c) := by
      ext k
      by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hkc : k=c <;>
        simp_all [s₂,s₁,List.reverse_cons,List.append_assoc]
    have h := Eval.whileCons (by simp [he]) (Eval.seq h₁ h₂) ht
    convert h using 1 <;> simp_all [duplicateReverse,Nat.mul_add,Nat.add_assoc] ; omega

/-- Copy an arbitrary binary word, restoring the operand and clearing
temporary storage; all registers have fixed indices. -/
def copy (a b tmp : K) : Program K :=
  .seq (clear b) (.seq (clear tmp) (.seq (reverse a tmp) (duplicateReverse tmp a b)))

lemma eval_copy {a b tmp : K} (hab : a ≠ b) (hat : a ≠ tmp) (hbt : b ≠ tmp)
    (s : Store K) :
    Eval (copy a b tmp) s (update (update s b (s a)) tmp [])
      (7*(s a).length+2*(s b).length+2*(s tmp).length+7) := by
  let s₁ := update s b []
  let s₂ := update s₁ tmp []
  let s₃ := update (update s₂ a []) tmp ((s₂ a).reverse++s₂ tmp)
  have h₁ := eval_clear b s
  have h₂ := eval_clear tmp s₁
  have h₃ := eval_reverse hat s₂
  have h₄ := eval_duplicateReverse (Ne.symm hat) (Ne.symm hbt) hab s₃
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))
  have hh : update (update (update s₃ tmp []) a ((s₃ tmp).reverse++s₃ a)) b
        ((s₃ tmp).reverse++s₃ b) = update (update s b (s a)) tmp [] := by
    ext k
    by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hkt : k=tmp <;>
      simp_all [s₃,s₂,s₁]
  change Eval (copy a b tmp) s
    (update (update (update s₃ tmp []) a ((s₃ tmp).reverse++s₃ a)) b
        ((s₃ tmp).reverse++s₃ b)) _ at h
  rw [hh] at h
  convert h using 1
  simp [s₃,s₂,s₁,hab,hat,Ne.symm hbt]
  omega

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

/-- Little-endian binary words; zero has the empty word. -/
def wordValue : List Bool → ℕ
  | [] => 0
  | b::l => (if b then 1 else 0)+2*wordValue l

def incrementWord : List Bool → List Bool
  | [] => [true]
  | false::l => true::l
  | true::l => false::incrementWord l

@[simp] theorem incrementWord_value (l : List Bool) : wordValue (incrementWord l) = wordValue l+1 := by
  induction l with
  | nil => simp [incrementWord,wordValue]
  | cons b l ih => cases b <;> simp [incrementWord,wordValue,ih] <;> omega

def carrySplit : List Bool → ℕ × List Bool
  | [] => (0,[true])
  | false::l => (0,true::l)
  | true::l => let r := carrySplit l; (r.1+1,r.2)

theorem carrySplit_spec (l : List Bool) :
    incrementWord l = List.replicate (carrySplit l).1 false ++ (carrySplit l).2 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b with
    | false => rfl
    | true => simp [incrementWord,carrySplit,List.replicate_succ,ih]

theorem carrySplit_length (l : List Bool) : (carrySplit l).1 ≤ l.length := by
  induction l with
  | nil => simp [carrySplit]
  | cons b l ih => cases b <;> simp [carrySplit] ; omega

theorem incrementWord_length (l : List Bool) : (incrementWord l).length ≤ l.length+1 := by
  induction l with
  | nil => simp [incrementWord]
  | cons b l ih => cases b <;> simp [incrementWord] ; omega

def incrementBody (a tmp flag : K) : Program K := .branch a
  (.seq (.push a true) (clear flag))
  (.seq (.drop a) (.seq (.push a true) (clear flag)))
  (.seq (.drop a) (.push tmp false))

def incrementLoop (a tmp flag : K) : Program K := .loop flag (incrementBody a tmp flag)

lemma eval_incrementLoop {a tmp flag : K} (hat : a ≠ tmp) (haf : a ≠ flag) (htf : tmp ≠ flag)
    (s : Store K) (hf : s flag = [true]) :
    ∃ t ≤ 5*(s a).length+10, Eval (incrementLoop a tmp flag) s
      (update (update (update s a (carrySplit (s a)).2) tmp
        (List.replicate (carrySplit (s a)).1 false ++ s tmp)) flag []) t := by
  generalize he : s a = l
  induction l generalizing s with
  | nil =>
    let s₁ := update s a [true]
    have hf₁ : s₁ flag = [true] := by simp [s₁,Ne.symm haf,hf]
    have hclear : Eval (clear flag) s₁ (update s₁ flag []) 3 := by
      simpa [hf₁] using eval_clear flag s₁
    have hpush : Eval (Program.push a true) s s₁ 1 := by
      simpa [s₁,he] using Eval.push a true s
    have hb : Eval (incrementBody a tmp flag) s (update s₁ flag []) 6 :=
      Eval.branchNone he (Eval.seq hpush hclear)
    have halt : Eval (incrementLoop a tmp flag) (update s₁ flag []) (update s₁ flag []) 1 :=
      Eval.whileNil (by simp)
    have h := Eval.whileCons (by simp [hf]) hb halt
    have hh : update (update (update s a [true]) tmp (s tmp)) flag [] = update s₁ flag [] := by
      ext k
      by_cases hka : k=a <;> by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;> simp_all [s₁]
    refine ⟨8,by simp,?_⟩
    simpa [incrementLoop,he,carrySplit,hh] using h
  | cons b l ih =>
    cases b with
    | false =>
      let s₁ := update s a l
      let s₂ := update s₁ a (true::l)
      have hf₂ : s₂ flag = [true] := by simp [s₂,s₁,Ne.symm haf,hf]
      have hclear : Eval (clear flag) s₂ (update s₂ flag []) 3 := by
        simpa [hf₂] using eval_clear flag s₂
      have hdrop : Eval (Program.drop a) s s₁ 1 := by simpa [s₁,he] using Eval.drop a s
      have hpush : Eval (Program.push a true) s₁ s₂ 1 := by simpa [s₂,s₁] using Eval.push a true s₁
      have hb : Eval (incrementBody a tmp flag) s (update s₂ flag []) 8 :=
        Eval.branchFalse he (Eval.seq hdrop (Eval.seq hpush hclear))
      have halt : Eval (incrementLoop a tmp flag) (update s₂ flag []) (update s₂ flag []) 1 :=
        Eval.whileNil (by simp)
      have h := Eval.whileCons (by simp [hf]) hb halt
      have hh : update (update (update s a (true::l)) tmp (s tmp)) flag [] = update s₂ flag [] := by
        ext k
        by_cases hka : k=a <;> by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;> simp_all [s₂,s₁]
      refine ⟨10,by simp,?_⟩
      simpa [incrementLoop,he,carrySplit,hh] using h
    | true =>
      let s₁ := update s a l
      let s₂ := update s₁ tmp (false::s tmp)
      have ha₂ : s₂ a = l := by simp [s₂,s₁,hat]
      have hf₂ : s₂ flag = [true] := by simp [s₂,s₁,Ne.symm haf,Ne.symm htf,hf]
      have hdrop : Eval (Program.drop a) s s₁ 1 := by simpa [s₁,he] using Eval.drop a s
      have hpush : Eval (Program.push tmp false) s₁ s₂ 1 := by simpa [s₂,s₁,Ne.symm hat] using Eval.push tmp false s₁
      have hb : Eval (incrementBody a tmp flag) s s₂ 4 :=
        Eval.branchTrue he (Eval.seq hdrop hpush)
      obtain ⟨t,ht,hev⟩ := ih s₂ hf₂ ha₂
      have h := Eval.whileCons (by simp [hf]) hb hev
      have hh :
        update (update (update s₂ a (carrySplit l).2) tmp
          (List.replicate (carrySplit l).1 false++s₂ tmp)) flag [] =
        update (update (update s a (carrySplit l).2) tmp
          (List.replicate ((carrySplit l).1+1) false++s tmp)) flag [] := by
        ext k
        by_cases hka : k=a <;> by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;>
          simp_all [s₂,s₁,List.replicate_add,List.append_assoc]
      refine ⟨5+t,by simp only [List.length_cons] at *; omega,?_⟩
      simpa only [incrementLoop,ha₂,carrySplit,hh] using h

def increment (a tmp flag : K) : Program K :=
  .seq (clear tmp) (.seq (clear flag) (.seq (.push flag true)
    (.seq (incrementLoop a tmp flag) (reverse tmp a))))

lemma eval_increment {a tmp flag : K} (hat : a ≠ tmp) (haf : a ≠ flag) (htf : tmp ≠ flag)
    (s : Store K) :
    ∃ t ≤ 7*(s a).length+2*(s tmp).length+2*(s flag).length+18,
      Eval (increment a tmp flag) s
        (update (update (update s a (incrementWord (s a))) tmp []) flag []) t := by
  let s₁ := update s tmp []
  let s₂ := update s₁ flag []
  let s₃ := update s₂ flag [true]
  have ha₃ : s₃ a = s a := by simp [s₃,s₂,s₁,hat,haf]
  have ht₃ : s₃ tmp = [] := by simp [s₃,s₂,s₁,htf]
  obtain ⟨t,ht,hloop⟩ := eval_incrementLoop hat haf htf s₃ (by simp [s₃])
  let s₄ := update (update (update s₃ a (carrySplit (s a)).2) tmp
        (List.replicate (carrySplit (s a)).1 false)) flag []
  change Eval (incrementLoop a tmp flag) s₃ _ t at hloop
  have hloop' : Eval (incrementLoop a tmp flag) s₃ s₄ t := by
    simpa [ha₃,ht₃,s₄] using hloop
  have h₁ := eval_clear tmp s
  have h₂ := eval_clear flag s₁
  have hp : Eval (Program.push flag true) s₂ s₃ 1 := by simpa [s₂,s₃] using Eval.push flag true s₂
  have hrev := eval_reverse (Ne.symm hat) s₄
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq hp (Eval.seq hloop' hrev)))
  have hfinal : update (update s₄ tmp []) a ((s₄ tmp).reverse++s₄ a) =
      update (update (update s a (incrementWord (s a))) tmp []) flag [] := by
    ext k
    by_cases hka : k=a <;> by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;>
      simp_all [s₄,s₃,s₂,s₁,carrySplit_spec]
  rw [hfinal] at h
  refine ⟨_,?_,h⟩
  have hc := carrySplit_length (s a)
  simp only [ha₃] at ht
  simp [s₄,s₃,s₂,s₁,htf,Ne.symm htf]
  omega

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

lemma wordValue_head_tail (l : List Bool) :
    wordValue l = (if l.headD false then 1 else 0)+2*wordValue l.tail := by
  cases l with
  | nil => rfl
  | cons b l => rfl

/-- Grade-school addition, scanning the second operand one bit at a time.
The first operand is shifted after adding the incoming low bit. -/
def addWord : List Bool → List Bool → List Bool
  | a, [] => a
  | a, false::b => a.headD false :: addWord a.tail b
  | a, true::b => (incrementWord a).headD false :: addWord (incrementWord a).tail b

@[simp] theorem addWord_value (a b : List Bool) :
    wordValue (addWord a b) = wordValue a + wordValue b := by
  induction b generalizing a with
  | nil => simp [addWord,wordValue]
  | cons x b ih =>
    cases x with
    | false =>
      simp only [addWord,wordValue,Bool.false_eq_true,↓reduceIte,zero_add,ih]
      rw [wordValue_head_tail a]
      omega
    | true =>
      simp only [addWord,wordValue,↓reduceIte,ih]
      have hh := wordValue_head_tail (incrementWord a)
      rw [incrementWord_value] at hh
      omega

lemma incrementWord_tail_length (a : List Bool) : (incrementWord a).tail.length ≤ a.length := by
  have hh := incrementWord_length a
  rw [List.length_tail]
  omega

lemma addWord_length (a b : List Bool) : (addWord a b).length ≤ a.length+b.length := by
  induction b generalizing a with
  | nil => simp [addWord]
  | cons x b ih =>
    cases x with
    | false =>
      have hh := ih a.tail
      simp only [addWord,List.length_cons]
      have ht : a.tail.length ≤ a.length := by simp
      omega
    | true =>
      have hh := ih (incrementWord a).tail
      have ht := incrementWord_tail_length a
      simp only [addWord,List.length_cons]
      omega

/-- Emits one least-significant bit, supplying zero for an exhausted operand. -/
def emitLow (a out : K) : Program K :=
  .branch a (.push out false) (.transfer a out) (.transfer a out)

lemma eval_emitLow {a out : K} (hao : a ≠ out) (s : Store K) :
    Eval (emitLow a out) s
      (update (update s a (s a).tail) out ((s a).headD false::s out)) 2 := by
  cases he : s a with
  | nil =>
    have hh : update (update s a (s a).tail) out ((s a).headD false::s out) =
        update s out (false::s out) := by
      ext k; by_cases hka : k=a <;> by_cases hko : k=out <;> simp_all
    simp only [he] at hh
    rw [hh]
    exact Eval.branchNone he (Eval.push out false s)
  | cons x xs =>
    have ht := Eval.transfer a out s
    simp only [transfer,he,Function.update_of_ne (Ne.symm hao)] at ht
    cases x with
    | false => simpa [emitLow,he] using Eval.branchFalse he ht
    | true => simpa [emitLow,he] using Eval.branchTrue he ht

/-- Output invariant for the single pass: a reversed low part is on `out`. -/
def addSplit : List Bool → List Bool → List Bool × List Bool
  | a, [] => ([],a)
  | a, false::b =>
    let r := addSplit a.tail b
    (a.headD false::r.1,r.2)
  | a, true::b =>
    let r := addSplit (incrementWord a).tail b
    ((incrementWord a).headD false::r.1,r.2)

lemma addSplit_spec (a b : List Bool) : (addSplit a b).1++(addSplit a b).2 = addWord a b := by
  induction b generalizing a with
  | nil => rfl
  | cons x b ih => cases x <;> simp [addSplit,addWord,ih]

lemma addSplit_first_length (a b : List Bool) : (addSplit a b).1.length = b.length := by
  induction b generalizing a with
  | nil => rfl
  | cons x b ih => cases x <;> simp [addSplit,ih]

def addBody (a b out tmp flag : K) : Program K :=
  .branch b .skip (.seq (.drop b) (emitLow a out))
    (.seq (.drop b) (.seq (increment a tmp flag) (emitLow a out)))

def addLoop (a b out tmp flag : K) : Program K := .loop b (addBody a b out tmp flag)

lemma eval_addLoop {a b out tmp flag : K}
    (hab : a ≠ b) (hao : a ≠ out) (hat : a ≠ tmp) (haf : a ≠ flag)
    (hbo : b ≠ out) (hbt : b ≠ tmp) (hbf : b ≠ flag)
    (hot : out ≠ tmp) (hof : out ≠ flag) (htf : tmp ≠ flag)
    (s : Store K) (ht : s tmp = []) (hf : s flag = []) :
    ∃ t ≤ (s b).length*(7*(s a).length+25)+1,
      Eval (addLoop a b out tmp flag) s
        (update (update (update s a (addSplit (s a) (s b)).2) b []) out
          ((addSplit (s a) (s b)).1.reverse++s out)) t := by
  generalize he : s b = l
  induction l generalizing s with
  | nil =>
    have hh : update (update (update s a (s a)) b []) out (s out) = s := by
      ext k; by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hko : k=out <;> simp_all
    refine ⟨1,by simp,?_⟩
    change Eval (addLoop a b out tmp flag) s
      (update (update (update s a (s a)) b []) out (s out)) 1
    rw [hh]
    exact Eval.whileNil he
  | cons x l ih =>
    let s₁ := update s b l
    have hdrop : Eval (Program.drop b) s s₁ 1 := by simpa [s₁,he] using Eval.drop b s
    cases x with
    | false =>
      let s₂ := update (update s₁ a (s a).tail) out ((s a).headD false::s out)
      have hh : Eval (emitLow a out) s₁ s₂ 2 := by
        simpa [s₂,s₁,hab,Ne.symm hbo] using eval_emitLow hao s₁
      have hb : Eval (addBody a b out tmp flag) s s₂ 5 :=
        Eval.branchFalse he (Eval.seq hdrop hh)
      have hta : s₂ a = (s a).tail := by simp [s₂,hao]
      have htb : s₂ b = l := by simp [s₂,s₁,hbo,Ne.symm hab]
      have htt : s₂ tmp = [] := by simp [s₂,s₁,Ne.symm hot,Ne.symm hat,Ne.symm hbt,ht]
      have htf' : s₂ flag = [] := by simp [s₂,s₁,Ne.symm hof,Ne.symm haf,Ne.symm hbf,hf]
      obtain ⟨t,htime,hloop⟩ := ih s₂ htt htf' htb
      have h := Eval.whileCons (by simp [he]) hb hloop
      have hfinal :
        update (update (update s₂ a (addSplit (s₂ a) (s₂ b)).2) b []) out
          ((addSplit (s₂ a) (s₂ b)).1.reverse++s₂ out) =
        update (update (update s a (addSplit (s a) (false::l)).2) b []) out
          ((addSplit (s a) (false::l)).1.reverse++s out) := by
        ext k
        by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hko : k=out <;>
          simp_all [s₂,s₁,addSplit,List.append_assoc]
      simp only [htb] at hfinal
      rw [hfinal] at h
      refine ⟨6+t,?_,by simpa [addLoop,he] using h⟩
      simp only [hta] at htime
      have hlen : (s a).tail.length ≤ (s a).length := by simp
      have hmul := Nat.mul_le_mul_left l.length (Nat.add_le_add_right (Nat.mul_le_mul_left 7 hlen) 25)
      simp only [List.length_cons]
      linarith
    | true =>
      obtain ⟨u,hu,hinc⟩ := eval_increment hat haf htf s₁
      let s₂ := update (update (update s₁ a (incrementWord (s a))) tmp []) flag []
      have hii : Eval (increment a tmp flag) s₁ s₂ u := by simpa [s₂,s₁,hab] using hinc
      let s₃ := update (update s₂ a (incrementWord (s a)).tail) out
        ((incrementWord (s a)).headD false::s out)
      have hh : Eval (emitLow a out) s₂ s₃ 2 := by
        simpa [s₃,s₂,s₁,hat,haf,Ne.symm hao,Ne.symm hbo,hot,hof] using eval_emitLow hao s₂
      have hb : Eval (addBody a b out tmp flag) s s₃ (6+u) := by
        simpa [addBody,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          (Eval.branchTrue he (Eval.seq hdrop (Eval.seq hii hh)))
      have hta : s₃ a = (incrementWord (s a)).tail := by simp [s₃,hao]
      have htb : s₃ b = l := by simp [s₃,s₂,s₁,hbo,hbt,hbf,Ne.symm hab]
      have htt : s₃ tmp = [] := by simp [s₃,s₂,Ne.symm hot,Ne.symm hat,htf]
      have htf' : s₃ flag = [] := by simp [s₃,s₂,Ne.symm hof,Ne.symm haf]
      obtain ⟨t,htime,hloop⟩ := ih s₃ htt htf' htb
      have h := Eval.whileCons (by simp [he]) hb hloop
      have hfinal :
        update (update (update s₃ a (addSplit (s₃ a) (s₃ b)).2) b []) out
          ((addSplit (s₃ a) (s₃ b)).1.reverse++s₃ out) =
        update (update (update s a (addSplit (s a) (true::l)).2) b []) out
          ((addSplit (s a) (true::l)).1.reverse++s out) := by
        ext k
        by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hko : k=out <;>
        by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;>
          simp_all [s₃,s₂,s₁,addSplit,List.append_assoc]
      simp only [htb] at hfinal
      rw [hfinal] at h
      refine ⟨7+u+t,?_,by simpa [addLoop,he,←Nat.add_assoc] using h⟩
      simp only [hta] at htime
      have hlen := incrementWord_tail_length (s a)
      have hmul := Nat.mul_le_mul_left l.length (Nat.add_le_add_right (Nat.mul_le_mul_left 7 hlen) 25)
      simp [s₁,hab,Ne.symm hbt,Ne.symm hbf,ht,hf] at hu
      simp only [List.length_cons]
      linarith

/-- Destructive binary addition. The second operand and all scratch words are
cleared; the first register holds the exact sum. -/
def add (a b out tmp flag : K) : Program K :=
  .seq (clear out) (.seq (clear tmp) (.seq (clear flag)
    (.seq (addLoop a b out tmp flag) (reverse out a))))

lemma eval_add {a b out tmp flag : K}
    (hab : a ≠ b) (hao : a ≠ out) (hat : a ≠ tmp) (haf : a ≠ flag)
    (hbo : b ≠ out) (hbt : b ≠ tmp) (hbf : b ≠ flag)
    (hot : out ≠ tmp) (hof : out ≠ flag) (htf : tmp ≠ flag)
    (s : Store K) :
    ∃ t ≤ (s b).length*(7*(s a).length+27)+
        2*(s out).length+2*(s tmp).length+2*(s flag).length+9,
      Eval (add a b out tmp flag) s
        (update (update (update (update (update s a (addWord (s a) (s b))) b []) out []) tmp []) flag []) t := by
  let s₁ := update s out []
  let s₂ := update s₁ tmp []
  let s₃ := update s₂ flag []
  have ha₃ : s₃ a = s a := by simp [s₃,s₂,s₁,hao,hat,haf]
  have hb₃ : s₃ b = s b := by simp [s₃,s₂,s₁,hbo,hbt,hbf]
  have ho₃ : s₃ out = [] := by simp [s₃,s₂,s₁,hot,hof]
  obtain ⟨t,ht,hloop⟩ := eval_addLoop hab hao hat haf hbo hbt hbf hot hof htf s₃
    (by simp [s₃,s₂,htf]) (by simp [s₃])
  let s₄ := update (update (update s₃ a (addSplit (s a) (s b)).2) b []) out
      (addSplit (s a) (s b)).1.reverse
  have hlo : Eval (addLoop a b out tmp flag) s₃ s₄ t := by
    simpa [s₄,ha₃,hb₃,ho₃] using hloop
  have hrev := eval_reverse (Ne.symm hao) s₄
  have h := Eval.seq (eval_clear out s) (Eval.seq (eval_clear tmp s₁)
    (Eval.seq (eval_clear flag s₂) (Eval.seq hlo hrev)))
  have hfinal : update (update s₄ out []) a ((s₄ out).reverse++s₄ a) =
      update (update (update (update (update s a (addWord (s a) (s b))) b []) out []) tmp []) flag [] := by
    ext k
    by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hko : k=out <;>
    by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;>
      simp_all [s₄,s₃,s₂,s₁,addSplit_spec]
  rw [hfinal] at h
  refine ⟨_,?_,h⟩
  rw [ha₃,hb₃] at ht
  simp [s₄,s₃,s₂,s₁,Ne.symm hot,Ne.symm hof,Ne.symm htf,addSplit_first_length]
  linarith

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryMultiply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

lemma wordValue_append (a b : List Bool) :
    wordValue (a++b) = wordValue a + 2^a.length * wordValue b := by
  induction a with
  | nil => simp [wordValue]
  | cons x a ih => simp [wordValue,ih,pow_succ]; ring

/-- Removes the high zero bits of a most-significant-first word. -/
def trimMSD : List Bool → List Bool
  | [] => []
  | false::l => trimMSD l
  | true::l => true::l

lemma trimMSD_length (l : List Bool) : (trimMSD l).length ≤ l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [trimMSD] ; omega

lemma trimMSD_reverse_value (l : List Bool) :
    wordValue (trimMSD l).reverse = wordValue l.reverse := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [trimMSD,List.reverse_cons,wordValue_append,wordValue,ih]

def Canonical (l : List Bool) : Prop := l = [] ∨ ∃ w, l = w++[true]

lemma canonical_tail {b : Bool} {l : List Bool} (h : Canonical (b::l)) : Canonical l := by
  obtain h | ⟨w,hw⟩ := h
  · contradiction
  · cases w with
    | nil => simp only [List.nil_append,List.cons.injEq] at hw; exact Or.inl hw.2
    | cons x w =>
      simp only [List.cons_append,List.cons.injEq] at hw
      exact Or.inr ⟨w,hw.2⟩

lemma canonical_single {b : Bool} (h : Canonical [b]) : b = true := by
  obtain h | ⟨w,hw⟩ := h
  · contradiction
  · cases w with
    | nil => simpa using hw
    | cons a w =>
      have hl := congrArg List.length hw
      simp only [List.length_cons,List.length_append] at hl
      omega

lemma bits_wordValue (l : List Bool) (h : Canonical l) : (wordValue l).bits = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have htail := ih (canonical_tail h)
    have hz : wordValue l = 0 → b = true := by
      intro hh
      have hl : l = [] := by simpa [hh] using htail.symm
      subst l
      exact canonical_single h
    have he : wordValue (b::l) = Nat.bit b (wordValue l) := by
      cases b <;> simp [wordValue,Nat.bit] ; omega
    rw [he,Nat.bits_append_bit _ _ hz,htail]

lemma canonical_trim_reverse (l : List Bool) : Canonical (trimMSD l).reverse := by
  induction l with
  | nil => exact Or.inl rfl
  | cons b l ih =>
    cases b with
    | false => exact ih
    | true => exact Or.inr ⟨l.reverse,by simp [trimMSD]⟩

def normalizeWord (l : List Bool) : List Bool := (trimMSD l.reverse).reverse

@[simp] theorem normalizeWord_value (l : List Bool) : wordValue (normalizeWord l) = wordValue l := by
  simpa [normalizeWord] using trimMSD_reverse_value l.reverse

@[simp] theorem normalizeWord_eq_bits (l : List Bool) : normalizeWord l = (wordValue l).bits := by
  rw [← normalizeWord_value l]
  exact (bits_wordValue _ (canonical_trim_reverse l.reverse)).symm

def trimBody (a flag : K) : Program K := .branch a (clear flag) (.drop a) (clear flag)
def trimLoop (a flag : K) : Program K := .loop flag (trimBody a flag)

lemma eval_trimLoop {a flag : K} (haf : a ≠ flag) (s : Store K) (hf : s flag = [true]) :
    ∃ t ≤ 3*(s a).length+6,
      Eval (trimLoop a flag) s (update (update s a (trimMSD (s a))) flag []) t := by
  generalize he : s a = l
  induction l generalizing s with
  | nil =>
    have hh : update (update s a []) flag [] = update s flag [] := by
      ext k; by_cases hka : k=a <;> by_cases hkf : k=flag <;> simp_all
    have hc : Eval (clear flag) s (update s flag []) 3 := by simpa [hf] using eval_clear flag s
    have hb : Eval (trimBody a flag) s (update s flag []) 4 := Eval.branchNone he hc
    have halt : Eval (trimLoop a flag) (update s flag []) (update s flag []) 1 := Eval.whileNil (by simp)
    refine ⟨6,by simp,?_⟩
    simpa [trimLoop,he,trimMSD,hh] using Eval.whileCons (by simp [hf]) hb halt
  | cons b l ih =>
    cases b with
    | false =>
      let s₁ := update s a l
      have hh : s₁ flag = [true] := by simp [s₁,Ne.symm haf,hf]
      obtain ⟨t,ht,hloop⟩ := ih s₁ hh (by simp [s₁])
      have hd : Eval (Program.drop a) s s₁ 1 := by simpa [s₁,he] using Eval.drop a s
      have hb : Eval (trimBody a flag) s s₁ 2 := Eval.branchFalse he hd
      have h := Eval.whileCons (by simp [hf]) hb hloop
      refine ⟨3+t,by simp only [List.length_cons]; omega,?_⟩
      simpa [trimLoop,trimMSD,s₁] using h
    | true =>
      have hh : update (update s a (true::l)) flag [] = update s flag [] := by
        ext k; by_cases hka : k=a <;> by_cases hkf : k=flag <;> simp_all
      have hc : Eval (clear flag) s (update s flag []) 3 := by simpa [hf] using eval_clear flag s
      have hb : Eval (trimBody a flag) s (update s flag []) 4 := Eval.branchTrue he hc
      have halt : Eval (trimLoop a flag) (update s flag []) (update s flag []) 1 := Eval.whileNil (by simp)
      refine ⟨6,by simp,?_⟩
      simpa [trimLoop,trimMSD,hh] using Eval.whileCons (by simp [hf]) hb halt

def normalize (a tmp flag : K) : Program K :=
  .seq (clear tmp) (.seq (clear flag) (.seq (.push flag true)
    (.seq (reverse a tmp) (.seq (trimLoop tmp flag) (reverse tmp a)))))

lemma eval_normalize {a tmp flag : K} (hat : a ≠ tmp) (haf : a ≠ flag) (htf : tmp ≠ flag)
    (s : Store K) :
    ∃ t ≤ 7*(s a).length+2*(s tmp).length+2*(s flag).length+16,
      Eval (normalize a tmp flag) s
        (update (update (update s a (normalizeWord (s a))) tmp []) flag []) t := by
  let s₁ := update s tmp []
  let s₂ := update s₁ flag []
  let s₃ := update s₂ flag [true]
  let s₄ := update (update s₃ a []) tmp (s a).reverse
  have hr : Eval (reverse a tmp) s₃ s₄ (2*(s a).length+1) := by
    simpa [s₄,s₃,s₂,s₁,hat,haf,htf] using eval_reverse hat s₃
  obtain ⟨t,ht,htrim⟩ := eval_trimLoop htf s₄ (by simp [s₄,s₃,Ne.symm htf,Ne.symm haf])
  let s₅ := update (update s₄ tmp (trimMSD (s a).reverse)) flag []
  have htr : Eval (trimLoop tmp flag) s₄ s₅ t := by simpa [s₅,s₄] using htrim
  have hp : Eval (Program.push flag true) s₂ s₃ 1 := by simpa [s₃,s₂] using Eval.push flag true s₂
  have h := Eval.seq (eval_clear tmp s) (Eval.seq (eval_clear flag s₁)
    (Eval.seq hp (Eval.seq hr (Eval.seq htr (eval_reverse (Ne.symm hat) s₅)))))
  have heq : update (update s₅ tmp []) a ((s₅ tmp).reverse++s₅ a) =
      update (update (update s a (normalizeWord (s a))) tmp []) flag [] := by
    ext k
    by_cases hka : k=a <;> by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;>
      simp_all [s₅,s₄,s₃,s₂,s₁,normalizeWord]
  rw [heq] at h
  refine ⟨_,?_,h⟩
  have hl := trimMSD_length (s a).reverse
  simp [s₄] at ht
  simp [s₅,s₄,s₃,s₂,s₁,htf,Ne.symm htf]
  simp only [List.length_reverse] at hl
  omega

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinarySubtract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

/-- Shift-and-add on explicit little-endian words. -/
def mulAccWord : List Bool → List Bool → List Bool → List Bool
  | _a, [], c => c
  | a, false::b, c => mulAccWord (false::a) b c
  | a, true::b, c => mulAccWord (false::a) b (addWord c a)

@[simp] theorem mulAccWord_value (a b c : List Bool) :
    wordValue (mulAccWord a b c) = wordValue c + wordValue a*wordValue b := by
  induction b generalizing a c with
  | nil => simp [mulAccWord,wordValue]
  | cons x b ih => cases x <;> simp [mulAccWord,wordValue,ih,addWord_value] <;> ring

lemma mulAccWord_length (a b c : List Bool) :
    (mulAccWord a b c).length ≤ c.length+b.length*(a.length+b.length) := by
  induction b generalizing a c with
  | nil => simp [mulAccWord]
  | cons x b ih =>
    cases x with
    | false =>
      have h := ih (false::a) c
      simp only [mulAccWord,List.length_cons] at *
      linarith
    | true =>
      have h := ih (false::a) (addWord c a)
      have hh := addWord_length c a
      simp only [mulAccWord,List.length_cons] at *
      linarith

/-- Registers: 0 multiplicand, 1 multiplier, 2 accumulator,
3 copied addend, 4/5/6 addition scratch, 7 copy scratch. -/
def mulBody : Program (Fin 8) := .branch 1 .skip
  (.seq (.drop 1) (.push 0 false))
  (.seq (.drop 1) (.seq (copy 0 3 7) (.seq (add 2 3 4 5 6) (.push 0 false))))

def mulLoop : Program (Fin 8) := .loop 1 mulBody

lemma eval_mulLoop (s : Store (Fin 8))
    (hf : ∀ k : Fin 8, 3 ≤ k.val → s k = []) (A C : ℕ)
    (hA : (s 0).length+(s 1).length ≤ A)
    (hC : (s 2).length+(s 1).length*((s 0).length+(s 1).length) ≤ C) :
    ∃ t ≤ (s 1).length*(A*(7*C+34)+23)+1,
      Eval mulLoop s
        (update (update (update s 0 (List.replicate (s 1).length false++s 0)) 1 [])
          2 (mulAccWord (s 0) (s 1) (s 2))) t := by
  generalize he : s 1 = l at *
  induction l generalizing s with
  | nil =>
    have hh : update (update (update s 0 (s 0)) 1 []) 2 (s 2) = s := by
      ext k; fin_cases k <;> simp_all
    refine ⟨1,by simp,?_⟩
    change Eval mulLoop s (update (update (update s 0 (s 0)) 1 []) 2 (s 2)) 1
    rw [hh]
    exact Eval.whileNil he
  | cons x l ih =>
    let s₁ := update s 1 l
    have hd : Eval (Program.drop 1) s s₁ 1 := by simpa [s₁,he] using Eval.drop (1 : Fin 8) s
    cases x with
    | false =>
      let s₂ := update s₁ 0 (false::s 0)
      have hp : Eval (Program.push 0 false) s₁ s₂ 1 := by simpa [s₂,s₁] using Eval.push (0 : Fin 8) false s₁
      have hb : Eval mulBody s s₂ 4 := Eval.branchFalse he (Eval.seq hd hp)
      have hf₂ : ∀ k : Fin 8, 3 ≤ k.val → s₂ k = [] := by
        intro k hk; fin_cases k <;> simp_all [s₂,s₁]
      have hA₂ : (s₂ 0).length+(s₂ 1).length ≤ A := by simp [s₂,s₁]; simp only [List.length_cons] at hA; omega
      have hC₂ : (s₂ 2).length+(s₂ 1).length*((s₂ 0).length+(s₂ 1).length) ≤ C := by
        simp [s₂,s₁]; simp only [List.length_cons] at hC
        linarith
      obtain ⟨t,ht,hloop⟩ := ih s₂ hf₂ (by simp [s₂,s₁]) (by simpa [s₂,s₁] using hA₂) (by simpa [s₂,s₁] using hC₂)
      have h := Eval.whileCons (by simp [he]) hb hloop
      have heq :
        update (update (update s₂ 0 (List.replicate l.length false++s₂ 0)) 1 [])
          2 (mulAccWord (s₂ 0) l (s₂ 2)) =
        update (update (update s 0 (List.replicate (l.length+1) false++s 0)) 1 [])
          2 (mulAccWord (s 0) (false::l) (s 2)) := by
        ext k; fin_cases k <;> simp [s₂,s₁,mulAccWord,List.replicate_add,List.append_assoc]
      rw [heq] at h
      refine ⟨5+t,?_,by simpa [mulLoop] using h⟩
      simp only [List.length_cons]
      nlinarith
    | true =>
      have hc := eval_copy (a := (0 : Fin 8)) (b := 3) (tmp := 7) (by decide) (by decide) (by decide) s₁
      let s₂ := update (update s₁ 3 (s 0)) 7 []
      have hc' : Eval (copy 0 3 7) s₁ s₂ (7*(s 0).length+7) := by
        have h3 := hf 3 (by decide); have h7 := hf 7 (by decide)
        simpa [s₂,s₁,h3,h7] using hc
      obtain ⟨u,hu,ha⟩ := eval_add (a := (2 : Fin 8)) (b := 3) (out := 4) (tmp := 5) (flag := 6)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) s₂
      let s₃ := update (update (update (update (update s₂ 2 (addWord (s 2) (s 0))) 3 []) 4 []) 5 []) 6 []
      have ha' : Eval (add 2 3 4 5 6) s₂ s₃ u := by simpa [s₃,s₂,s₁] using ha
      let s₄ := update s₃ 0 (false::s 0)
      have hp : Eval (Program.push 0 false) s₃ s₄ 1 := by
        simpa [s₄,s₃,s₂,s₁] using Eval.push (0 : Fin 8) false s₃
      have hb : Eval mulBody s s₄ (6+(7*(s 0).length+7)+u) := by
        convert (Eval.branchTrue (p := Program.skip)
          (q := Program.seq (.drop 1) (.push 0 false)) he
          (Eval.seq hd (Eval.seq hc' (Eval.seq ha' hp)))) using 1 <;> first | rfl | omega
      have hf₄ : ∀ k : Fin 8, 3 ≤ k.val → s₄ k = [] := by
        intro k hk; fin_cases k <;> simp_all [s₄,s₃,s₂,s₁]
      have hA₄ : (s₄ 0).length+(s₄ 1).length ≤ A := by simp [s₄,s₃,s₂,s₁]; simp only [List.length_cons] at hA; omega
      have hC₄ : (s₄ 2).length+(s₄ 1).length*((s₄ 0).length+(s₄ 1).length) ≤ C := by
        have hh := addWord_length (s 2) (s 0)
        simp [s₄,s₃,s₂,s₁]; simp only [List.length_cons] at hC
        linarith
      obtain ⟨t,ht,hloop⟩ := ih s₄ hf₄ (by simp [s₄,s₃,s₂,s₁]) (by simpa [s₄,s₃,s₂,s₁] using hA₄) (by simpa [s₄,s₃,s₂,s₁] using hC₄)
      have h := Eval.whileCons (by simp [he]) hb hloop
      have heq :
        update (update (update s₄ 0 (List.replicate l.length false++s₄ 0)) 1 [])
          2 (mulAccWord (s₄ 0) l (s₄ 2)) =
        update (update (update s 0 (List.replicate (l.length+1) false++s 0)) 1 [])
          2 (mulAccWord (s 0) (true::l) (s 2)) := by
        have h3 := hf 3 (by decide); have h4 := hf 4 (by decide)
        have h5 := hf 5 (by decide); have h6 := hf 6 (by decide); have h7 := hf 7 (by decide)
        ext k; fin_cases k <;> simp [s₄,s₃,s₂,s₁,mulAccWord,List.replicate_add,List.append_assoc,h3,h4,h5,h6,h7]
      rw [heq] at h
      refine ⟨7+(7*(s 0).length+7)+u+t,?_,by simpa [mulLoop,←Nat.add_assoc] using h⟩
      have ha0 : (s 0).length ≤ A := by simp only [List.length_cons] at hA; omega
      have hc0 : (s 2).length ≤ C := by omega
      have h4 := hf 4 (by decide); have h5 := hf 5 (by decide); have h6 := hf 6 (by decide)
      simp [s₂,s₁,h4,h5,h6] at hu
      have hmul := Nat.mul_le_mul ha0 (Nat.add_le_add_right (Nat.mul_le_mul_left 7 hc0) 34)
      simp only [List.length_cons]
      linarith

/-- The normalized multiplication instruction; the accumulator starts at zero.
After execution register 2 is the canonical binary product. -/
def multiply : Program (Fin 8) := .seq mulLoop (normalize 2 5 6)

lemma eval_multiply (s : Store (Fin 8)) (hzero : s 2 = [])
    (hf : ∀ k : Fin 8, 3 ≤ k.val → s k = []) :
    let A := (s 0).length+(s 1).length
    let C := (s 1).length*A
    ∃ t ≤ (s 1).length*(A*(7*C+34)+23)+7*C+18,
      Eval multiply s
        (update (update (update s 0 (List.replicate (s 1).length false++s 0)) 1 [])
          2 (wordValue (s 0)*wordValue (s 1)).bits) t := by
  dsimp only
  obtain ⟨t,ht,hloop⟩ := eval_mulLoop s hf ((s 0).length+(s 1).length)
    ((s 1).length*((s 0).length+(s 1).length)) (le_refl _) (by simp [hzero])
  let v := update (update (update s 0 (List.replicate (s 1).length false++s 0)) 1 [])
    2 (mulAccWord (s 0) (s 1) (s 2))
  obtain ⟨u,hu,hnorm⟩ := eval_normalize (a := (2 : Fin 8)) (tmp := 5) (flag := 6)
    (by decide) (by decide) (by decide) v
  have h := Eval.seq hloop hnorm
  have h5 := hf 5 (by decide); have h6 := hf 6 (by decide)
  have heq : update (update (update v 2 (normalizeWord (v 2))) 5 []) 6 [] =
      update (update (update s 0 (List.replicate (s 1).length false++s 0)) 1 [])
        2 (wordValue (s 0)*wordValue (s 1)).bits := by
    ext k; fin_cases k <;> simp [v,normalizeWord_eq_bits,mulAccWord_value,hzero,wordValue,h5,h6]
  rw [heq] at h
  refine ⟨1+t+u,?_,h⟩
  have hl := mulAccWord_length (s 0) (s 1) (s 2)
  simp [v,h5,h6,hzero] at hu
  simp [hzero] at hl
  omega

lemma wordValue_lt (l : List Bool) : wordValue l < 2^l.length := by
  induction l with
  | nil => simp [wordValue]
  | cons b l ih => cases b <;> simp [wordValue,pow_succ] <;> omega

lemma product_bits_length (a b : List Bool) :
    (wordValue a * wordValue b).bits.length ≤ a.length+b.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le,pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (wordValue_lt a) (wordValue_lt b)

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

/-- Boolean full-subtractor gate. -/
def differenceBit (x y c : Bool) : Bool := (x ^^ y) ^^ c
def borrowBit (x y c : Bool) : Bool := ((!x) && (y || c)) || (y && c)
@[simp] lemma wordValue_nil : wordValue [] = 0 := rfl

variable {K : Type} [DecidableEq K]

def readBit (k : K) (f : Bool → Program K) : Program K := .branch k (f false) (f false) (f true)

/-- Registers 0,1 input, 2 reverse output, 3 singleton borrow, 4 loop flag. -/
def subtractDigit : Program (Fin 5) :=
  readBit 0 fun x => readBit 1 fun y => readBit 3 fun c =>
    .seq (.drop 0) (.seq (.drop 1) (.seq (.drop 3)
      (.seq (.push 3 (borrowBit x y c)) (.push 2 (differenceBit x y c)))))

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

def subtractBody : Program (Fin 5) :=
  .branch 0 (.branch 1 (clear 4) subtractDigit subtractDigit) subtractDigit subtractDigit

def subtractLoop : Program (Fin 5) := .loop 4 subtractBody

/-- Subtract and compare, destructively. Output register 2 has the little-endian
fixed-width modular difference; singleton register 3 is exactly the comparison
bit (true iff the first number was smaller). -/
def subtract : Program (Fin 5) :=
  .seq (clear 2) (.seq (clear 3) (.seq (clear 4) (.seq (.push 3 false)
    (.seq (.push 4 true) (.seq subtractLoop (reverse 2 0))))))

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function
variable {K L : Type} [DecidableEq K] [DecidableEq L]

def Program.rename (f : K → L) : Program K → Program L
  | .skip => .skip
  | .push k b => .push (f k) b
  | .drop k => .drop (f k)
  | .transfer a b => .transfer (f a) (f b)
  | .seq a b => .seq (a.rename f) (b.rename f)
  | .branch k a b c => .branch (f k) (a.rename f) (b.rename f) (c.rename f)
  | .loop k a => .loop (f k) (a.rename f)

lemma extend_update_store (f : K → L) (hf : Injective f) (s : Store K) (S : Store L)
    (k : K) (w : List Bool) :
    extend f (update s k w) S = update (extend f s S) (f k) w := by
  classical
  funext l
  by_cases h : ∃ a, f a = l
  · obtain ⟨a,rfl⟩ := h
    by_cases ha : a=k
    · subst a; simp [hf.extend_apply]
    · have hfa : f a ≠ f k := fun h => ha (hf h)
      simp [hf.extend_apply,ha,hfa]
  · have hfk : l ≠ f k := fun he => h ⟨k,he.symm⟩
    simp [extend_apply' _ _ _ h,hfk]

lemma extend_transfer_store (f : K → L) (hf : Injective f) (s : Store K) (S : Store L)
    (a b : K) :
    extend f (transfer a b s) S = transfer (f a) (f b) (extend f s S) := by
  classical
  simp only [transfer,hf.extend_apply]
  cases he : (s a).head? with
  | none => rfl
  | some x =>
    rw [extend_update_store f hf,extend_update_store f hf]
    congr 1
    rw [←extend_update_store f hf,hf.extend_apply]

lemma extend_pull_store {K L : Type} [DecidableEq K] [DecidableEq L]
  (f : K → L) (hf : Function.Injective f) (S : RationalHitting.StackLanguage.Store L) :
  Function.extend f (fun k => S (f k)) S = S := by
  classical
  funext l
  by_cases h : ∃ a, f a = l
  · obtain ⟨a,rfl⟩ := h; exact hf.extend_apply ..
  · exact extend_apply' _ _ _ h

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryGcd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

def subEmbed : Fin 5 ↪ Fin 10 := Fin.castAddEmb 5

def subtract10 : Program (Fin 10) := subtract.rename subEmbed

def reducePick : Program (Fin 10) :=
  .branch 3 .skip (.push 7 true) (.seq (copy 8 0 9) (.push 7 false))

def reduceOnce : Program (Fin 10) :=
  .seq (copy 0 8 9) (.seq (copy 5 1 9) (.seq subtract10 (.seq reducePick
    (.seq (normalize 0 2 4) (.seq (clear 3) (clear 8))))))

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

@[simp] lemma wordValue_bits (n : ℕ) : wordValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    cases b <;> simp [wordValue,ih,Nat.bit] ; omega

/-- Remainder 0, denominator 5, unread MSD numerator 6, quotient 7. -/
def divBody : Program (Fin 10) :=
  readBit 6 fun x => .seq (.drop 6) (.seq (.push 0 x) reduceOnce)
def divLoop : Program (Fin 10) := .loop 6 divBody

/-- Binary division starts with numerator in 0 and denominator in 5.
The original denominator is retained; quotient is placed in 7, remainder in 0.
Every other register is cleared. -/
def divide : Program (Fin 10) :=
  .seq (reverse 0 6) (.seq divLoop (normalize 7 2 4))

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryFactorial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

/-- Destructive exact binary quotient, retaining its positive denominator. -/
def quotient : Program (Fin 10) := .seq divide (.seq (copy 7 0 9) (clear 7))

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinaryBinomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

/-- Clean multiplication interface used by the finite rising-product loop. -/
def multiplyClean : Program (Fin 8) :=
  .seq multiply (.seq (clear 0) (.seq (copy 2 0 7) (clear 2)))

def factorMul : Fin 8 ↪ Fin 10 := ⟨fun k => ⟨k.val,by omega⟩,by intro i j h; exact Fin.ext (show i.val=j.val from congrArg (fun k : Fin 10 => k.val) h)⟩

def factorialScratch (s : Store (Fin 10)) : Prop :=
  ∀ k : Fin 10, 1≤k.val → k.val<8 → s k=[]

/-- One rising-product step: multiply accumulator by the copied current index,
advance the binary index, and drop one symbol of the unary loop counter. -/
def factorialBody : Program (Fin 10) :=
  .seq (copy 8 1 7) (.seq (multiplyClean.rename factorMul)
    (.seq (increment 8 5 6) (.drop 9)))

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

def factorialLoop : Program (Fin 10) := .loop 9 factorialBody

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

/-- Factorial with clean local registers: only the unary counter and output
register are changed. This is the binary subroutine for the Taylor binomials. -/
def factorialCore : Program (Fin 10) :=
  .seq (.push 0 true) (.seq (.push 8 true) (.seq factorialLoop (clear 8)))

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

def unaryDiffBody (a b flag : K) : Program K :=
  .branch a (.seq (.drop b) (.push flag true))
    (.seq (.drop a) (.drop b)) (.seq (.drop a) (.drop b))
def unaryDiff (a b flag : K) : Program K := .loop b (unaryDiffBody a b flag)

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage.Binomial
open Function

def arith : Fin 10 ↪ Fin 18 := ⟨fun k => ⟨k.val,by omega⟩,by
  intro i j h; exact Fin.ext (show i.val=j.val from congrArg (fun k : Fin 18 => k.val) h)⟩

def lowEmpty (s : Store (Fin 18)) : Prop := ∀ k : Fin 18, k.val<10 → s k=[]
def factorialCost (n : ℕ) : ℕ := n*(300*(1+n*(1+n)+1)^4+1)+2*n+10

def factorBlock (a b : Fin 18) : Program (Fin 18) :=
  .seq (copy a 9 17) (.seq (factorialCore.rename arith) (.seq (copy 0 b 17) (clear 0)))

def factorCost (n b : ℕ) : ℕ := factorialCost n+7*n+9*(1+n*(n+1))+2*b+20

end RationalHitting.StackLanguage.Binomial

namespace RationalHitting.StackLanguage.Binomial
open Function

def prepare : Program (Fin 18) :=
  .seq (copy 14 12 17) (.seq (copy 15 16 17) (unaryDiff 12 16 13))

end RationalHitting.StackLanguage.Binomial

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.BinomialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage.Binomial
open Function

def allFactors : Program (Fin 18) :=
  .seq (factorBlock 14 10) (.seq (factorBlock 15 11) (factorBlock 12 16))

def cleanMul : Program (Fin 18) := (multiplyClean.rename factorMul).rename arith

end RationalHitting.StackLanguage.Binomial

namespace RationalHitting.StackLanguage.Binomial
open Function

def ratio : Program (Fin 18) :=
  .seq (copy 11 0 17) (.seq (copy 16 1 17) (.seq cleanMul
    (.seq (copy 0 5 17) (.seq (copy 10 0 17) (.seq (quotient.rename arith)
      (.seq (clear 5) (.seq (clear 10) (.seq (clear 11) (.seq (clear 12) (clear 16))))))))))

def width (n k : ℕ) : ℕ := (1+n*(n+1))+(1+k*(k+1))+(1+(n-k)*((n-k)+1))
def ratioCost (n k : ℕ) : ℕ :=
  200*(width n k+1)^4+400*(width n k+1)^2+100*width n k+10*(n+k)+100

end RationalHitting.StackLanguage.Binomial

namespace RationalHitting.StackLanguage.Binomial
open Function

def compute : Program (Fin 18) := .seq allFactors ratio
def discard : Program (Fin 18) := .seq (clear 12) (clear 13)
def choose : Program (Fin 18) := .seq prepare (.branch 13 compute discard discard)
def cost (n k : ℕ) : ℕ := factorCost n 0+factorCost k 0+factorCost (n-k) 0+ratioCost n k+20*(n+k)+100

lemma factorCost_bound (j R : ℕ) (hR : 1≤R) (hj : j≤R) : factorCost j 0≤77000*R^10 := by
  have hj2 : j*(1+j)≤R*(1+R) := Nat.mul_le_mul hj (by omega)
  have hb : 1+j*(1+j)+1≤4*R^2 := by nlinarith
  have hb4 := Nat.pow_le_pow_left hb 4
  have hw := Nat.mul_le_mul hj (Nat.add_le_add_right (Nat.mul_le_mul_left 300 hb4) 1)
  have hm : j*(300*(1+j*(1+j)+1)^4+1)≤76800*R^9+R := by
    calc
      _ ≤ R*(300*((4*R^2)^4)+1) := hw
      _ = _ := by ring
  have hr : 9*j+9*(1+j*(j+1))+30≤100*R^2 := by nlinarith
  have hpow2 : R^2≤R^10 := Nat.pow_le_pow_right hR (by decide)
  have hpow9 : R^9≤R^10 := Nat.pow_le_pow_right hR (by decide)
  have hpow1 : R≤R^10 := by simpa using Nat.pow_le_pow_right hR (show 1≤10 by decide)
  unfold factorCost factorialCost
  linarith only [hm,hr,hpow2,hpow9,hpow1]

lemma width_bound (n k R : ℕ) (hR : 1≤R) (hn : n≤R) (hk : k≤R) : width n k≤9*R^2 := by
  have hf (j : ℕ) (hj : j≤R) : 1+j*(j+1)≤3*R^2 := by
    have hh := Nat.mul_le_mul hj (Nat.add_le_add_right hj 1)
    nlinarith
  have h1 := hf n hn
  have h2 := hf k hk
  have h3 := hf (n-k) ((Nat.sub_le ..).trans hn)
  unfold width;omega

lemma cost_bound (n k : ℕ) : cost n k≤3000000*(n+k+1)^10 := by
  let R := n+k+1
  have hR : 1≤R := by dsimp [R];omega
  have hn : n≤R := by dsimp [R];omega
  have hk : k≤R := by dsimp [R];omega
  have hf1 := factorCost_bound n R hR hn
  have hf2 := factorCost_bound k R hR hk
  have hf3 := factorCost_bound (n-k) R hR ((Nat.sub_le ..).trans hn)
  have hw := width_bound n k R hR hn hk
  have hw' : width n k+1≤10*R^2 := by nlinarith
  have h4 : (width n k+1)^4≤10000*R^8 := by
    calc
      _ ≤ (10*R^2)^4 := Nat.pow_le_pow_left hw' 4
      _ = _ := by ring
  have h2 : (width n k+1)^2≤100*R^4 := by
    calc
      _ ≤ (10*R^2)^2 := Nat.pow_le_pow_left hw' 2
      _ = _ := by ring
  have hp8 : R^8≤R^10 := Nat.pow_le_pow_right hR (by decide)
  have hp4 : R^4≤R^10 := Nat.pow_le_pow_right hR (by decide)
  have hp2 : R^2≤R^10 := Nat.pow_le_pow_right hR (by decide)
  have hp1 : R≤R^10 := by simpa using Nat.pow_le_pow_right hR (show 1≤10 by decide)
  have hp0 : 1≤R^10 := Nat.one_le_pow _ _ hR
  have hnk : n+k≤R := by dsimp [R];omega
  change cost n k≤3000000*R^10
  unfold cost ratioCost
  linarith only [hf1,hf2,hf3,hw,h4,h2,hp8,hp4,hp2,hp1,hp0,hnk]

end RationalHitting.StackLanguage.Binomial

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.RationalBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.RationalCanonical

lemma divInt_num_abs (a b : ℤ) (hb : b≠0) :
    (Rat.divInt a b).num.natAbs = a.natAbs/Nat.gcd a.natAbs b.natAbs := by
  rw [Rat.num_divInt,Int.natAbs_ediv_of_dvd (dvd_mul_of_dvd_right (Int.gcd_dvd_right b a) b.sign),
    Int.natAbs_mul,Int.natAbs_sign_of_ne_zero hb,Int.natAbs_natCast,one_mul]
  simp only [Int.gcd, Nat.gcd_comm]

lemma divInt_den (a b : ℤ) (hb : b≠0) :
    (Rat.divInt a b).den = b.natAbs/Nat.gcd a.natAbs b.natAbs := by
  simp [Rat.den_divInt,hb,Int.gcd,Nat.gcd_comm]

/-- The sign used by the canonical binary rational encoder. -/
lemma divInt_sign (a b : ℤ) (hb : b≠0) :
    decide ((Rat.divInt a b).num<0) =
      if a=0 then false else (decide (a<0) ^^ decide (b<0)) := by
  have hs : (Rat.divInt a b).num<0 ↔ (a:ℚ)/(b:ℚ)<0 := by
    rw [←Rat.num_neg, Rat.divInt_eq_div]
  simp only [hs]
  by_cases ha : a=0
  · simp [ha]
  · rw [ite_eq_right ha]
    rcases lt_or_gt_of_ne ha with hna|hpa <;> rcases lt_or_gt_of_ne hb with hnb|hpb
    · have hp : (0:ℚ)<(a:ℚ)/(b:ℚ) := div_pos_of_neg_of_neg (by exact_mod_cast hna) (by exact_mod_cast hnb)
      simp [hna,hnb,not_lt_of_ge hp.le]
    · have hn : (a:ℚ)/(b:ℚ)<0 := div_neg_of_neg_of_pos (by exact_mod_cast hna) (by exact_mod_cast hpb)
      simp [hna,not_lt_of_gt hpb,hn]
    · have hn : (a:ℚ)/(b:ℚ)<0 := div_neg_of_pos_of_neg (by exact_mod_cast hpa) (by exact_mod_cast hnb)
      simp [not_lt_of_gt hpa,hnb,hn]
    · have hp : (0:ℚ)<(a:ℚ)/(b:ℚ) := div_pos (by exact_mod_cast hpa) (by exact_mod_cast hpb)
      simp [not_lt_of_gt hpa,not_lt_of_gt hpb,not_lt_of_ge hp.le]

end RationalHitting.RationalCanonical

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Tabulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage

structure BitWord where
  val : List Bool
  deriving DecidableEq
end RationalHitting.StackLanguage

end OAI
end


