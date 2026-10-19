-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30
-- name    : QAlgorithms_Papers_Independent_Information100_P30
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T10:18:28.088383+00:00
-- url     : https://prove2.me/theorems/838f3935-9f44-4bb8-bb32-6703c37f07c3
-- title:
--   Definitions for Feasibility Ordering of Entanglement-Source Placement for Qubit Channels
-- statement:
--   The objects the formalized statements of *Feasibility Ordering of Entanglement-Source Placement for Qubit Channels* (arXiv:2609.18803) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `MatrixMap`: Complex-linear maps between local matrix algebras (PDF p.2, §II.A–B).
--   - `tensorMap`: Tensor action expanded in the fixed matrix-unit bases (PDF p.2, Eqs.(8)–(11)). The first map acts on the first subsystem; the local dimensions may differ.
--   - `IsPositiveMap`: Positivity alone, with neither complete positivity nor trace preservation (PDF p.2, §II.B).
--   - `IsQubitChannel`: A qubit channel is a complex-linear CPTP map (PDF p.2, Eq.(5)). The frozen normalized Kraus-family predicate supplies complete positivity and trace preservation.
--   - `IsParallelEA`: Ordinary physical EA on the positive cone, not an all-tensor-powers condition (PDF p.2, Eq.(9)). The separable-positive cone is the frozen finite-sum cone.
--   - `IsStrictlyPositive`: Strict positivity means positivity improving on every nonzero PSD operator (PDF p.2, Eq.(12)); it is not a condition on a Choi matrix.
--   - `channelTranspose`: Channel transpose in the fixed computational basis (PDF p.3, Eq.(16)). If F(X) = Σ K X K†, this gives Σ Kᵀ X conjugate(K); it transposes the superoperator's matrix-unit coefficient array, without conjugating that array.
--   - `depolarizing`: Qubit depolarization with retained-signal parameter q (PDF p.4, Eq.(46)). Channel claims below are made only at q = 1/2 and q = 1/4.
-- source:
--   Feasibility Ordering of Entanglement-Source Placement for Qubit Channels, arXiv:2609.18803v1, https://arxiv.org/abs/2609.18803v1

import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity

/-! Statements of arXiv:2609.18803v1. All new interfaces are local to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Complex-linear maps between local matrix algebras (PDF p.2, §II.A–B). -/
abbrev MatrixMap (I J : Type*) := Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ

/-- Tensor action expanded in the fixed matrix-unit bases (PDF p.2, Eqs.(8)–(11)).
The first map acts on the first subsystem; the local dimensions may differ. -/
def tensorMap {I J K L : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (F : MatrixMap I K) (G : MatrixMap J L) (X : Matrix (I × J) (I × J) ℂ) :
    Matrix (K × L) (K × L) ℂ :=
  ∑ i, ∑ j, ∑ a, ∑ b, X (i,j) (a,b) •
    Matrix.kronecker (F (Matrix.single i a 1)) (G (Matrix.single j b 1))

/-- Positivity alone, with neither complete positivity nor trace preservation (PDF p.2, §II.B). -/
def IsPositiveMap {I J : Type*} [Fintype I] [Fintype J] (F : MatrixMap I J) : Prop :=
  ∀ X, X.PosSemidef → (F X).PosSemidef

/-- A qubit channel is a complex-linear CPTP map (PDF p.2, Eq.(5)).
The frozen normalized Kraus-family predicate supplies complete positivity and trace preservation. -/
def IsQubitChannel (F : MatrixMap Bool Bool) : Prop := IsChannel F

/-- Ordinary physical EA on the positive cone, not an all-tensor-powers condition
(PDF p.2, Eq.(9)). The separable-positive cone is the frozen finite-sum cone. -/
def IsParallelEA (F G : MatrixMap Bool Bool) : Prop :=
  ∀ X : Matrix (Bool × Bool) (Bool × Bool) ℂ, X.PosSemidef →
    Entanglement.IsSeparablePositive (tensorMap F G X)

/-- Strict positivity means positivity improving on every nonzero PSD operator
(PDF p.2, Eq.(12)); it is not a condition on a Choi matrix. -/
def IsStrictlyPositive (F : MatrixMap Bool Bool) : Prop :=
  ∀ X : Matrix Bool Bool ℂ, X.PosSemidef → X ≠ 0 → (F X).PosDef

/-- Channel transpose in the fixed computational basis (PDF p.3, Eq.(16)).
If F(X) = Σ K X K†, this gives Σ Kᵀ X conjugate(K); it transposes the
superoperator's matrix-unit coefficient array, without conjugating that array. -/
def channelTranspose (F : MatrixMap Bool Bool) : MatrixMap Bool Bool where
  toFun X := Matrix.of fun i j => ∑ a : Bool, ∑ b : Bool,
    F (Matrix.single i j 1) a b * X a b
  map_add' X Y := by
    ext i j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j
    simp [Finset.mul_sum, mul_left_comm]
    ring

/-- Qubit depolarization with retained-signal parameter q (PDF p.4, Eq.(46)).
Channel claims below are made only at q = 1/2 and q = 1/4. -/
def depolarizing (q : ℝ) : MatrixMap Bool Bool where
  toFun X := (q : ℂ) • X + (((1-q)/2 : ℝ) : ℂ) • (X.trace • (1 : Matrix Bool Bool ℂ))
  map_add' X Y := by
    simp [Matrix.trace_add, smul_add, add_smul]
    abel
  map_smul' c X := by
    simp [Matrix.trace_smul, smul_add, smul_smul, mul_comm, mul_left_comm]
    ext i j
    simp [smul_eq_mul, Complex.real_smul, mul_assoc]

example {I J K L : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (F : MatrixMap I K) (G : MatrixMap J L) : tensorMap F G 0 = 0 := by
  simp [tensorMap]

example : IsPositiveMap (LinearMap.id : MatrixMap Bool Bool) := fun X hX => hX

example : IsParallelEA (0 : MatrixMap Bool Bool) (0 : MatrixMap Bool Bool) := by
  intro X _
  have hzero : tensorMap (0 : MatrixMap Bool Bool) (0 : MatrixMap Bool Bool) X = 0 := by
    simp [tensorMap]
  rw [hzero]
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j
  · simp

example {I J : Type*} [Fintype I] [Fintype J] :
    IsPositiveMap (0 : MatrixMap I J) := fun X _ => Matrix.PosSemidef.zero

example : IsQubitChannel (LinearMap.id : MatrixMap Bool Bool) := by
  refine ⟨1, fun _ => 1, by simp [IsKrausFamily], ?_⟩
  intro X
  simp [krausApply]

example : ¬ IsStrictlyPositive (0 : MatrixMap Bool Bool) := by
  intro h
  have hp := h 1 Matrix.PosSemidef.one (by simp)
  have ht := hp.2 (x := Finsupp.single false 1) (by simp)
  simp at ht

example : channelTranspose 0 = 0 := by
  ext X i j
  simp [channelTranspose]

example (F : MatrixMap Bool Bool) (i j a b : Bool) :
    channelTranspose F (Matrix.single a b 1) i j = F (Matrix.single i j 1) a b := by
  cases a <;> cases b <;> simp [channelTranspose, Matrix.single_apply]

example : depolarizing 1 = LinearMap.id := by
  ext X i j
  simp [depolarizing]

example (q : ℝ) : depolarizing q (1 : Matrix Bool Bool ℂ) = 1 := by
  ext i j
  simp [depolarizing, Matrix.trace_one, Matrix.one_apply]
  split_ifs <;> push_cast <;> ring

end QAlgorithms.Papers.Independent.Information100.P30


