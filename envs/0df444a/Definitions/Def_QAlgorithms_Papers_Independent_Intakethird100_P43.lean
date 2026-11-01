-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P43
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P43
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:17:26.683345+00:00
-- url     : https://prove2.me/theorems/269dc39f-51a1-4518-bebf-0c10395ce4a7
-- title:
--   Definitions for Distillability via protocols respecting the positivity of partial transpose
-- statement:
--   The objects the formalized statements of *Distillability via protocols respecting the positivity of partial transpose* (arXiv:quant-ph/0104095) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsPPTMap`: PDF p.2, opening of Section II: positive, trace-preserving, and Gamma T Gamma positive on every positive operator. The last condition has no CP amplification.
--   - `IsPositiveConjugatePPTChannel`: PDF pp.1–2: an admissible channel is additionally completely positive. The frozen CP predicate tests id_r tensor T for every finite ancillary dimension r. This differs from Information100.P04.IsPPTChannel, which also requires CP of Gamma T Gamma; that stronger class is deliberately not substituted here.
--   - `IsPositiveConjugatePPTDistillable`: PDF pp.1,3 and Theorem 1 p.2: qualitative distillability means that arbitrarily small singlet error is possible from finitely many identical copies. No rate is prescribed. The channels may depend on the known state and accuracy; they act linearly on all inputs.
--   - `RainsFeasibleEffect`: PDF p.2, (2): the Hermitian effect A and the two Loewner bounds on m Gamma(A). All inequalities are expressed as positivity of the corresponding differences.
--   - `linearTracePair`: PDF p.2, (3): the complex-linear functional X |-> Tr(X A).
--   - `isotropicRaw`: PDF p.2, (3): the two-coefficient isotropic map, on every complex operator X.
--   - `complementaryCoefficient`: PDF p.2, trace equation after (3): B is computed from A, not independent. Used at m>=2, where m^2-1 is nonzero.
--   - `isotropicPreparation`: PDF p.2, (3) with its trace constraint imposed.
--   - `HasIsotropicForm`: PDF p.2: maps of the precise form (3), independently of positivity or trace constraints.
--   - `negativeSpaceWitness`: PDF p.2, (6): the constructed A. Also used at epsilon=2 in the attainment result. In the PPT case P_neg=0 and this is I/m without taking an inverse of its norm.
--   - `positivePPTFidelityValues`: PDF p.2, (1): the operational set of attainable fidelities, over the positive trace-preserving PPT maps of this paper. IsGreatest records both optimality and attainment, so no real supremum default on an empty or unbounded set is used.
-- source:
--   Distillability via protocols respecting the positivity of partial transpose, arXiv:quant-ph/0104095v2, https://arxiv.org/abs/quant-ph/0104095v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

/-!
Statements from Eggeling, Vollbrecht, Werner and Wolf, arXiv:quant-ph/0104095v2.
All page numbers are PDF pages. Accepted imports supply Bob transpose, copies,
Bell and negative spectral projectors, Werner states, and positive complex-linear maps.
Paper-specific definitions implement only the finite-dimensional
model of this paper. In particular PPT preservation below means POSITIVITY of the
transpose-conjugated map, not complete positivity of that map.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P43

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P04
  (gamma copies bellProjector negativeProjector werner)
open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

/-- PDF p.2, opening of Section II: positive, trace-preserving, and Gamma T Gamma
positive on every positive operator. The last condition has no CP amplification. -/
def IsPPTMap {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (T : Matrix (I × J) (I × J) ℂ →ₗ[ℂ] Matrix (K × L) (K × L) ℂ) : Prop :=
  IsPositiveMap T ∧ (∀ X, (T X).trace = X.trace) ∧
    ∀ X, X.PosSemidef → (gamma (T (gamma X))).PosSemidef

/-- PDF pp.1–2: an admissible channel is additionally completely positive.
The frozen CP predicate tests id_r tensor T for every finite ancillary dimension r.
This differs from Information100.P04.IsPPTChannel, which also requires CP of
Gamma T Gamma; that stronger class is deliberately not substituted here. -/
def IsPositiveConjugatePPTChannel {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (T : Matrix (I × J) (I × J) ℂ →ₗ[ℂ] Matrix (K × L) (K × L) ℂ) : Prop :=
  IsPPTMap T ∧ Entanglement.IsCompletelyPositive T

/-- PDF pp.1,3 and Theorem 1 p.2: qualitative distillability means that arbitrarily
small singlet error is possible from finitely many identical copies. No rate is prescribed.
The channels may depend on the known state and accuracy; they act linearly on all inputs. -/
def IsPositiveConjugatePPTDistillable {I J : Type*} [Fintype I] [Fintype J]
    (rho : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∀ eta : ℝ, 0 < eta → eta < 1 → ∃ n : ℕ, 0 < n ∧
    ∃ T : Matrix ((Fin n → I) × (Fin n → J))
        ((Fin n → I) × (Fin n → J)) ℂ →ₗ[ℂ]
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      IsPositiveConjugatePPTChannel T ∧ 1 - eta ≤ effectProb (bellProjector 2) (T (copies rho n))

/-- PDF p.2, (2): the Hermitian effect A and the two Loewner bounds on m Gamma(A).
All inequalities are expressed as positivity of the corresponding differences. -/
def RainsFeasibleEffect {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (m : ℕ) (A : Matrix (I × J) (I × J) ℂ) : Prop :=
  A.IsHermitian ∧ IsEffect A ∧
    (1 - (m : ℂ) • gamma A).PosSemidef ∧
    (1 + (m : ℂ) • gamma A).PosSemidef

/-- PDF p.2, (3): the complex-linear functional X |-> Tr(X A). -/
def linearTracePair {I : Type*} [Fintype I] (A : Matrix I I ℂ) : Matrix I I ℂ →ₗ[ℂ] ℂ where
  toFun X := (X * A).trace
  map_add' X Y := by simp [Matrix.add_mul]
  map_smul' c X := by simp [Matrix.smul_mul]

/-- PDF p.2, (3): the two-coefficient isotropic map, on every complex operator X. -/
def isotropicRaw {I J : Type*} [Fintype I] [Fintype J]
    (m : ℕ) (A B : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × J) (I × J) ℂ →ₗ[ℂ] Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ :=
  (linearTracePair B).smulRight (1 - bellProjector m) +
    (linearTracePair A).smulRight (bellProjector m)

/-- PDF p.2, trace equation after (3): B is computed from A, not independent.
Used at m>=2, where m^2-1 is nonzero. -/
def complementaryCoefficient {I J : Type*} [DecidableEq I] [DecidableEq J]
    (m : ℕ) (A : Matrix (I × J) (I × J) ℂ) : Matrix (I × J) (I × J) ℂ :=
  (((m : ℂ)^2 - 1)⁻¹) • (1 - A)

/-- PDF p.2, (3) with its trace constraint imposed. -/
def isotropicPreparation {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (m : ℕ) (A : Matrix (I × J) (I × J) ℂ) :=
  isotropicRaw m A (complementaryCoefficient m A)

/-- PDF p.2: maps of the precise form (3), independently of positivity or trace constraints. -/
def HasIsotropicForm {I J : Type*} [Fintype I] [Fintype J] {m : ℕ}
    (T : Matrix (I × J) (I × J) ℂ →ₗ[ℂ] Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ) : Prop :=
  ∃ A B, T = isotropicRaw m A B

/-- PDF p.2, (6): the constructed A. Also used at epsilon=2 in the attainment result.
In the PPT case P_neg=0 and this is I/m without taking an inverse of its norm. -/
def negativeSpaceWitness {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (m : ℕ) (epsilon : ℝ) :
    Matrix (I × J) (I × J) ℂ :=
  ((m : ℂ)⁻¹) • (1 - (epsilon : ℂ) • gamma (negativeProjector rho))

/-- PDF p.2, (1): the operational set of attainable fidelities, over the positive
trace-preserving PPT maps of this paper. IsGreatest records both optimality and attainment,
so no real supremum default on an empty or unbounded set is used. -/
def positivePPTFidelityValues {I J : Type*} [Fintype I] [Fintype J]
    (rho : Matrix (I × J) (I × J) ℂ) (m : ℕ) : Set ℝ :=
  {v | ∃ T : Matrix (I × J) (I × J) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ,
    IsPPTMap T ∧ v = effectProb (bellProjector m) (T rho)}

/-- Sanity check: the identity satisfies the paper's channel convention. -/
example {I J : Type*} [Fintype I] [Fintype J] :
    IsPositiveConjugatePPTChannel (LinearMap.id : Matrix (I × J) (I × J) ℂ →ₗ[ℂ]
      Matrix (I × J) (I × J) ℂ) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro X hX; exact hX
    · intro X; rfl
    · intro X hX; exact hX
  · intro r X hX
    exact hX

example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (m : ℕ) : RainsFeasibleEffect m (0 : Matrix (I × J) (I × J) ℂ) := by
  have hg : gamma (0 : Matrix (I × J) (I × J) ℂ) = 0 := rfl
  refine ⟨Matrix.PosSemidef.zero.isHermitian, ⟨Matrix.PosSemidef.zero, ?_⟩, ?_, ?_⟩
  · simpa only [sub_zero] using (Matrix.PosSemidef.one :
      (1 : Matrix (I × J) (I × J) ℂ).PosSemidef)
  · simpa only [hg, smul_zero, sub_zero] using (Matrix.PosSemidef.one :
      (1 : Matrix (I × J) (I × J) ℂ).PosSemidef)
  · simpa only [hg, smul_zero, add_zero] using (Matrix.PosSemidef.one :
      (1 : Matrix (I × J) (I × J) ℂ).PosSemidef)

example {I J : Type*} (X : Matrix (I × J) (I × J) ℂ) : gamma (gamma X) = X := rfl

example {I J : Type*} (X : Matrix (I × J) (I × J) ℂ) :
    gamma X = (Entanglement.partialTransposeFirst X).transpose := rfl

example (m : ℕ) :
    bellProjector (m+1) ((0 : Fin (m+1)), 0) (0, 0) = ((m+1 : ℕ) : ℂ)⁻¹ := by
  simp [bellProjector]

example : bellProjector 1 = (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := by
  ext i j
  simp [bellProjector, Matrix.one_apply, Subsingleton.elim i j, Subsingleton.elim i.1 i.2,
    Subsingleton.elim j.1 j.2]

example {I J : Type*} (rho : Matrix (I × J) (I × J) ℂ) : copies rho 0 = 1 := by
  ext i j
  simp [copies, Matrix.one_apply, Subsingleton.elim i j]

example {I : Type*} [Fintype I] (A X : Matrix I I ℂ) :
    linearTracePair A X = (X * A).trace := rfl

example {I J : Type*} [Fintype I] [Fintype J] (m : ℕ)
    (A B X : Matrix (I × J) (I × J) ℂ) :
    isotropicRaw m A B X = (X*B).trace • (1-bellProjector m) +
      (X*A).trace • bellProjector m := rfl

example {I J : Type*} [DecidableEq I] [DecidableEq J]
    (A : Matrix (I × J) (I × J) ℂ) : complementaryCoefficient 2 A = (1/3 : ℂ) • (1-A) := by
  norm_num [complementaryCoefficient]

example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    negativeProjector (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
  have hz : gamma (0 : Matrix (I × J) (I × J) ℂ) = 0 := rfl
  simp [negativeProjector, hz, cfc_apply_zero]

example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (m : ℕ) :
    negativeSpaceWitness rho m 0 = ((m : ℂ)⁻¹) • 1 := by simp [negativeSpaceWitness]

example (d : ℕ) : werner d 0 =
    (((2 / ((d : ℝ)*(d+1)) : ℝ) : ℂ)) •
      QAlgorithms.Papers.Independent.Information100.P04.wernerP0 d := by simp [werner]

end QAlgorithms.Papers.Independent.Intakethird100.P43


