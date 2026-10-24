-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41
-- name    : QAlgorithms_Papers_Independent_Support50_P41
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T22:10:45.499342+00:00
-- url     : https://prove2.me/theorems/7045edba-46ca-4e19-8ff2-8d17a1d5ae72
-- title:
--   Definitions for Sending quantum entanglement through noisy channels
-- statement:
--   The objects the formalized statements of *Sending quantum entanglement through noisy channels* (arXiv:quant-ph/9604023) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `OperatorSum`: PDF pp.5--6, (2)--(3): a specified normalized operator-sum representation.
--   - `CountableOperatorSum`: PDF pp.9--10,34,36: countably indexed operator sums with actual convergence.
--   - `outcomeEntropy`: PDF p.21, (15): Shannon entropy of the computed exchange-matrix diagonal.
--   - `indexState`: PDF p.31: conjugate coefficients in the paired reference basis.
--   - `omegaTilde`: PDF p.31: unnormalized maximally entangled vector, squared norm d.
--   - `relativeVector`: PDF pp.7,31: partial inner product with the reference vector.
--   - `relativeOperator`: PDF pp.32--33: contraction of both reference legs with z.
--   - `normalizedOperatorVector`: PDF pp.34,36: subnormalized vector of D/d, with coefficient A[j,i]/sqrt(d). The p.36 parenthetical tilde is read using the consistent p.34 scaling.
--   - `dilationChoiVector`: PDF pp.35--36: reorder the actual dilation output as (RQ),E.
--   - `padKraus`: PDF p.37: extend a finite Kraus list by zero operators.
--   - `mixedInteraction`: PDF pp.23--24: fixed unitary interaction with an independent mixed environment.
--   - `jointInformation`: PDF pp.24--25: countable mutual information in bits, as a nonnegative relative-entropy sum, so infinite marginal entropies cause no subtraction.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, https://arxiv.org/abs/quant-ph/9604023v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P38
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

/-! Schumacher, arXiv:quant-ph/9604023v1. PDF page numbers; reference-first
coordinates; entropy in bits; squared fidelity. Compilation is pending.
The unquantified recovery claim on p.30 is deferred in HARD.md. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms
open QAlgorithms.Entanglement (IsCompletelyPositive)
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)
open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- PDF pp.5--6, (2)--(3): a specified normalized operator-sum representation. -/
def OperatorSum {d m : ℕ} (Phi : Superop (Fin d) (Fin d))
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  IsKrausFamily A ∧ ∀ X, Phi X = krausApply A X

/-- PDF pp.9--10,34,36: countably indexed operator sums with actual convergence. -/
def CountableOperatorSum {K : Type*} {d : ℕ} (Phi : Superop (Fin d) (Fin d))
    (A : K → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  HasSum (fun k => (A k)ᴴ * A k) 1 ∧
    ∀ X, HasSum (fun k => A k * X * (A k)ᴴ) (Phi X)

/-- PDF p.21, (15): Shannon entropy of the computed exchange-matrix diagonal. -/
def outcomeEntropy {d m : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  -∑ k, (complementaryMap A rho k k).re * Real.logb 2 (complementaryMap A rho k k).re

/-- PDF p.31: conjugate coefficients in the paired reference basis. -/
def indexState {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun i => conj (v i)

/-- PDF p.31: unnormalized maximally entangled vector, squared norm d. -/
def omegaTilde (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then 1 else 0

/-- PDF pp.7,31: partial inner product with the reference vector. -/
def relativeVector {a d : ℕ} (z : EuclideanSpace ℂ (Fin a))
    (v : EuclideanSpace ℂ (Fin a × Fin d)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun j => ∑ i, conj (z i) * v (i, j)

/-- PDF pp.32--33: contraction of both reference legs with z. -/
def relativeOperator {a d : ℕ} (z : EuclideanSpace ℂ (Fin a))
    (D : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun j k => ∑ i, ∑ l, conj (z i) * D (i, j) (l, k) * z l

/-- PDF pp.34,36: subnormalized vector of D/d, with coefficient A[j,i]/sqrt(d).
The p.36 parenthetical tilde is read using the consistent p.34 scaling. -/
def normalizedOperatorVector {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  ((Real.sqrt d)⁻¹ : ℂ) • vectorizeInputFirst A

/-- PDF pp.35--36: reorder the actual dilation output as (RQ),E. -/
def dilationChoiVector {d e : ℕ} [NeZero d]
    (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e)) :
    EuclideanSpace ℂ ((Fin d × Fin d) × Fin e) :=
  WithLp.toLp 2 fun p => dilatedVector U eta (finiteMaxEntangled (Fin d))
    (p.1.1, (p.1.2, p.2))

/-- PDF p.37: extend a finite Kraus list by zero operators. -/
def padKraus {d m : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    Fin n → Matrix (Fin d) (Fin d) ℂ :=
  fun k => if h : k.val < m then A ⟨k.val, h⟩ else 0

/-- PDF pp.23--24: fixed unitary interaction with an independent mixed environment. -/
def mixedInteraction {d e : ℕ} (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ)
    (sigma : Matrix (Fin e) (Fin e) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ :=
  conjSuperop (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (Matrix.kronecker X sigma)

/-- PDF pp.24--25: countable mutual information in bits, as a nonnegative
relative-entropy sum, so infinite marginal entropies cause no subtraction. -/
def jointInformation {X Y : Type*} (P : X × Y → ℝ) : ℝ≥0∞ :=
  ∑' z : X × Y, classicalKLTerm (P z)
    ((∑' y, P (z.1, y)) * (∑' x, P (x, z.2)))

/-- The one-operator identity representation satisfies both normalization and action. -/
example {d : ℕ} : OperatorSum (fun X : Matrix (Fin d) (Fin d) ℂ => X)
    (fun _ : Fin 1 => (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  constructor
  · simp [IsKrausFamily]
  · intro X
    simp [krausApply]

/-- The countable interface agrees with the one-label identity representation. -/
example {d : ℕ} : CountableOperatorSum (fun X : Matrix (Fin d) (Fin d) ℂ => X)
    (fun _ : Fin 1 => (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  constructor
  · simpa using (hasSum_fintype (fun _ : Fin 1 =>
      (1 : Matrix (Fin d) (Fin d) ℂ)ᴴ * 1))
  · intro X
    simpa using (hasSum_fintype (fun _ : Fin 1 =>
      (1 : Matrix (Fin d) (Fin d) ℂ) * X * (1 : Matrix (Fin d) (Fin d) ℂ)ᴴ))

example {d m : ℕ} (Phi : Superop (Fin d) (Fin d))
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (h : OperatorSum Phi A) :
    IsKrausFamily A := h.1

example {K : Type*} {d : ℕ} (Phi : Superop (Fin d) (Fin d))
    (A : K → Matrix (Fin d) (Fin d) ℂ) (h : CountableOperatorSum Phi A) :
    HasSum (fun k => (A k)ᴴ * A k) 1 := h.1

example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) :
    outcomeEntropy (fun k : Fin 0 => Fin.elim0 k) rho = 0 := by simp [outcomeEntropy]

example {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) (i : Fin d) :
    indexState (indexState v) i = v i := by simp [indexState]

example : omegaTilde 1 (0, 0) = 1 := by simp [omegaTilde]

example {a d : ℕ} (v : EuclideanSpace ℂ (Fin a × Fin d)) :
    relativeVector 0 v = 0 := by ext j; simp [relativeVector]

example {a d : ℕ} (D : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    relativeOperator 0 D = 0 := by ext j k; simp [relativeOperator]

example (A : Matrix (Fin 1) (Fin 1) ℂ) : normalizedOperatorVector A (0, 0) = A 0 0 := by
  simp [normalizedOperatorVector, vectorizeInputFirst, Matrix.vec]

example {d e : ℕ} [NeZero d] (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ)
    (eta : EuclideanSpace ℂ (Fin e)) (i j : Fin d) (k : Fin e) :
    dilationChoiVector U eta ((i, j), k) =
      dilatedVector U eta (finiteMaxEntangled (Fin d)) (i, (j, k)) := rfl

example {d m : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (n : ℕ)
    (k : Fin n) (h : m ≤ k.val) : padKraus A n k = 0 := by
  simp [padKraus, Nat.not_lt.mpr h]

example {d e : ℕ} (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ)
    (sigma : Matrix (Fin e) (Fin e) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    mixedInteraction U sigma X = conjSuperop (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
      (Matrix.kronecker X sigma) := rfl

example {X Y : Type*} : jointInformation (fun _ : X × Y => 0) = 0 := by
  simp [jointInformation, classicalKLTerm]

end QAlgorithms.Papers.Independent.Support50.P41


