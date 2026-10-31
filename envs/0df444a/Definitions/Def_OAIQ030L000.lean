-- Prove2me | Definitions.Def_OAIQ030L000
-- name    : OAIQ030L000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:31:26.671999+00:00
-- url     : https://prove2.me/theorems/36a515a1-4178-4e79-8f5a-12782e914e88
-- title:
--   Definitions bundle OAIQ030L000 of the split of OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 252 declarations of OpenAI's Lean: 150 definitions, 1 inductive type or structure and 101 theorems. The definitions and types are `OAI.LaughlinGap.Arithmetic.checkMatrix`, `OAI.LaughlinGap.Arithmetic.checkVector`, `OAI.LaughlinGap.Averaging.adjointMap`, `OAI.LaughlinGap.Averaging.average`, `OAI.LaughlinGap.Averaging.commutator`, `OAI.LaughlinGap.Averaging.coordinates`, `OAI.LaughlinGap.Averaging.invariantSpace`, `OAI.LaughlinGap.Averaging.rotationCommutant`, `OAI.LaughlinGap.Chart.PairSpectators`, `OAI.LaughlinGap.Chart.diagonal`, `OAI.LaughlinGap.Chart.difference`, `OAI.LaughlinGap.Chart.exponent`, `OAI.LaughlinGap.Chart.laughlinPolynomial`, `OAI.LaughlinGap.Chart.pairConfigurationEquiv`, `OAI.LaughlinGap.Chart.spectatorMonomial`, `OAI.LaughlinGap.Chart.spinorChart`, `OAI.LaughlinGap.Chart.statePolynomial`, `OAI.LaughlinGap.ColumnSpace`, `OAI.LaughlinGap.ContractionIndex`, `OAI.LaughlinGap.Occupation.BasisLabel`, `OAI.LaughlinGap.Occupation.ExteriorCoordinates`, `OAI.LaughlinGap.Occupation.Hilbert`, `OAI.LaughlinGap.Occupation.Homogeneous`, `OAI.LaughlinGap.Occupation.PairLabel`, `OAI.LaughlinGap.Occupation.allBasisContraction`, `OAI.LaughlinGap.Occupation.annihilation`, `OAI.LaughlinGap.Occupation.auxiliaryRow`, `OAI.LaughlinGap.Occupation.basicPair`, `OAI.LaughlinGap.Occupation.basisContraction`, `OAI.LaughlinGap.Occupation.bodySpace`, `OAI.LaughlinGap.Occupation.coordinatesFromTensor`, `OAI.LaughlinGap.Occupation.createdGram`, `OAI.LaughlinGap.Occupation.creation`, `OAI.LaughlinGap.Occupation.creationCombination`, `OAI.LaughlinGap.Occupation.creationExteriorHom`, `OAI.LaughlinGap.Occupation.diagonal`, `OAI.LaughlinGap.Occupation.diagonalCLM`, `OAI.LaughlinGap.Occupation.endCongr`, `OAI.LaughlinGap.Occupation.extendLocal`, `OAI.LaughlinGap.Occupation.extendLocalHom` and 111 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LaughlinGap_Averaging`, `LaughlinGap_Basic`, `LaughlinGap_Certificate10`, `LaughlinGap_Certificate11`, `LaughlinGap_Certificate12`, `LaughlinGap_Certificate5`, `LaughlinGap_Certificate6`, `LaughlinGap_CheckedTables`, `LaughlinGap_Contraction`, `LaughlinGap_Creation`, `LaughlinGap_ExtendedPair`, `LaughlinGap_ExteriorTermExpansion`, `LaughlinGap_NormalOrder`, `LaughlinGap_Occupation`, `LaughlinGap_PairEnergy`, `LaughlinGap_PhysicalSpinSpectrum`, `LaughlinGap_RationalExterior`, `LaughlinGap_SpinWork`, `LaughlinGap_TensorSpin`, `LaughlinGap_WedgeIdentification`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinGap`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ030L026`, `OAIQ030L027`, `OAIQ030L028`, `OAIQ030L029`, `OAIQ030L030`, `OAIQ030L031`, `OAIQ030L032`, `OAIQ030L033` and `OAIQ030L034`.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_LaughlinGap

section
-- module Solutions.OAIQ030_LG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Averaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging. -/

noncomputable section


namespace LaughlinGap.Averaging
open scoped BigOperators InnerProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def coordinates : Matrix ι ι ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (ι × ι) where
  toFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  invFun x := Matrix.of (fun i j => x (i,j))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def invariantSpace (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) :
    Submodule ℝ (EuclideanSpace ℝ (ι × ι)) :=
  S.toSubalgebra.toSubmodule.map coordinates.toLinearMap

noncomputable def average (S : StarSubalgebra ℝ (Matrix ι ι ℝ)) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
  coordinates.symm.toLinearMap.comp
    ((invariantSpace S).starProjection.toLinearMap.comp coordinates.toLinearMap)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def adjointMap (F : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ) :
    Matrix κ κ ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
  coordinates.symm.toLinearMap.comp
    ((coordinates.toLinearMap.comp (F.comp coordinates.symm.toLinearMap)).adjoint.comp
      coordinates.toLinearMap)

noncomputable def commutator (L : Matrix ι ι ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun X := L*X-X*L
  map_add' A B := by simp [mul_add, add_mul]; abel
  map_smul' r A := by simp [smul_sub]

noncomputable def rotationCommutant (L : Matrix ι ι ℝ) :
    StarSubalgebra ℝ (Matrix ι ι ℝ) := StarSubalgebra.centralizer ℝ {L}

lemma rotationCommutant_mem (L A : Matrix ι ι ℝ) :
    A ∈ rotationCommutant L ↔ commutator L A = 0 ∧ commutator L.transpose A = 0 := by
  simp only [rotationCommutant, StarSubalgebra.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, commutator,
    LinearMap.coe_mk, AddHom.coe_mk, sub_eq_zero]

end LaughlinGap.Averaging

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Basic. -/

noncomputable section


namespace LaughlinGap
export _root_.OAI.Laughlin (Configuration State Antisymmetric pairCoefficient pairAmplitude energy SpinorVariables bracket laughlinPolynomial monomialExponent laughlinVector distanceToLaughlinSq )
open scoped BigOperators

abbrev TensorHilbert (N Q : ℕ) := EuclideanSpace ℂ (Configuration N Q)

noncomputable def toTensorHilbert {N Q : ℕ} (ψ : State N Q) : TensorHilbert N Q :=
  WithLp.toLp 2 ψ

@[simp]
theorem toTensorHilbert_apply {N Q : ℕ} (ψ : State N Q) (a : Configuration N Q) :
    toTensorHilbert ψ a = ψ a := rfl

@[simp]
theorem toTensorHilbert_norm_sq {N Q : ℕ} (ψ : State N Q) :
    ‖toTensorHilbert ψ‖ ^ 2 = ∑ a, ‖ψ a‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq _

section PairNormalization
open Polynomial

noncomputable def euler (P : ℝ[X]) : ℝ[X] := P.derivative * X

abbrev PairHilbert (Q : ℕ) := EuclideanSpace ℂ (Fin (Q + 1) × Fin (Q + 1))

noncomputable def pairVector (Q p : ℕ) : PairHilbert Q :=
  WithLp.toLp 2 (fun xy => (pairCoefficient Q p xy.1 xy.2 : ℂ))

end PairNormalization

def OrbitalTriple (D : ℕ) :=
  {t : ℕ × ℕ × ℕ // t.1 + t.2.1 + t.2.2 = D ∧ t.2.1 < t.2.2}

noncomputable def tensorMonomialScale {N Q : ℕ} (a : Configuration N Q) : ℝ :=
  ∏ i : Fin N, Real.sqrt (Nat.choose Q (a i).val : ℝ)

noncomputable def statePolynomial {N Q : ℕ} (ψ : State N Q) :
    MvPolynomial (SpinorVariables N) ℂ :=
  ∑ a : Configuration N Q, MvPolynomial.monomial (monomialExponent a)
    ((tensorMonomialScale a : ℂ) * ψ a)

@[simp]
theorem statePolynomial_smul {N Q : ℕ} (c : ℂ) (ψ : State N Q) :
    statePolynomial (c • ψ) = c • statePolynomial ψ := by
  classical
  unfold statePolynomial
  simp only [Finset.smul_sum, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← MvPolynomial.C_mul']
  simp only [MvPolynomial.C_mul_monomial]
  congr 1
  ring

def antisymmetricSubmodule (N Q : ℕ) : Submodule ℂ (TensorHilbert N Q) where
  carrier := {ψ | Antisymmetric (WithLp.ofLp ψ)}
  zero_mem' := by intros i j hij a; simp
  add_mem' := by
    intro ψ φ hψ hφ i j hij a
    change ψ (a ∘ Equiv.swap i j) + φ (a ∘ Equiv.swap i j) = -(ψ a + φ a)
    rw [hψ i j hij a, hφ i j hij a, neg_add]
  smul_mem' := by
    intro c ψ hψ i j hij a
    change c * ψ (a ∘ Equiv.swap i j) = -(c * ψ a)
    rw [hψ i j hij a, mul_neg]

abbrev SectorHilbert (N Q : ℕ) := ↥(antisymmetricSubmodule N Q)

abbrev ContractionIndex (N Q : ℕ) :=
  Fin N × Fin N × Fin (2 * Q - 1) × Configuration N Q

namespace Chart
open MvPolynomial
open scoped BigOperators

noncomputable def difference {σ : Type*} (i j : σ) : MvPolynomial σ ℂ := X j - X i

noncomputable def diagonal {σ : Type*} [DecidableEq σ] (i j : σ) :
    MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ := rename (Function.update id j i)

@[simp]
lemma diagonal_difference {σ : Type*} [DecidableEq σ] (i j : σ) :
    diagonal i j (difference i j) = 0 := by
  by_cases h : i = j
  · simp [difference, h]
  · simp [diagonal, difference, h]

end Chart

namespace Chart
open MvPolynomial

noncomputable def spinorChart (N : ℕ) :
    MvPolynomial (SpinorVariables N) ℂ →ₐ[ℂ] MvPolynomial (Fin N) ℂ :=
  aeval (fun ib => if ib.2 then X ib.1 else 1)

noncomputable def exponent {N Q : ℕ} (a : Configuration N Q) : Fin N →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => (a i).val) (by intro; simp)

noncomputable def statePolynomial {N Q : ℕ} (ψ : State N Q) : MvPolynomial (Fin N) ℂ :=
  ∑ a : Configuration N Q, monomial (exponent a) ((tensorMonomialScale a : ℂ) * ψ a)

noncomputable def laughlinPolynomial (N : ℕ) : MvPolynomial (Fin N) ℂ :=
  ∏ i : Fin N, ∏ j : Fin N, if i < j then difference i j ^ 3 else 1

@[simp] theorem statePolynomial_smul {N Q : ℕ} (c : ℂ) (ψ : State N Q) :
    statePolynomial (c • ψ) = c • statePolynomial ψ := by
  classical
  unfold statePolynomial
  simp only [Finset.smul_sum, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← C_mul']
  simp only [C_mul_monomial]
  congr 1
  ring

@[simp] theorem spinorChart_bracket {N : ℕ} (i j : Fin N) :
    spinorChart N (bracket i j) = difference i j := by
  simp [spinorChart, bracket, difference]

@[simp] theorem spinorChart_laughlinPolynomial (N : ℕ) :
    spinorChart N (LaughlinGap.laughlinPolynomial N) = laughlinPolynomial N := by
  classical
  simp [LaughlinGap.laughlinPolynomial, laughlinPolynomial, apply_ite]

abbrev PairSpectators {N Q : ℕ} (i j : Fin N) :=
  {a : Configuration N Q // a i = 0 ∧ a j = 0}

def pairConfigurationEquiv {N Q : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Configuration N Q ≃ PairSpectators (Q := Q) i j × Fin (Q + 1) × Fin (Q + 1) where
  toFun a := (⟨Function.update (Function.update a i 0) j 0, by simp [hij]⟩, a i, a j)
  invFun t := Function.update (Function.update t.1.val i t.2.1) j t.2.2
  left_inv a := by
    funext k
    by_cases hkj : k = j
    · simp [hkj]
    by_cases hki : k = i
    · simp [hki, hij]
    simp [Function.update_of_ne hkj, Function.update_of_ne hki]
  right_inv t := by
    rcases t with ⟨⟨a, ha⟩, x, y⟩
    apply Prod.ext
    · apply Subtype.ext
      funext k
      by_cases hkj : k = j
      · simp [hkj, ha.2]
      by_cases hki : k = i
      · simp [hki, hij, ha.1]
      simp [Function.update_of_ne hkj, Function.update_of_ne hki]
    · simp [hij]

noncomputable def spectatorMonomial {N Q : ℕ} (i j : Fin N)
    (a : PairSpectators (Q := Q) i j) : MvPolynomial (Fin N) ℂ :=
  ∏ k ∈ (Finset.univ.erase i).erase j,
    C (Real.sqrt (Q.choose (a.val k).val : ℝ) : ℂ) * X k ^ (a.val k).val

end Chart

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Occupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Occupation. -/

noncomputable section


namespace LaughlinGap
namespace Occupation
open scoped BigOperators InnerProduct

abbrev Hilbert (n : ℕ) := EuclideanSpace ℂ (Finset (Fin n))

def flip {n : ℕ} (j : Fin n) : Equiv.Perm (Finset (Fin n)) :=
  let f : Finset (Fin n) → Finset (Fin n) := fun A => if j ∈ A then A.erase j else insert j A
  have h : Function.Involutive f := by
    intro A
    by_cases hj : j ∈ A <;> simp [f, hj]
  ⟨f, f, h, h⟩

@[simp] lemma flip_of_mem {n : ℕ} {j : Fin n} {A : Finset (Fin n)} (h : j ∈ A) :
    flip j A = A.erase j := ite_eq_left h

@[simp] lemma flip_of_not_mem {n : ℕ} {j : Fin n} {A : Finset (Fin n)} (h : j ∉ A) :
    flip j A = insert j A := ite_eq_right h

@[simp] lemma flip_flip {n : ℕ} (j : Fin n) (A : Finset (Fin n)) : flip j (flip j A) = A :=
  (flip j).left_inv A

@[simp] lemma mem_flip_self {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    j ∈ flip j A ↔ j ∉ A := by
  by_cases hj : j ∈ A <;> simp [hj]

@[simp] lemma mem_flip_other {n : ℕ} {i j : Fin n} (hij : i ≠ j) (A : Finset (Fin n)) :
    i ∈ flip j A ↔ i ∈ A := by
  by_cases hj : j ∈ A <;> simp [hj, hij]

lemma flip_comm {n : ℕ} (i j : Fin n) (A : Finset (Fin n)) :
    flip i (flip j A) = flip j (flip i A) := by
  by_cases hij : i = j
  · subst j; rfl
  ext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  by_cases hkj : k = j
  · subst k
    simp [Ne.symm hij]
  simp [hki, hkj]

def sign {n : ℕ} (j : Fin n) (A : Finset (Fin n)) : ℂ :=
  (-1 : ℂ) ^ (A.filter (fun k => k < j)).card

@[simp] lemma sign_norm {n : ℕ} (j : Fin n) (A : Finset (Fin n)) : ‖sign j A‖ = 1 := by
  simp [sign, norm_pow]

@[simp] lemma sign_star {n : ℕ} (j : Fin n) (A : Finset (Fin n)) : star (sign j A) = sign j A := by
  simp [sign]

@[simp] lemma sign_sq {n : ℕ} (j : Fin n) (A : Finset (Fin n)) : sign j A * sign j A = 1 := by
  unfold sign
  rw [← mul_pow]
  norm_num

lemma sign_insert {n : ℕ} (j : Fin n) {i : Fin n} {A : Finset (Fin n)} (hi : i ∉ A) :
    sign j (insert i A) = if i < j then -sign j A else sign j A := by
  by_cases hij : i < j
  · simp [sign, Finset.filter_insert, hij, Finset.card_insert_of_notMem, hi, pow_succ]
  · simp [sign, Finset.filter_insert, hij]

lemma sign_flip {n : ℕ} (i j : Fin n) (A : Finset (Fin n)) :
    sign j (flip i A) = if i < j then -sign j A else sign j A := by
  by_cases hi : i ∈ A
  · have h := sign_insert j (Finset.notMem_erase i A)
    rw [Finset.insert_erase hi] at h
    rw [flip_of_mem hi]
    split_ifs with hij
    · simp only [ite_eq_left hij] at h
      rw [h, neg_neg]
    · simpa [hij] using h.symm
  · rw [flip_of_not_mem hi, sign_insert j hi]

@[simp] lemma sign_flip_self {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    sign j (flip j A) = sign j A := by simp [sign_flip]

@[simp] lemma sign_conj {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    starRingEnd ℂ (sign j A) = sign j A := by
  simp only [sign, map_pow, map_neg, map_one]

@[simp] lemma sign_erase_self {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    sign j (A.erase j) = sign j A := by
  simp [sign, Finset.filter_erase]

@[simp] lemma sign_insert_self {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    sign j (insert j A) = sign j A := by
  simp [sign, Finset.filter_insert]

noncomputable def transition {n : ℕ} (j : Fin n) (ε : Bool) : Hilbert n →ₗ[ℂ] Hilbert n where
  toFun x := WithLp.toLp 2 (fun A =>
    if (decide (j ∈ A)) = ε then sign j A * x (flip j A) else 0)
  map_add' x y := by
    ext A
    by_cases h : (decide (j ∈ A)) = ε <;> simp [h, mul_add]
  map_smul' c x := by
    ext A
    by_cases h : (decide (j ∈ A)) = ε <;> simp [h, mul_left_comm]

@[simp] lemma transition_apply {n : ℕ} (j : Fin n) (ε : Bool) (x : Hilbert n)
    (A : Finset (Fin n)) :
    transition j ε x A = if (decide (j ∈ A)) = ε then sign j A * x (flip j A) else 0 := rfl

noncomputable abbrev annihilation {n : ℕ} (j : Fin n) := transition j false

noncomputable abbrev creation {n : ℕ} (j : Fin n) := transition j true

theorem transition_adjoint {n : ℕ} (j : Fin n) (ε : Bool) :
    (transition j ε).adjoint = transition j (!ε) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rw [← Equiv.sum_comp (flip j) (fun A => inner ℂ (x A) (transition j ε y A))]
  apply Finset.sum_congr rfl
  intro A _
  cases ε <;> by_cases hj : j ∈ A <;>
    simp [transition_apply, hj] <;> ring

theorem transition_anticommute_of_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ε η : Bool) :
    (transition i ε ∘ₗ transition j η) = -(transition j η ∘ₗ transition i ε) := by
  ext x A
  change transition i ε (transition j η x) A = -transition j η (transition i ε x) A
  simp only [transition_apply, mem_flip_other hij, mem_flip_other (Ne.symm hij), sign_flip]
  rw [flip_comm j i A]
  by_cases hi : (decide (i ∈ A)) = ε <;> by_cases hj : (decide (j ∈ A)) = η
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · simp [hi, hj, hlt, not_lt_of_ge (le_of_lt hlt)]
      ring
    · simp [hi, hj, hgt, not_lt_of_ge (le_of_lt hgt)]
      ring
  all_goals simp [hi, hj]

theorem transition_square {n : ℕ} (j : Fin n) (ε : Bool) :
    transition j ε ∘ₗ transition j ε = 0 := by
  ext x A
  change transition j ε (transition j ε x) A = 0
  cases ε <;> by_cases hj : j ∈ A <;> simp [transition_apply, hj]

@[simp] lemma annihilation_adjoint {n : ℕ} (i : Fin n) :
    (annihilation i).adjoint = creation i := transition_adjoint i false

@[simp] lemma creation_adjoint {n : ℕ} (i : Fin n) :
    (creation i).adjoint = annihilation i := transition_adjoint i true

lemma adjoint_mul {n : ℕ} (A B : Module.End ℂ (Hilbert n)) :
    (A * B).adjoint = B.adjoint * A.adjoint := LinearMap.adjoint_comp A B

noncomputable def auxiliaryRow {n : ℕ} {ι : Type*} [Fintype ι] (lam : ℝ)
    (Bt : Module.End ℂ (Hilbert n)) (α : ι → ℝ) (i : ι → Fin n)
    (A : ι → Module.End ℂ (Hilbert n)) : Module.End ℂ (Hilbert n) :=
  (lam : ℂ) • Bt + ∑ b, (α b : ℂ) • (creation (i b) * A b)

noncomputable def weight {n : ℕ} (d : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∏ j ∈ A, d j

noncomputable def diagonal {n : ℕ} (d : Fin n → ℝ) : Hilbert n →ₗ[ℂ] Hilbert n where
  toFun x := WithLp.toLp 2 (fun A => (weight d A : ℂ) * x A)
  map_add' x y := by ext A; simp [mul_add]
  map_smul' c x := by ext A; simp [mul_left_comm]

@[simp] lemma diagonal_apply {n : ℕ} (d : Fin n → ℝ) (x : Hilbert n) (A : Finset (Fin n)) :
    diagonal d x A = (weight d A : ℂ) * x A := rfl

@[simp] theorem diagonal_one {n : ℕ} : diagonal (fun _ : Fin n => (1 : ℝ)) = LinearMap.id := by
  ext x A
  simp [diagonal_apply, weight]

noncomputable def word {n : ℕ} : List (Fin n) → Hilbert n →ₗ[ℂ] Hilbert n
  | [] => LinearMap.id
  | j :: js => word js ∘ₗ annihilation j

noncomputable def pairAnnihilator {n : ℕ} (v : Fin n → Fin n → ℂ) :
    Module.End ℂ (Hilbert n) :=
  ∑ x, ∑ y, if x < y then star (v x y) • (annihilation y * annihilation x) else 0

end Occupation
end LaughlinGap
namespace LaughlinGap
open scoped BigOperators Topology
open Filter

noncomputable def orbitalDiagonalFactor (Q x : ℕ) : ℝ :=
  Real.sqrt ((Q.descFactorial x : ℝ) / (Q : ℝ)^x)

noncomputable def sphericalExteriorPairCoefficient (Q p x y : ℕ) : ℝ :=
  if x + y = p + 1 then
    ((x : ℝ) - (y : ℝ)) * Real.sqrt
      ((Q.descFactorial x : ℝ) * (Q.descFactorial y : ℝ) * (p.factorial : ℝ) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.factorial : ℝ) * (y.factorial : ℝ)))
  else 0

noncomputable def limitingExteriorPairCoefficient (p x y : ℕ) : ℝ :=
  if x + y = p + 1 then
    ((x : ℝ) - (y : ℝ)) * Real.sqrt
      ((p.factorial : ℝ) / ((2 : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ)))
  else 0

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators Topology
open Filter

noncomputable def diagonalCLM {n : ℕ} (d : Fin n → ℝ) : Hilbert n →L[ℂ] Hilbert n :=
  LinearMap.toContinuousLinearMap (diagonal d)

@[simp] lemma diagonalCLM_apply {n : ℕ} (d : Fin n → ℝ) (x : Hilbert n) :
    diagonalCLM d x = diagonal d x := rfl

@[simp] lemma diagonalCLM_one {n : ℕ} : diagonalCLM (fun _ : Fin n => (1 : ℝ)) = 1 := by
  ext x A
  simp [diagonalCLM_apply, diagonal_one]

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Energy. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators Topology
open Filter

noncomputable def localPair (n Q p : ℕ) : Module.End ℂ (Hilbert n) :=
  pairAnnihilator (fun x y => (sphericalExteriorPairCoefficient Q p x.val y.val : ℂ))

noncomputable def localPairStar (n p : ℕ) : Module.End ℂ (Hilbert n) :=
  pairAnnihilator (fun x y => (limitingExteriorPairCoefficient p x.val y.val : ℂ))

noncomputable def localDelta (n Q : ℕ) : Hilbert n →L[ℂ] Hilbert n :=
  diagonalCLM (fun x => orbitalDiagonalFactor Q x.val)

noncomputable def localDeltaInv (n Q : ℕ) : Hilbert n →L[ℂ] Hilbert n :=
  diagonalCLM (fun x => (orbitalDiagonalFactor Q x.val)⁻¹)

noncomputable def localPairEnergyStar (n L : ℕ) (x : Hilbert n) : ℝ :=
  ∑ p : Fin L, ‖localPairStar n p.val x‖ ^ 2

noncomputable def localPairEnergy (n L Q : ℕ) (x : Hilbert n) : ℝ :=
  ∑ p : Fin L, ‖localPair n Q p.val x‖ ^ 2

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

def joinEquiv (n m : ℕ) : (Finset (Fin n) × Finset (Fin m)) ≃ Finset (Fin (n+m)) :=
  Finset.sumEquiv.toEquiv.symm.trans finSumFinEquiv.finsetCongr

def join {n m : ℕ} (A : Finset (Fin n)) (R : Finset (Fin m)) : Finset (Fin (n+m)) :=
  joinEquiv n m (A,R)

noncomputable def slice {n m : ℕ} (R : Finset (Fin m)) : Hilbert (n+m) →ₗ[ℂ] Hilbert n where
  toFun x := WithLp.toLp 2 (fun A => x (join A R))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma slice_apply {n m : ℕ} (R : Finset (Fin m)) (x : Hilbert (n+m))
    (A : Finset (Fin n)) : slice R x A = x (join A R) := rfl

lemma inner_eq_sum_slice {n m : ℕ} (x y : Hilbert (n+m)) :
    inner ℂ x y = ∑ R : Finset (Fin m), inner ℂ (slice R x) (slice R y) := by
  simp only [PiLp.inner_apply, slice_apply]
  rw [← Equiv.sum_comp (joinEquiv n m) (fun A => inner ℂ (x A) (y A)), Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

noncomputable def extendLocal {n m : ℕ} (T : Module.End ℂ (Hilbert n)) :
    Module.End ℂ (Hilbert (n+m)) where
  toFun x := WithLp.toLp 2 (fun S =>
    T (slice ((joinEquiv n m).symm S).2 x) ((joinEquiv n m).symm S).1)
  map_add' x y := by ext S; simp
  map_smul' c x := by ext S; simp

@[simp] lemma slice_extendLocal {n m : ℕ} (R : Finset (Fin m)) (T : Module.End ℂ (Hilbert n))
    (x : Hilbert (n+m)) : slice R (extendLocal T x) = T (slice R x) := by
  ext A
  simp [slice_apply, extendLocal, join]

lemma eq_of_slice_eq {n m : ℕ} {x y : Hilbert (n+m)}
    (h : ∀ R : Finset (Fin m), slice R x = slice R y) : x = y := by
  ext S
  obtain ⟨⟨A,R⟩, rfl⟩ := (joinEquiv n m).surjective S
  exact congrArg (fun z : Hilbert n => z A) (h R)

@[simp] theorem extendLocal_one {n m : ℕ} :
    extendLocal (m := m) (1 : Module.End ℂ (Hilbert n)) = 1 := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  simp

@[simp] theorem extendLocal_add {n m : ℕ} (T S : Module.End ℂ (Hilbert n)) :
    extendLocal (m := m) (T + S) = extendLocal T + extendLocal S := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  simp

@[simp] theorem extendLocal_mul {n m : ℕ} (T S : Module.End ℂ (Hilbert n)) :
    extendLocal (m := m) (T * S) = extendLocal T * extendLocal S := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  simp only [Module.End.mul_apply, slice_extendLocal]

@[simp] theorem extendLocal_zero {n m : ℕ} :
    extendLocal (m := m) (0 : Module.End ℂ (Hilbert n)) = 0 := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  simp

@[simp] theorem extendLocal_smul {n m : ℕ} (c : ℂ) (T : Module.End ℂ (Hilbert n)) :
    extendLocal (m := m) (c • T) = c • extendLocal T := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  simp

@[simp] theorem extendLocal_adjoint {n m : ℕ} (T : Module.End ℂ (Hilbert n)) :
    (extendLocal (m := m) T).adjoint = extendLocal T.adjoint := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_eq_sum_slice, inner_eq_sum_slice]
  simp only [slice_extendLocal, LinearMap.adjoint_inner_left]

noncomputable def extendLocalHom (n m : ℕ) :
    Module.End ℂ (Hilbert n) →⋆ₐ[ℂ] Module.End ℂ (Hilbert (n+m)) where
  toFun := extendLocal
  map_one' := extendLocal_one
  map_mul' := extendLocal_mul
  map_zero' := extendLocal_zero
  map_add' := extendLocal_add
  commutes' c := by
    change extendLocal (m := m) (c • (1 : Module.End ℂ (Hilbert n))) = c • 1
    rw [extendLocal_smul, extendLocal_one]
  map_star' T := (extendLocal_adjoint T).symm

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped BigOperators InnerProduct ComplexOrder

section PositiveLifting
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

noncomputable def matrixLift (B : ι → Module.End ℂ E) :
    Matrix ι ι ℂ →ₗ[ℂ] Module.End ℂ E where
  toFun M := ∑ i, ∑ j, M i j • ((B i).adjoint * B j)
  map_add' M N := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.smul_sum, smul_smul]

noncomputable def contractCombination (B : ι → Module.End ℂ E) (v : ι → ℂ) :
    Module.End ℂ E := ∑ i, star (v i) • B i

end PositiveLifting

namespace Occupation

abbrev BasisLabel (n k : ℕ) := {A : Finset (Fin n) // A.card = k}

abbrev ExteriorCoordinates (n k : ℕ) := EuclideanSpace ℂ (BasisLabel n k)

noncomputable def basisContraction {n k : ℕ} (A : BasisLabel n k) :
    Module.End ℂ (Hilbert n) := word (A.val.sort (· ≤ ·))

noncomputable def exteriorContraction {n k : ℕ} (v : ExteriorCoordinates n k) :
    Module.End ℂ (Hilbert n) := contractCombination basisContraction v

noncomputable def exteriorLift {n k : ℕ} :
    Matrix (BasisLabel n k) (BasisLabel n k) ℂ →ₗ[ℂ] Module.End ℂ (Hilbert n) :=
  matrixLift basisContraction

end Occupation
end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

def Homogeneous {n : ℕ} (k : ℕ) (x : Hilbert n) : Prop :=
  ∀ A, A.card ≠ k → x A = 0

lemma annihilation_homogeneous {n k : ℕ} {x : Hilbert n} (hx : Homogeneous (k+1) x)
    (j : Fin n) : Homogeneous k (annihilation j x) := by
  intro A hA
  by_cases hj : j ∈ A
  · simp [transition_apply, hj]
  · rw [transition_apply]
    simp only [hj, decide_false, ite_true, flip_of_not_mem hj]
    rw [hx (insert j A) (by rw [Finset.card_insert_of_notMem hj]; omega), mul_zero]

lemma word_apply_empty_sorted {n : ℕ} (js : List (Fin n))
    (hs : js.Pairwise (· < ·)) (x : Hilbert n) : word js x ∅ = x js.toFinset := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih =>
    obtain ⟨hj, hs⟩ := List.pairwise_cons.mp hs
    change word js (annihilation j x) ∅ = _
    rw [ih hs]
    have hj' : j ∉ js.toFinset := by
      intro h
      exact lt_irrefl j (hj j (List.mem_toFinset.mp h))
    have he : (js.toFinset.filter (fun k => k < j)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hij
      exact not_lt_of_gt (hj i (List.mem_toFinset.mp hi)) hij
    simp [transition_apply, hj', sign, he]

@[simp] lemma basisContraction_apply_empty {n k : ℕ} (A : BasisLabel n k) (x : Hilbert n) :
    basisContraction A x ∅ = x A.val := by
  simpa only [basisContraction, Finset.sort_toFinset] using
    word_apply_empty_sorted (A.val.sort (· ≤ ·)) A.val.sortedLT_sort.pairwise x

noncomputable def vacuum (n : ℕ) : Hilbert n := EuclideanSpace.single ∅ 1

@[simp] lemma vacuum_apply (n : ℕ) (A : Finset (Fin n)) :
    vacuum n A = if A = ∅ then 1 else 0 := by
  simp only [vacuum, PiLp.single_apply]

@[simp] lemma vacuum_norm (n : ℕ) : ‖vacuum n‖ = 1 := by
  simp [vacuum]

lemma degree_zero_eq_vacuum {n : ℕ} {x : Hilbert n} (hx : Homogeneous 0 x) :
    x = x ∅ • vacuum n := by
  ext A
  by_cases h : A = ∅
  · simp [h]
  · have hc : A.card ≠ 0 := by simpa using h
    simp [vacuum_apply, h, hx A hc]

noncomputable def sectorInclusion (n k : ℕ) : ExteriorCoordinates n k →ₗ[ℂ] Hilbert n where
  toFun x := WithLp.toLp 2 (fun A => if h : A.card = k then x ⟨A,h⟩ else 0)
  map_add' x y := by
    ext A
    by_cases h : A.card = k <;> simp [h]
  map_smul' c x := by
    ext A
    by_cases h : A.card = k <;> simp [h]

@[simp] lemma sectorInclusion_apply {n k : ℕ} (x : ExteriorCoordinates n k)
    (A : Finset (Fin n)) :
    sectorInclusion n k x A = if h : A.card = k then x ⟨A,h⟩ else 0 := rfl

@[simp] lemma sectorInclusion_apply_label {n k : ℕ} (x : ExteriorCoordinates n k)
    (A : BasisLabel n k) : sectorInclusion n k x A.val = x A := by
  simp only [sectorInclusion_apply, A.property, ↓reduceDIte]

lemma sectorInclusion_homogeneous {n k : ℕ} (x : ExteriorCoordinates n k) :
    Homogeneous k (sectorInclusion n k x) := fun A h => by simp [h]

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Contraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators InnerProduct Topology

section BlockOperator
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

abbrev ColumnSpace (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] := PiLp 2 (fun _ : ι => E)

noncomputable def columnProjection (b : ι) : ColumnSpace ι E →L[ℂ] E :=
  (PiLp.projₗ 2 (fun _ : ι => E) b).toContinuousLinearMap

omit [DecidableEq ι] in
@[simp] lemma columnProjection_apply (b : ι) (x : ColumnSpace ι E) :
    columnProjection b x = x b := rfl

end BlockOperator
end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct Topology ComplexOrder

@[simp] lemma word_nil {n : ℕ} : word ([] : List (Fin n)) = 1 := rfl
@[simp] lemma word_cons {n : ℕ} (j : Fin n) (js : List (Fin n)) :
    word (j :: js) = word js * annihilation j := rfl

lemma annihilation_anticommute {n : ℕ} (i j : Fin n) :
    annihilation i * annihilation j = -(annihilation j * annihilation i) := by
  by_cases h : i = j
  · subst j
    have hz : annihilation i * annihilation i = 0 := transition_square i false
    simp only [hz, neg_zero]
  · exact transition_anticommute_of_ne h false false

@[simp] lemma inner_vacuum_left {n : ℕ} (x : Hilbert n) :
    inner ℂ (vacuum n) x = x ∅ := by
  simp [vacuum, EuclideanSpace.inner_single_left]

noncomputable def allBasisContraction {n : ℕ} (A : Finset (Fin n)) : Module.End ℂ (Hilbert n) :=
  word (A.sort (· ≤ ·))

noncomputable def fullContraction {n : ℕ} (v : Hilbert n) : Module.End ℂ (Hilbert n) :=
  contractCombination allBasisContraction v

@[simp] theorem fullContraction_single {n : ℕ} (A : Finset (Fin n)) (c : ℂ) :
    fullContraction (EuclideanSpace.single A c) = star c • allBasisContraction A := by
  classical
  simp [fullContraction, contractCombination, PiLp.single_apply, apply_ite, ite_smul]

@[simp] theorem fullContraction_add {n : ℕ} (v w : Hilbert n) :
    fullContraction (v+w) = fullContraction v + fullContraction w := by
  simp [fullContraction, contractCombination, add_smul, Finset.sum_add_distrib]

@[simp] theorem fullContraction_smul {n : ℕ} (c : ℂ) (v : Hilbert n) :
    fullContraction (c • v) = star c • fullContraction v := by
  simp [fullContraction, contractCombination, smul_smul, Finset.smul_sum]

@[simp] theorem fullContraction_zero {n : ℕ} : fullContraction (0 : Hilbert n) = 0 := by
  simp [fullContraction, contractCombination]

noncomputable def reconstruct {n : ℕ} :
    Module.End ℂ (Hilbert n) →ₗ[ℂ] Module.End ℂ (Hilbert n) where
  toFun B := fullContraction (B.adjoint (vacuum n))
  map_add' B B' := by simp
  map_smul' c B := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, fullContraction_smul,
      Complex.star_def, Complex.conj_conj, RingHom.id_apply]

noncomputable def createdGram {n : ℕ} {ι : Type*} (B : ι → Module.End ℂ (Hilbert n)) :
    Matrix ι ι ℂ := fun r s => inner ℂ ((B r).adjoint (vacuum n)) ((B s).adjoint (vacuum n))

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

abbrev PairLabel (n : ℕ) := {a : Fin n × Fin n // a.1 < a.2}

noncomputable def basicPair {n : ℕ} (a : PairLabel n) : Module.End ℂ (Hilbert n) :=
  annihilation a.val.2 * annihilation a.val.1

noncomputable def pairContraction {n : ℕ} (v : PairLabel n → ℂ) : Module.End ℂ (Hilbert n) :=
  ∑ a, star (v a) • basicPair a

noncomputable def oneContraction {n : ℕ} (a b : PairLabel n) : Module.End ℂ (Hilbert n) :=
  -(if a.val.1 = b.val.1 then creation b.val.2 * annihilation a.val.2 else 0) +
    (if a.val.2 = b.val.1 then creation b.val.2 * annihilation a.val.1 else 0) +
    (if a.val.1 = b.val.2 then creation b.val.1 * annihilation a.val.2 else 0) -
    (if a.val.2 = b.val.2 then creation b.val.1 * annihilation a.val.1 else 0)

noncomputable def pairOneContraction {n : ℕ} (v w : PairLabel n → ℂ) :
    Module.End ℂ (Hilbert n) :=
  ∑ a, ∑ b, (star (v a) * w b) • oneContraction a b

noncomputable def pairHamiltonian {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : Module.End ℂ (Hilbert n) :=
  ∑ p, (pairContraction (v p)).adjoint * pairContraction (v p)

noncomputable def pairThreeTerm {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : Module.End ℂ (Hilbert n) :=
  ∑ p, ∑ r, (pairContraction (v p)).adjoint * pairOneContraction (v p) (v r) *
    pairContraction (v r)

noncomputable def pairFourTerm {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : Module.End ℂ (Hilbert n) :=
  ∑ p, ∑ r, (pairContraction (v r) * pairContraction (v p)).adjoint *
    (pairContraction (v r) * pairContraction (v p))

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal Order. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

noncomputable def bodySpace (n k : ℕ) : Submodule ℂ (Module.End ℂ (Hilbert n)) :=
  (exteriorLift (n := n) (k := k)).range

@[simp] lemma exteriorLift_single {n k : ℕ} (A B : BasisLabel n k) (c : ℂ) :
    exteriorLift (Matrix.single A B c) = c • ((basisContraction A).adjoint * basisContraction B) := by
  classical
  simp [exteriorLift, matrixLift, Matrix.single_apply, ite_smul, ite_and]

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

noncomputable def sectorReadout (n k : ℕ) : Hilbert n →ₗ[ℂ] ExteriorCoordinates n k where
  toFun x := WithLp.toLp 2 (fun A => x A.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma sectorReadout_apply {n k : ℕ} (x : Hilbert n) (A : BasisLabel n k) :
    sectorReadout n k x A = x A.val := rfl

noncomputable def pairWedgeColumn {n : ℕ} (v w : PairLabel n → ℂ) : ExteriorCoordinates n 4 :=
  sectorReadout n 4 ((pairContraction w * pairContraction v).adjoint (vacuum n))

noncomputable def pairWedgeMatrix {n : ℕ} {ι : Type*} (v : ι → PairLabel n → ℂ) :
    Matrix (BasisLabel n 4) (ι × ι) ℂ := fun A pr => pairWedgeColumn (v pr.1) (v pr.2) A

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma sectorInclusion_adjoint (n k : ℕ) : (sectorInclusion n k).adjoint = sectorReadout n k := by
  classical
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  let f : Finset (Fin n) → ℂ := fun A => inner ℂ (x A) (sectorInclusion n k y A)
  calc
    (∑ A : BasisLabel n k, inner ℂ (sectorReadout n k x A) (y A)) =
        ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => A.card = k), f A := by
      have h := Finset.sum_subtype (p := fun A : Finset (Fin n) => A.card = k) (F := inferInstance) (Finset.univ.filter (fun A : Finset (Fin n) => A.card = k))
        (by simp) f
      simpa only [f, sectorInclusion_apply_label, sectorReadout_apply] using h.symm
    _ = ∑ A, inner ℂ (x A) (sectorInclusion n k y A) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro A _ hA
      have hh : A.card ≠ k := by simpa using hA
      simp [f, sectorInclusion_apply, hh]

noncomputable def sectorExtract (n k : ℕ) :
    Module.End ℂ (Hilbert n) →ₗ[ℂ] Matrix (BasisLabel n k) (BasisLabel n k) ℂ where
  toFun T := Matrix.toEuclideanLin.symm (sectorReadout n k ∘ₗ T ∘ₗ sectorInclusion n k)
  map_add' _ _ := by simp only [LinearMap.comp_add, LinearMap.add_comp, map_add]
  map_smul' _ _ := by simp only [LinearMap.comp_smul, LinearMap.smul_comp, map_smul, RingHom.id_apply]

@[simp] lemma sectorExtract_toEuclideanLin (n k : ℕ) (T : Module.End ℂ (Hilbert n)) :
    (sectorExtract n k T).toEuclideanLin = sectorReadout n k ∘ₗ T ∘ₗ sectorInclusion n k :=
  Matrix.toEuclideanLin.apply_symm_apply _

lemma numberOperator_apply {n : ℕ} (x : Hilbert n) (A : Finset (Fin n)) :
    (∑ i : Fin n, creation i (annihilation i x)) A = (A.card : ℂ) * x A := by
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  have ht (i : Fin n) : creation i (annihilation i x) A = if i ∈ A then x A else 0 := by
    by_cases hi : i ∈ A <;>
      simp [transition_apply, hi, ← mul_assoc]
  simp only [ht]
  rw [← Finset.sum_filter]
  simp

noncomputable def pairTripleOperator {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : Module.End ℂ (Hilbert n) :=
  ∑ p, ∑ i : Fin n, (annihilation i * pairContraction (v p)).adjoint *
    (annihilation i * pairContraction (v p))

noncomputable def tripleWedgeColumn {n : ℕ} (v : PairLabel n → ℂ) (i : Fin n) :
    ExteriorCoordinates n 3 :=
  sectorReadout n 3 ((annihilation i * pairContraction v).adjoint (vacuum n))

noncomputable def tripleWedgeMatrix {n : ℕ} {ι : Type*} (v : ι → PairLabel n → ℂ) :
    Matrix (BasisLabel n 3) (ι × Fin n) ℂ := fun A pi => tripleWedgeColumn (v pi.1) pi.2 A

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

noncomputable def physicalPairForms (Q : ℕ) : Fin (2*Q-1) → PairLabel (Q+1) → ℂ := fun p a =>
  (sphericalExteriorPairCoefficient Q p.val a.val.1.val a.val.2.val : ℂ)

noncomputable def physicalOccupationHamiltonian (Q : ℕ) : Module.End ℂ (Hilbert (Q+1)) :=
  pairHamiltonian (physicalPairForms Q)

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma numberOperator_homogeneous {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x) :
    (∑ i : Fin n, creation i (annihilation i x)) = (k : ℂ) • x := by
  ext A
  rw [numberOperator_apply]
  change (A.card : ℂ) * x A = (k : ℂ) * x A
  by_cases hA : A.card = k
  · rw [hA]
  · rw [hx A hA, mul_zero, mul_zero]

lemma sum_annihilation_norm_sq {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x) :
    ∑ i : Fin n, ‖annihilation i x‖ ^ 2 = (k : ℝ) * ‖x‖ ^ 2 := by
  have h := congrArg (fun y : Hilbert n => (inner ℂ x y).re) (numberOperator_homogeneous hx)
  simp only [inner_sum, Complex.re_sum, ← annihilation_adjoint,
    LinearMap.adjoint_inner_right, inner_smul_right,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at h
  have hr (y : Hilbert n) : (inner ℂ y y).re = ‖y‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm
  simpa only [hr] using h

noncomputable def rawReadout (n N : ℕ) : Hilbert n →ₗ[ℂ] EuclideanSpace ℂ (Fin N → Fin n) where
  toFun x := WithLp.toLp 2 (fun a => word (List.ofFn a) x ∅)
  map_add' x y := by ext a; simp only [map_add, PiLp.add_apply]
  map_smul' c x := by ext a; simp only [map_smul, RingHom.id_apply, PiLp.smul_apply]

@[simp] lemma rawReadout_apply {n N : ℕ} (x : Hilbert n) (a : Fin N → Fin n) :
    rawReadout n N x a = word (List.ofFn a) x ∅ := rfl

lemma rawReadout_succ {n N : ℕ} (x : Hilbert n) (a : Fin (N+1) → Fin n) :
    rawReadout n (N+1) x a = rawReadout n N (annihilation (a 0) x) (fun i => a i.succ) := by
  simp only [rawReadout_apply, List.ofFn_succ, word_cons, Module.End.mul_apply]

theorem rawReadout_norm_sq {n N : ℕ} {x : Hilbert n} (hx : Homogeneous N x) :
    ‖rawReadout n N x‖ ^ 2 = (N.factorial : ℝ) * ‖x‖ ^ 2 := by
  induction N generalizing x with
  | zero =>
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_unique, rawReadout_apply, List.ofFn_zero, word_nil,
      Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, one_mul]
    rw [degree_zero_eq_vacuum hx, norm_smul, vacuum_norm, mul_one]
    simp
  | succ N ih =>
    rw [EuclideanSpace.norm_sq_eq]
    rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Fin n)).sum_comp]
    simp only [Fintype.sum_prod_type]
    change (∑ i : Fin n, ∑ a : Fin N → Fin n,
      ‖rawReadout n (N+1) x (Fin.cons i a)‖ ^ 2) = _
    simp only [rawReadout_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [← EuclideanSpace.norm_sq_eq, ih (annihilation_homogeneous hx _)]
    rw [← Finset.mul_sum, sum_annihilation_norm_sq hx, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring

noncomputable def normalizedReadout (n N : ℕ) :
    Hilbert n →ₗ[ℂ] EuclideanSpace ℂ (Fin N → Fin n) :=
  ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) • rawReadout n N

@[simp] lemma normalizedReadout_apply {n N : ℕ} (x : Hilbert n) (a : Fin N → Fin n) :
    normalizedReadout n N x a =
      ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) * word (List.ofFn a) x ∅ := rfl

lemma normalizedReadout_norm_sq {n N : ℕ} {x : Hilbert n} (hx : Homogeneous N x) :
    ‖normalizedReadout n N x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hf : 0 < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hs : 0 < Real.sqrt (N.factorial : ℝ) := Real.sqrt_pos.mpr hf
  simp only [normalizedReadout, LinearMap.smul_apply, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_pow,
    inv_pow, Real.sq_sqrt hf.le, rawReadout_norm_sq hx]
  field_simp

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Creation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Creation. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma creation_anticommute {n : ℕ} (i j : Fin n) :
    creation i * creation j = -(creation j * creation i) := by
  have h := congrArg (fun T : Module.End ℂ (Hilbert n) => T.adjoint)
    (annihilation_anticommute j i)
  simpa only [adjoint_mul, annihilation_adjoint, map_neg] using h

noncomputable def creationCombination (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] Module.End ℂ (Hilbert n) where
  toFun v := ∑ i, (v i) • creation i
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [smul_smul, Finset.smul_sum]

lemma creationCombination_square (n : ℕ) (v : Fin n → ℂ) :
    creationCombination n v * creationCombination n v = 0 := by
  have h : creationCombination n v * creationCombination n v =
      -(creationCombination n v * creationCombination n v) := by
    simp only [creationCombination, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [creation_anticommute j i, mul_comm (v j) (v i), smul_neg]
  apply LinearMap.ext
  intro x
  ext A
  have he := congrArg (fun T : Module.End ℂ (Hilbert n) => T x A) h
  change (creationCombination n v * creationCombination n v) x A =
    -((creationCombination n v * creationCombination n v) x A) at he
  change (creationCombination n v * creationCombination n v) x A = 0
  linear_combination (1/2 : ℂ) * he

noncomputable def creationExteriorHom (n : ℕ) :
    ExteriorAlgebra ℂ (Fin n → ℂ) →ₐ[ℂ] Module.End ℂ (Hilbert n) :=
  ExteriorAlgebra.lift ℂ ⟨creationCombination n, creationCombination_square n⟩

@[simp] lemma creationCombination_single {n : ℕ} (j : Fin n) :
    creationCombination n (Pi.single j 1) = creation j := by
  classical
  simp [creationCombination, Pi.single_apply, ite_smul]

lemma creationExteriorHom_multi {n N : ℕ} (a : Fin N → Fin n) :
    creationExteriorHom n (ExteriorAlgebra.ιMulti ℂ N (fun i => Pi.single (a i) 1)) =
      (word (List.ofFn a)).adjoint := by
  induction N with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply, word_nil]
  | succ N ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    simp only [creationExteriorHom, ExteriorAlgebra.lift_ι_apply, creationCombination_single]
    change creation (a 0) * creationExteriorHom n
      (ExteriorAlgebra.ιMulti ℂ N (fun i => Pi.single (a i.succ) 1)) = _
    rw [ih]
    simp only [List.ofFn_succ, word_cons, adjoint_mul, annihilation_adjoint]

lemma word_ofFn_swap {n N : ℕ} (a : Fin N → Fin n) (i j : Fin N) (hij : i ≠ j) :
    word (List.ofFn (a ∘ Equiv.swap i j)) = -word (List.ofFn a) := by
  have hh := (ExteriorAlgebra.ιMulti ℂ N (M := Fin n → ℂ)).map_swap
    (fun k => Pi.single (a k) 1) hij
  have he := congrArg (creationExteriorHom n) hh
  simp only [map_neg] at he
  change creationExteriorHom n (ExteriorAlgebra.ιMulti ℂ N
    (fun k => Pi.single ((a ∘ Equiv.swap i j) k) 1)) = _ at he
  rw [creationExteriorHom_multi, creationExteriorHom_multi] at he
  have hf := congrArg (fun T : Module.End ℂ (Hilbert n) => T.adjoint) he
  simpa only [LinearMap.adjoint_adjoint, map_neg] using hf

theorem normalizedReadout_antisymmetric {Q N : ℕ} (x : Hilbert (Q+1)) :
    Antisymmetric (WithLp.ofLp (normalizedReadout (Q+1) N x)) := by
  intro i j hij a
  simp only [normalizedReadout_apply, word_ofFn_swap a i j hij,
    LinearMap.neg_apply, PiLp.neg_apply, mul_neg]

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped BigOperators InnerProduct

lemma Antisymmetric.perm {N Q : ℕ} {ψ : State N Q} (hψ : Antisymmetric ψ)
    (a : Configuration N Q) (σ : Equiv.Perm (Fin N)) :
    ψ (a ∘ σ) = Equiv.Perm.sign σ • ψ a := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap s i j hij ih => simp_all [← Function.comp_assoc, hψ i j hij]

lemma Antisymmetric.eq_zero_of_not_injective {N Q : ℕ} {ψ : State N Q}
    (hψ : Antisymmetric ψ) {a : Configuration N Q} (ha : ¬ Function.Injective a) :
    ψ a = 0 := by
  classical
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp ha
  have he : a ∘ Equiv.swap i j = a := by
    ext k
    by_cases hki : k = i
    · subst k; simp [hij]
    by_cases hkj : k = j
    · subst k; simp [hij]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hh := hψ i j hne a
  rw [he] at hh
  linear_combination (1/2 : ℂ) * hh

lemma Antisymmetric.ext_increasing {N Q : ℕ} {ψ φ : State N Q}
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ)
    (he : ∀ a, StrictMono a → ψ a = φ a) : ψ = φ := by
  funext a
  by_cases hi : Function.Injective a
  · have hs : StrictMono (a ∘ Tuple.sort a) :=
      (Tuple.monotone_sort a).strictMono_of_injective (hi.comp (Tuple.sort a).injective)
    have he' := he (a ∘ Tuple.sort a) hs
    rw [Antisymmetric.perm hψ, Antisymmetric.perm hφ] at he'
    exact (smul_left_cancel _ he')
  · rw [Antisymmetric.eq_zero_of_not_injective hψ hi,
      Antisymmetric.eq_zero_of_not_injective hφ hi]

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

noncomputable def increasingConfiguration {n N : ℕ} (A : BasisLabel n N) : Fin N → Fin n :=
  A.val.orderEmbOfFin A.property

lemma ofFn_increasingConfiguration {n N : ℕ} (A : BasisLabel n N) :
    List.ofFn (increasingConfiguration A) = A.val.sort (· ≤ ·) := by
  rw [List.ofFn_eq_map]
  exact A.val.listMap_orderEmbOfFin_finRange A.property

@[simp] lemma normalizedReadout_increasing {n N : ℕ} (x : Hilbert n) (A : BasisLabel n N) :
    normalizedReadout n N x (increasingConfiguration A) =
      ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) * x A.val := by
  rw [normalizedReadout_apply, ofFn_increasingConfiguration]
  rw [show word (A.val.sort (· ≤ ·)) = basisContraction A from rfl,
    basisContraction_apply_empty]

noncomputable def coordinatesFromTensor (Q N : ℕ) : TensorHilbert N Q →ₗ[ℂ]
    ExteriorCoordinates (Q+1) N where
  toFun ψ := WithLp.toLp 2 (fun A => (Real.sqrt (N.factorial : ℝ) : ℂ) *
    ψ (increasingConfiguration A))
  map_add' ψ φ := by ext A; exact mul_add _ _ _
  map_smul' c ψ := by ext A; exact mul_left_comm _ _ _

@[simp] lemma coordinatesFromTensor_apply {Q N : ℕ} (ψ : TensorHilbert N Q)
    (A : BasisLabel (Q+1) N) :
    coordinatesFromTensor Q N ψ A = (Real.sqrt (N.factorial : ℝ) : ℂ) *
      ψ (increasingConfiguration A) := rfl

lemma coordinatesFromTensor_readout {Q N : ℕ} (x : ExteriorCoordinates (Q+1) N) :
    coordinatesFromTensor Q N (normalizedReadout (Q+1) N (sectorInclusion (Q+1) N x)) = x := by
  have hs : (Real.sqrt (N.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos N))
  ext A
  simp only [coordinatesFromTensor_apply, normalizedReadout_increasing,
    sectorInclusion_apply_label]
  field_simp

theorem readout_coordinatesFromTensor {Q N : ℕ} {ψ : TensorHilbert N Q}
    (hψ : Antisymmetric (WithLp.ofLp ψ)) :
    normalizedReadout (Q+1) N (sectorInclusion (Q+1) N (coordinatesFromTensor Q N ψ)) = ψ := by
  classical
  apply (WithLp.equiv 2 _).injective
  apply Antisymmetric.ext_increasing (normalizedReadout_antisymmetric _) hψ
  intro a ha
  let A : BasisLabel (Q+1) N := ⟨Finset.univ.image a, by
    rw [Finset.card_image_of_injective _ ha.injective, Finset.card_fin]⟩
  have he : increasingConfiguration A = a := by
    symm
    exact Finset.orderEmbOfFin_unique A.property (by intro i; exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩) ha
  rw [← he]
  change normalizedReadout (Q+1) N _ (increasingConfiguration A) = ψ (increasingConfiguration A)
  rw [normalizedReadout_increasing, sectorInclusion_apply_label,
    coordinatesFromTensor_apply, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos N))

@[simp] lemma sectorReadout_inclusion {n k : ℕ} (x : ExteriorCoordinates n k) :
    sectorReadout n k (sectorInclusion n k x) = x := by
  ext A
  rw [sectorReadout_apply, sectorInclusion_apply_label]

lemma sectorInclusion_norm_sq {n k : ℕ} (x : ExteriorCoordinates n k) :
    ‖sectorInclusion n k x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    ← LinearMap.adjoint_inner_right, sectorInclusion_adjoint, sectorReadout_inclusion]

noncomputable def exteriorTensorIsometry (Q N : ℕ) :
    ExteriorCoordinates (Q+1) N ≃ₗᵢ[ℂ] SectorHilbert N Q where
  toFun x := ⟨normalizedReadout (Q+1) N (sectorInclusion (Q+1) N x), normalizedReadout_antisymmetric _⟩
  invFun ψ := coordinatesFromTensor Q N ψ.val
  left_inv x := coordinatesFromTensor_readout x
  right_inv ψ := Subtype.ext (readout_coordinatesFromTensor ψ.property)
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp
  norm_map' x := by
    change ‖normalizedReadout (Q+1) N (sectorInclusion (Q+1) N x)‖ = ‖x‖
    have he := normalizedReadout_norm_sq (sectorInclusion_homogeneous x)
    rw [sectorInclusion_norm_sq] at he
    nlinarith [norm_nonneg (normalizedReadout (Q+1) N (sectorInclusion (Q+1) N x)), norm_nonneg x]

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

noncomputable def exteriorHamiltonian (N Q : ℕ) :
    Module.End ℂ (ExteriorCoordinates (Q+1) N) :=
  sectorReadout (Q+1) N ∘ₗ physicalOccupationHamiltonian Q ∘ₗ sectorInclusion (Q+1) N

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpinWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Work. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Topology
open Filter

noncomputable def highestFactor (n m z k : ℕ) : ℝ :=
  ((m : ℝ) - z + k + 1) / ((n : ℝ) - k)

noncomputable def highestWeight (n m z p : ℕ) : ℝ :=
  (z.choose p : ℝ) * ∏ k ∈ Finset.range p, highestFactor n m z k

noncomputable def highestNormalization (n m z : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (z+1), highestWeight n m z p

noncomputable def highestCoefficient (n m z p : ℕ) : ℝ :=
  (-1 : ℝ) ^ (z-p) * Real.sqrt (highestWeight n m z p) /
    Real.sqrt (highestNormalization n m z)

noncomputable def firstLoweringCoefficient (n m z l p : ℕ) : ℝ :=
  Real.sqrt ((p : ℝ) * ((n : ℝ)-p+1)) /
    Real.sqrt (((l : ℝ)+1) * ((n : ℝ)+m-2*z-l))

noncomputable def secondLoweringCoefficient (n m z l p : ℕ) : ℝ :=
  Real.sqrt (((z : ℝ)+l-p+1) * ((m : ℝ)-z-l+p)) /
    Real.sqrt (((l : ℝ)+1) * ((n : ℝ)+m-2*z-l))

noncomputable def coupledCoefficient (n m z : ℕ) : ℕ → ℕ → ℝ
  | 0, p => highestCoefficient n m z p
  | l+1, p =>
      (if p = 0 then 0 else firstLoweringCoefficient n m z l p *
        coupledCoefficient n m z l (p-1)) +
      secondLoweringCoefficient n m z l p * coupledCoefficient n m z l p

open Polynomial

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_TensorSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def ladderStep (n : ℕ) (p : Fin n) : ℝ :=
  Real.sqrt (((p.val : ℝ)+1) * ((n : ℝ)-p.val))

noncomputable def lowering (n : ℕ) : Module.End ℝ (Fin (n+1) → ℝ) where
  toFun x := Fin.cases 0 (fun p => ladderStep n p * x p.castSucc)
  map_add' x y := by
    funext p
    cases p using Fin.cases <;> simp [mul_add]
  map_smul' r x := by
    funext p
    cases p using Fin.cases <;> simp [mul_left_comm]

noncomputable def weight (n : ℕ) : Module.End ℝ (Fin (n+1) → ℝ) where
  toFun x p := ((n : ℝ)-2*p.val) * x p
  map_add' x y := by funext p; simp [mul_add]
  map_smul' r x := by funext p; simp [mul_left_comm]

@[simp] lemma lowering_zero (n : ℕ) (x : Fin (n+1) → ℝ) : lowering n x 0 = 0 := rfl
@[simp] lemma lowering_succ (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin n) :
    lowering n x p.succ = ladderStep n p * x p.castSucc := rfl
@[simp] lemma weight_apply (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin (n+1)) :
    weight n x p = ((n : ℝ)-2*p.val) * x p := rfl

structure LadderSystem (ι : Type*) [Fintype ι] where
  lower : Module.End ℝ (ι → ℝ)
  raise : Module.End ℝ (ι → ℝ)
  weight : Module.End ℝ (ι → ℝ)
  adjoint : ∀ x y, dotProduct (lower x) y = dotProduct x (raise y)
  raise_lower : ∀ x, raise (lower x) = lower (raise x) + weight x
  weight_lower : ∀ x, weight (lower x) = lower (weight x) - (2 : ℝ) • lower x

namespace LadderSystem
variable {ι : Type*} [Fintype ι]

noncomputable def raw (S : LadderSystem ι) (x : ι → ℝ) (l : ℕ) : ι → ℝ :=
  (S.lower ^ l) x

@[simp] lemma raw_zero (S : LadderSystem ι) (x : ι → ℝ) : S.raw x 0 = x := rfl

end LadderSystem

noncomputable def onFirstEnd {ι κ : Type*} (A : Module.End ℝ (ι → ℝ)) :
    Module.End ℝ ((ι × κ) → ℝ) where
  toFun x pq := A (fun p => x (p, pq.2)) pq.1
  map_add' x y := by
    funext pq
    exact congrFun (A.map_add (fun p => x (p,pq.2)) (fun p => y (p,pq.2))) pq.1
  map_smul' r x := by
    funext pq
    exact congrFun (A.map_smul r (fun p => x (p,pq.2))) pq.1

noncomputable def onSecondEnd {ι κ : Type*} (A : Module.End ℝ (κ → ℝ)) :
    Module.End ℝ ((ι × κ) → ℝ) where
  toFun x pq := A (fun q => x (pq.1, q)) pq.2
  map_add' x y := by
    funext pq
    exact congrFun (A.map_add (fun q => x (pq.1,q)) (fun q => y (pq.1,q))) pq.2
  map_smul' r x := by
    funext pq
    exact congrFun (A.map_smul r (fun q => x (pq.1,q))) pq.2

@[simp] lemma onFirstEnd_apply {ι κ : Type*} (A : Module.End ℝ (ι → ℝ))
    (x : (ι × κ) → ℝ) (p : ι) (q : κ) :
    onFirstEnd A x (p,q) = A (fun i => x (i,q)) p := rfl

@[simp] lemma onSecondEnd_apply {ι κ : Type*} (A : Module.End ℝ (κ → ℝ))
    (x : (ι × κ) → ℝ) (p : ι) (q : κ) :
    onSecondEnd A x (p,q) = A (fun j => x (p,j)) q := rfl

noncomputable def highestTensor (n m z : ℕ) : (Fin (n+1) × Fin (m+1)) → ℝ :=
  fun pq => if pq.1.val + pq.2.val = z then highestCoefficient n m z pq.1.val else 0

noncomputable def coupledTensor (n m z l : ℕ) : (Fin (n+1) × Fin (m+1)) → ℝ :=
  fun pq => if pq.1.val + pq.2.val = z+l then coupledCoefficient n m z l pq.1.val else 0

@[simp] lemma coupledTensor_zero (n m z : ℕ) : coupledTensor n m z 0 = highestTensor n m z := by
  rfl

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_WedgeIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Wedge Identification. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

def orbitalDelta {n : ℕ} (i j : Fin n) : ℂ := if i=j then 1 else 0

end LaughlinGap.Occupation

namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct
open Occupation

noncomputable def spinPairForms (Q : ℕ) : Fin (2*Q-2+1) → PairLabel (Q+1) → ℂ := fun p a =>
  (sphericalExteriorPairCoefficient Q p.val a.val.1.val a.val.2.val : ℂ)

end LaughlinGap.Spin

namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct ComplexOrder
open Occupation

def physicalPairIndexEquiv {Q : ℕ} (hQ : 2 ≤ Q) :
    Fin (2*Q-1) ≃ Fin (2*Q-2+1) := finCongr (by omega)

def physicalThreeIndexEquiv {Q : ℕ} (hQ : 2 ≤ Q) :
    (Fin (2*Q-1) × Fin (Q+1)) ≃ (Fin (2*Q-2+1) × Fin (Q+1)) :=
  Equiv.prodCongr (physicalPairIndexEquiv hQ) (Equiv.refl _)

@[simp] lemma spinPairForms_physical_index {Q : ℕ} (hQ : 2 ≤ Q) (p : Fin (2*Q-1)) :
    spinPairForms Q (physicalPairIndexEquiv hQ p) = physicalPairForms Q p := rfl

@[simp] lemma spinTripleWedge_physical_index {Q : ℕ} (hQ : 2 ≤ Q)
    (a : BasisLabel (Q+1) 3) (p : Fin (2*Q-1) × Fin (Q+1)) :
    tripleWedgeMatrix (spinPairForms Q) a (physicalThreeIndexEquiv hQ p) =
      tripleWedgeMatrix (physicalPairForms Q) a p := rfl

noncomputable def physicalThreeVector {Q : ℕ} (hQ : 2 ≤ Q) (z l : ℕ) :
    (Fin (2*Q-1) × Fin (Q+1)) → ℂ := fun i =>
  (coupledTensor (2*Q-2) Q z l (physicalThreeIndexEquiv hQ i) : ℂ)

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PhysicalSpinSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Spin Spectrum. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct ComplexOrder
open Occupation

noncomputable def physicalThreeRankOne {Q : ℕ} (hQ : 2 ≤ Q) (z l : ℕ) :
    Matrix (Fin (2*Q-1) × Fin (Q+1)) (Fin (2*Q-1) × Fin (Q+1)) ℂ :=
  Matrix.vecMulVec (physicalThreeVector hQ z l) (star (physicalThreeVector hQ z l))

noncomputable def physicalThreeProjection {Q : ℕ} (hQ : 2 ≤ Q) (z : ℕ) :
    Matrix (Fin (2*Q-1) × Fin (Q+1)) (Fin (2*Q-1) × Fin (Q+1)) ℂ :=
  ∑ l : Fin ((2*Q-2)+Q-2*z+1), physicalThreeRankOne hQ z l.val

end LaughlinGap.Spin

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder
open Spin

noncomputable def physicalSpinThreeLift {Q : ℕ} (hQ : 2 ≤ Q) (z : ℕ) :
    Module.End ℂ (Hilbert (Q+1)) :=
  exteriorLift (tripleWedgeMatrix (physicalPairForms Q) * physicalThreeProjection hQ z *
    (tripleWedgeMatrix (physicalPairForms Q)).conjTranspose)

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ExtendedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extended Pair. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators ComplexOrder

noncomputable def endCongr {n m : ℕ} (h : n=m) :
    Module.End ℂ (Hilbert n) ≃ₐ[ℂ] Module.End ℂ (Hilbert m) := h ▸ AlgEquiv.refl

noncomputable def extendTo {n m : ℕ} (h : n ≤ m) :
    Module.End ℂ (Hilbert n) →ₐ[ℂ] Module.End ℂ (Hilbert m) :=
  (endCongr (Nat.add_sub_of_le h)).toAlgHom.comp (extendLocalHom n (m-n)).toAlgHom

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Exterior. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

def wordSign {n : ℕ} : List (Fin n) → ℚ
  | [] => 1
  | j :: js => if j ∈ js then 0 else
    (-1:ℚ)^(js.toFinset.filter (fun k => k < j)).card * wordSign js

end LaughlinGap.Occupation

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

abbrev FourTerm (D : ℕ) :=
  (Σ n : Fin (D+1), Fin ((n.val+1)/2) × Fin ((D-n.val+2)/2))

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ExteriorTermExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Term Expansion. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators

def pairLeft {n p : ℕ} (hp : p+1 < n) (i : Fin ((p+2)/2)) : Fin n :=
  ⟨i.val,by have := i.isLt; omega⟩
def pairRight {n p : ℕ} (hp : p+1 < n) (i : Fin ((p+2)/2)) : Fin n :=
  ⟨p+1-i.val,by omega⟩

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CheckedTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Checked Tables. -/

noncomputable section


namespace LaughlinGap.Arithmetic

def checkMatrix {n m : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → Fin m → α) : Bool :=
  (List.finRange n).all fun i => (List.finRange m).all fun j => decide (A i j = B i j)

end LaughlinGap.Arithmetic

namespace LaughlinGap.Arithmetic

def checkVector {n : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → α) : Bool :=
  (List.finRange n).all fun i => decide (A i = B i)

end LaughlinGap.Arithmetic

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate10

def keys : Fin 6 → Finset (Fin 25) := ![{0,1,2,8}, {0,1,3,7}, {0,1,4,6}, {0,2,3,6}, {0,2,4,5}, {1,2,3,5}]
def fibers : Fin 6 → Finset (FourTerm 10) := ![{⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}]
def columns : Matrix (Fin 5) (Fin 6) ℚ := ![![0, 0, 0, 0, 0, 0], ![-15120, 15120, -7560, -7560, 7560, 0], ![0, 0, 0, 0, 0, 0], ![11340, -11340, 5670, 5670, -5670, 0], ![-45360, 45360, -22680, -22680, 22680, 0]]
def Y : Matrix (Fin 5) (Fin 5) ℚ := ![![(200175459945085632193532343/6710886400000000000000), (-19934932341438578630554461/1677721600000000000000), (10688091490272052643120847/1342177280000000000000), (-25539656102181318071634093/3355443200000000000000), (20785777850578541715752031/838860800000000000000)], ![(-19934932341438578630554461/1677721600000000000000), (-23824125720222220870749/671088640000000000000), (-423999878564625416871237/335544320000000000000), (3981191132086811594405091/838860800000000000000), (-581783066891519285684403/41943040000000000000)], ![(10688091490272052643120847/1342177280000000000000), (-423999878564625416871237/335544320000000000000), (13103624809638522434317689/9395240960000000000000), (-2284683579713664648267057/671088640000000000000), (1918711872693053907602859/167772160000000000000)], ![(-25539656102181318071634093/3355443200000000000000), (3981191132086811594405091/838860800000000000000), (-2284683579713664648267057/671088640000000000000), (3925235702466226344344823/1677721600000000000000), (-1818861828136206279263793/419430400000000000000)], ![(20785777850578541715752031/838860800000000000000), (-581783066891519285684403/41943040000000000000), (1918711872693053907602859/167772160000000000000), (-1818861828136206279263793/419430400000000000000), (-7907022897840128737456029/104857600000000000000)]]
def Z : Matrix (Fin 5) (Fin 5) ℚ := ![![0, 0, 0, 0, 0], ![0, 30240, 0, -22680, 90720], ![0, 0, 0, 0, 0], ![0, -22680, 0, 17010, -68040], ![0, 90720, 0, -68040, 272160]]
def W : Matrix (Fin 5) (Fin 5) ℚ := ![![0, 0, 0, 0, 0], ![(-2093488721107348396109/36077725286400000000000000), (438867827883403177801057/1879048192000000000000000), (-1237433244599578471138079/4294967296000000000000000), (-474042061158101800190781/7516192768000000000000000), (1831244066560386205163291/22548578304000000000000000)], ![0, 0, 0, 0, 0], ![(2093488721107348396109/48103633715200000000000000), (-1316603483650209533403171/7516192768000000000000000), (3712299733798735413414237/17179869184000000000000000), (1422126183474305400572343/30064771072000000000000000), (-1831244066560386205163291/30064771072000000000000000)], ![(-2093488721107348396109/12025908428800000000000000), (1316603483650209533403171/1879048192000000000000000), (-3712299733798735413414237/4294967296000000000000000), (-1422126183474305400572343/7516192768000000000000000), (1831244066560386205163291/7516192768000000000000000)]]
def M : Matrix (Fin 5) (Fin 5) ℚ := ![![0, 0, 0, 0, 0], ![0, (425762667787958128783145313/26843545600000000000000), 0, (-1277288003363874386349435939/107374182400000000000000), (1277288003363874386349435939/26843545600000000000000)], ![0, 0, 0, 0, 0], ![0, (-1277288003363874386349435939/107374182400000000000000), 0, (3831864010091623159048307817/429496729600000000000000), (-3831864010091623159048307817/107374182400000000000000)], ![0, (1277288003363874386349435939/26843545600000000000000), 0, (-3831864010091623159048307817/107374182400000000000000), (3831864010091623159048307817/26843545600000000000000)]]
def L : Matrix (Fin 5) (Fin 5) ℚ := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, (-3/4), 0, 1, 0], ![0, 3, 0, 0, 1]]
def diag : Fin 5 → ℚ := ![0, (425762667787958128783145313/26843545600000000000000), 0, 0, 0]

def keyIndexTable : Fin 11 → Fin 13 → Fin 13 → Fin 6 := ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def keyIndex (n : Fin 11) (j : Fin ((n.val+1)/2)) (x : Fin ((10-n.val+2)/2)) : Fin 6 :=
  keyIndexTable n ⟨j.val,by have := j.isLt; have := n.isLt; omega⟩ ⟨x.val,by have := x.isLt; omega⟩
def representatives : Fin 6 → FourTerm 10 := ![⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩]
end Certificate10
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate11. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate11

def keys : Fin 9 → Finset (Fin 25) := ![{0,1,2,9}, {0,1,3,8}, {0,1,4,7}, {0,1,5,6}, {0,2,3,7}, {0,2,4,6}, {0,3,4,5}, {1,2,3,6}, {1,2,4,5}]
def fibers : Fin 9 → Finset (FourTerm 11) := ![{⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}]
def columns : Matrix (Fin 6) (Fin 9) ℚ := ![![226800, -226800, 340200, -340200, -113400, 0, 113400, 113400, -113400], ![90720, -90720, 75600, -75600, 15120, 0, -15120, -15120, 15120], ![28350, -28350, 4725, 16875, 23625, -21600, 19575, -2025, 2025], ![-62370, 62370, -25515, -4725, -36855, 30240, -23625, 6615, -6615], ![45360, -45360, -11340, 56700, 56700, -45360, 34020, -11340, 11340], ![1247400, -1247400, 1247400, -1247400, 0, 0, 0, 0, 0]]
def Y : Matrix (Fin 6) (Fin 6) ℚ := ![![(32839215004495137244466187/167772160000000000000), (-19588648001353140318042429/167772160000000000000), (769969819896078911998041/20971520000000000000), (-3060745927175333645962119/167772160000000000000), (1516286817957572396027451/20971520000000000000), (-19272986732194004208033657/20971520000000000000)], ![(-19588648001353140318042429/167772160000000000000), (24152328740360168247036519/838860800000000000000), (-2148675818210730931634253/167772160000000000000), (1994515423197492856394763/209715200000000000000), (8693018793801331618221/4194304000000000000), (-1927558817628006250840779/10485760000000000000)], ![(769969819896078911998041/20971520000000000000), (-2148675818210730931634253/167772160000000000000), (149319433910496770223741/46976204800000000000), (-342271579617331143233409/167772160000000000000), (65139956566813006253523/10485760000000000000), (2877018097116172834790361/20971520000000000000)], ![(-3060745927175333645962119/167772160000000000000), (1994515423197492856394763/209715200000000000000), (-342271579617331143233409/167772160000000000000), (-652126880335913571881601/104857600000000000000), (966055836873933781002981/104857600000000000000), (-511525534633041298988871/5242880000000000000)], ![(1516286817957572396027451/20971520000000000000), (8693018793801331618221/4194304000000000000), (65139956566813006253523/10485760000000000000), (966055836873933781002981/104857600000000000000), (-1172769771227963717819691/13107200000000000000), (521725615312896324070587/2621440000000000000)], ![(-19272986732194004208033657/20971520000000000000), (-1927558817628006250840779/10485760000000000000), (2877018097116172834790361/20971520000000000000), (-511525534633041298988871/5242880000000000000), (521725615312896324070587/2621440000000000000), (-1369918693771740518109957/131072000000000000)]]
def Z : Matrix (Fin 6) (Fin 6) ℚ := ![![7257600, 0, 0, 0, -453600, 9979200], ![0, 241920, 0, -60480, 0, 2494800], ![0, 0, 54000, -75600, 113400, 0], ![0, -60480, -75600, 120960, -158760, -623700], ![-453600, 0, 113400, -158760, 266490, -623700], ![9979200, 2494800, 0, -623700, -623700, 39449025]]
def W : Matrix (Fin 6) (Fin 6) ℚ := ![![(5964695117267475742980919/1503238553600000000000000), (1744624323817160701107537/1503238553600000000000000), (-161316238397235909250131/134217728000000000000000), (414064887714404869068081/751619276800000000000000), (-64800521002176063679207/187904819200000000000000), (15384382826163865762517/134217728000000000000000)], ![(512866081553008807390337/11274289152000000000000000), (-194897946662990208889687/3758096384000000000000000), (1871635346680482439661/50331648000000000000000), (-303975974406062929067597/5637144576000000000000000), (-19233547957227911298713/1409286144000000000000000), (9276944501934800833223/469762048000000000000000)], ![(-453817708231818879037087/36077725286400000000000000), (2031865538239284389204363/36077725286400000000000000), (-18408098023015419984551/375809638400000000000000), (-24170116272712712981741/721554505728000000000000), (98529294091720413115079/4509715660800000000000000), (-20089466216411214407027/4509715660800000000000000)], ![(1125259631410696923698261/180388626432000000000000000), (-11884283407719108217754297/180388626432000000000000000), (47737752682324330195009/805306368000000000000000), (5445674245348976488075063/90194313216000000000000000), (-204256955604377082203567/7516192768000000000000000), (29302929491660890850513/22548578304000000000000000)], ![(-8250049885990027717041051/30064771072000000000000000), (687492143573648402361607/15032385536000000000000000), (-59580937878949130564481/2147483648000000000000000), (-157502369657418727928627/1503238553600000000000000), (253426915913230802550397/3758096384000000000000000), (-4434231130321885021193/268435456000000000000000)], ![(8906646648378166256760477/1503238553600000000000000), (3189808830527522704705809/3006477107200000000000000), (-1362718846099888865026021/1073741824000000000000000), (302744511597940335001331/1503238553600000000000000), (-1444335560239755819933/2348810240000000000000), (678823330108464950298901/1879048192000000000000000)]]
def M : Matrix (Fin 6) (Fin 6) ℚ := ![![(5049552047366104719126260283/167772160000000000000), (8949117860231088857789367/16777216000000000000), (-39099590117542931979883869/268435456000000000000), (94714773618178746703399743/1342177280000000000000), (-1467660859958626572675955383/671088640000000000000), (7866011844464725027258136361/167772160000000000000)], ![(8949117860231088857789367/16777216000000000000), (1677004120298631639678687/41943040000000000000), (3044749629574206508033791/671088640000000000000), (-54853329812992078349810277/3355443200000000000000), (-39947051071179721194006141/1677721600000000000000), (38445358108099205386269927/33554432000000000000)], ![(-39099590117542931979883869/268435456000000000000), (3044749629574206508033791/671088640000000000000), (35550514566479531937111777/15032385536000000000000), (-47729513084776357969246941/10737418240000000000000), (75537373571788313927688669/5368709120000000000000), (-10300586047406982406675233/67108864000000000000)], ![(94714773618178746703399743/1342177280000000000000), (-54853329812992078349810277/3355443200000000000000), (-47729513084776357969246941/10737418240000000000000), (110703982169080563836793939/10737418240000000000000), (-368973410717799312717796119/26843545600000000000000), (-48018585876798273237896373/671088640000000000000)], ![(-1467660859958626572675955383/671088640000000000000), (-39947051071179721194006141/1677721600000000000000), (75537373571788313927688669/5368709120000000000000), (-368973410717799312717796119/26843545600000000000000), (2231147286200171863965309741/13421772800000000000000), (-8731261072446911549418855933/2684354560000000000000)], ![(7866011844464725027258136361/167772160000000000000), (38445358108099205386269927/33554432000000000000), (-10300586047406982406675233/67108864000000000000), (-48018585876798273237896373/671088640000000000000), (-8731261072446911549418855933/2684354560000000000000), (204769681017405795043351689717/2684354560000000000000)]]
def L : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![(1104829365460628254048070/62340148732914873075632843), 1, 0, 0, 0, 0], ![(-2413554945527341480239745/498721189863318984605062744), (4136195598756701681574722903125928982590421004929/17739236837277564358431182008444017483217516030648), 1, 0, 0, 0], ![(1169318192817021564239503/498721189863318984605062744), (-51127415237893867219062037832436524732154842072813/88696184186387821792155910042220087416087580153240), (-7/5), 1, 0, 0], ![(-18119269876032426823159943/249360594931659492302531372), (86860107573890735313069180965644508634398841103509/177392368372775643584311820084440174832175160306480), (21/10), 0, 1, 0], ![(97111257339070679348865881/62340148732914873075632843), (165/16), 0, 0, 0, 1]]
def diag : Fin 6 → ℚ := ![(5049552047366104719126260283/167772160000000000000), (19956641441937259903235079759499519668619705534479/653683837977649459501547839815680000000000000), (2458274422641393096494813566379712462387217062728478526502330063469129/10416525283295689221835547659184268682830082450037544058880000000000000), 0, 0, 0]

end Certificate11
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate12. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate12

def L : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, (4957658470759769563808575/11702752988909874665428494), 1, 0, 0, 0], ![0, (-4957658470759769563808575/15603670651879832887237992), (-3/4), 1, 0, 0], ![0, (-1/2), 0, 0, 1, 0], ![0, (10113092431876957268853470/1950458831484979110904749), (33/8), 0, 0, 1]]
end Certificate12
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate5. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate5

def L : Matrix (Fin 3) (Fin 3) ℚ := ![![1, 0, 0], ![(-1/2), 1, 0], ![(5/4), 0, 1]]
end Certificate5
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate6. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate6

def columns : Matrix (Fin 3) (Fin 1) ℚ := ![![0], ![0], ![0]]
def Z : Matrix (Fin 3) (Fin 3) ℚ := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]
end Certificate6
end LaughlinGap.RealOccupation

end

end OAI
end


