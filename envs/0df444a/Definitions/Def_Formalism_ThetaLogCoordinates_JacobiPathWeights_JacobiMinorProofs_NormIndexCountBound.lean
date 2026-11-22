-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:28:05.598038+00:00
-- url     : https://prove2.me/theorems/55471796-b84c-4c33-ad70-576f428fb672
-- title:
--   Norm Index Count Bound
-- statement:
--   Definitions and structural lemmas for Norm Index Count Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/NormIndexCountBound.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace Count
theorem antitone_of_step {n : ℕ} {f : Fin n → ℤ}
    (h : ∀ m m' : Fin n, m.val + 1 = m'.val → f m' ≤ f m) : Antitone f := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ hab
  change a ≤ b at hab
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k hak ih => intro hb; exact (h ⟨k, by omega⟩ ⟨k + 1, hb⟩ rfl).trans (ih (by omega))
theorem antitone_upper {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) : Antitone ν :=
  antitone_of_step fun m m' hm => (h.2.1 m m' hm).trans (h.1 m)
theorem antitone_lower {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) : Antitone μ :=
  antitone_of_step fun m m' hm => (h.1 m').trans (h.2.1 m m' hm)
def Step {n : ℕ} (v : Bool) (b : ℕ) (μ ν : Fin n → ℤ) : Prop :=
  if v then HStrip ν μ b else HStrip μ ν b
def succs {n : ℕ} (v : Bool) (b : ℕ) (μ : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  if v then stripsUp μ b else stripsDown μ b
theorem mem_succs (hS : StripsMem) {n : ℕ} (v : Bool) (b : ℕ) (μ ν : Fin n → ℤ) :
    ν ∈ succs v b μ ↔ Step v b μ ν := by
  unfold succs Step
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact (hS n μ ν b).2
  · simp only [↓reduceIte]; exact (hS n μ ν b).1
def baseEquiv (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ) :
    ContIdx n N N isVec B μ₀ ≃ {I : ℤ → Finset (Fin n) // IsStd μ₀ I} where
  toFun x := ⟨x.1.2, by
    have h := x.2.2.2.2
    rw [x.2.1] at h
    exact h⟩
  invFun I := ⟨(Function.update 0 N μ₀, I.1), by
    refine ⟨by simp, ?_, ?_, by simpa using I.2⟩
    · intro j hj
      have : j ≠ N := by omega
      simp [Function.update_of_ne this]
    · intro j h1 h2
      omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases hj : j = N
      · subst hj
        simpa using x.2.1.symm
      · have : j < N ∨ N < j := by omega
        simp [Function.update_of_ne hj, x.2.2.1 j this]
    · rfl
  right_inv I := rfl
def nextW (hS : StripsMem) {n i N : ℕ} (hi : i < N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ)
    (x : ContIdx n i N isVec B μ₀) : {ν // ν ∈ succs (isVec i) (B i) μ₀} :=
  ⟨x.1.1 (i + 1), by
    rw [mem_succs hS]
    have h := x.2.2.2.1 i le_rfl hi
    rw [x.2.1] at h
    exact h⟩
def fibreEquiv (hS : StripsMem) {n i N : ℕ} (hi : i < N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ)
    (ν : {ν // ν ∈ succs (isVec i) (B i) μ₀}) :
    {x : ContIdx n i N isVec B μ₀ // nextW hS hi isVec B μ₀ x = ν} ≃ ContIdx n (i + 1) N isVec B ν.1 where
  toFun x := ⟨(Function.update x.1.1.1 i 0, x.1.1.2), by
    have hν : x.1.1.1 (i + 1) = ν.1 := congrArg Subtype.val x.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Function.update_of_ne (show i + 1 ≠ i by omega)] using hν
    · intro j hj
      by_cases hji : j = i
      · subst hji; simp
      · simpa [Function.update_of_ne hji] using x.1.2.2.1 j (by omega)
    · intro j h1 h2
      have e1 : j ≠ i := by omega
      have e2 : j + 1 ≠ i := by omega
      simpa [Function.update_of_ne e1, Function.update_of_ne e2] using x.1.2.2.2.1 j (by omega) h2
    · have e1 : N ≠ i := by omega
      simpa [Function.update_of_ne e1] using x.1.2.2.2.2⟩
  invFun y := ⟨⟨(Function.update y.1.1 i μ₀, y.1.2), by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro j hj
      have e1 : j ≠ i := by omega
      simpa [Function.update_of_ne e1] using y.2.2.1 j (by omega)
    · intro j h1 h2
      by_cases hji : j = i
      · subst hji
        have e2 : j + 1 ≠ j := by omega
        have h := (mem_succs hS _ _ _ _).1 ν.2
        simpa [Function.update_of_ne e2, y.2.1, Step] using h
      · have e2 : j + 1 ≠ i := by omega
        simpa [Function.update_of_ne hji, Function.update_of_ne e2] using y.2.2.2.1 j (by omega) h2
    · have e1 : N ≠ i := by omega
      simpa [Function.update_of_ne e1] using y.2.2.2.2⟩, by
    apply Subtype.ext
    have e2 : i + 1 ≠ i := by omega
    simpa [nextW, Function.update_of_ne e2] using y.2.1⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases hji : j = i
      · subst hji
        simpa using x.1.2.1.symm
      · simp [Function.update_of_ne hji]
    · rfl
  right_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases hji : j = i
      · subst hji
        simpa using (y.2.2.1 j (by omega)).symm
      · simp [Function.update_of_ne hji]
    · rfl
theorem antitone_of_rules {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ} (h0 : Antitone (μ 0))
    (h : ∀ j < N, if isVec j then HStrip (μ (j + 1)) (μ j) (B j) else HStrip (μ j) (μ (j + 1)) (B j)) :
    ∀ i ≤ N, Antitone (μ i) := by
  intro i hi
  cases i with
  | zero => exact h0
  | succ j =>
    have hj := h j (by omega)
    split_ifs at hj
    · exact antitone_upper hj
    · exact antitone_lower hj
def pathEquiv (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) : PathIdx n N isVec B ≃ ContIdx n 0 N isVec B 0 :=
  Equiv.subtypeEquivRight fun x => by
    constructor
    · rintro ⟨⟨h0, _, h2⟩, h3, h4⟩
      exact ⟨h0, fun j hj => h3 j (by omega), fun j _ hj => h2 j hj, h4⟩
    · rintro ⟨h0, h1, h2, h3⟩
      have h2' : ∀ j < N, if isVec j then HStrip (x.1 (j + 1)) (x.1 j) (B j)
          else HStrip (x.1 j) (x.1 (j + 1)) (B j) := fun j hj => h2 j (Nat.zero_le _) hj
      refine ⟨⟨h0, antitone_of_rules (by rw [h0]; exact fun _ _ _ => le_rfl) h2', h2'⟩,
        fun j hj => h1 j (Or.inr hj), h3⟩
end Count
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


