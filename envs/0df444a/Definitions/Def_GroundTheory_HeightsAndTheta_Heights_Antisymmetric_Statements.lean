-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:52.54388+00:00
-- url     : https://prove2.me/theorems/1bbfbd36-f0ad-4689-9bda-c78a11aca73e
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/Statements.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
section Objects
variable (T : Type*) [Fintype T] [DecidableEq T] (N : ℕ)
def antisymWeyl (j : ℕ) : Subgroup (Equiv.Perm (T × Fin N)) where
  carrier := {σ | ∀ p, (σ p).1 = p.1 ∧ ((σ p).2.val < j ↔ p.2.val < j)}
  one_mem' := by intro p; simp
  mul_mem' := by
    intro σ ρ hσ hρ p
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    exact ⟨(hσ (ρ p)).1.trans (hρ p).1, (hσ (ρ p)).2.trans (hρ p).2⟩
  inv_mem' := by
    intro σ hσ p
    have h := hσ (σ⁻¹ p)
    have e : σ (σ⁻¹ p) = p := by simp
    rw [e] at h
    exact ⟨h.1.symm, h.2.symm⟩
def IsBlockSimpleSwap (j : ℕ) (σ : Equiv.Perm (T × Fin N)) : Prop :=
  ∃ (τ : T) (a b : Fin N), b.val = a.val + 1 ∧ (b.val < j ∨ j ≤ a.val) ∧
    σ = Equiv.swap (τ, a) (τ, b)
def antisymDelta : MvPolynomial (T × Fin N) ℝ :=
  ∏ τ : T, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b))
def antisymDegree : ℕ := Fintype.card T * N.choose 2
def antisymSpace (j : ℕ) : Submodule ℝ (MvPolynomial (T × Fin N) ℝ) where
  carrier := {P | P ∈ homogeneousSubmodule (T × Fin N) ℝ (antisymDegree T N + 1) ∧
    ∀ σ, IsBlockSimpleSwap T N j σ → rename σ P = -P}
  zero_mem' := ⟨Submodule.zero_mem _, fun σ _ => by simp⟩
  add_mem' := by
    rintro P Q ⟨hP, hP'⟩ ⟨hQ, hQ'⟩
    refine ⟨Submodule.add_mem _ hP hQ, fun σ hσ => ?_⟩
    rw [map_add, hP' σ hσ, hQ' σ hσ, neg_add]
  smul_mem' := by
    rintro c P ⟨hP, hP'⟩
    refine ⟨Submodule.smul_mem _ c hP, fun σ hσ => ?_⟩
    rw [map_smul, hP' σ hσ, smul_neg]
def antisymInv (j : ℕ) : Submodule ℝ (MvPolynomial (T × Fin N) ℝ) where
  carrier := {l | l ∈ homogeneousSubmodule (T × Fin N) ℝ 1 ∧
    ∀ σ ∈ antisymWeyl T N j, rename σ l = l}
  zero_mem' := ⟨Submodule.zero_mem _, fun σ _ => by simp⟩
  add_mem' := by
    rintro P Q ⟨hP, hP'⟩ ⟨hQ, hQ'⟩
    refine ⟨Submodule.add_mem _ hP hQ, fun σ hσ => ?_⟩
    rw [map_add, hP' σ hσ, hQ' σ hσ]
  smul_mem' := by
    rintro c P ⟨hP, hP'⟩
    refine ⟨Submodule.smul_mem _ c hP, fun σ hσ => ?_⟩
    rw [map_smul, hP' σ hσ]
def diagHyperplane (τ : T) (a b : Fin N) : Set (T × Fin N → ℝ) :=
  {x | x (τ, a) = x (τ, b)}
end Objects
def AntisymDivisible.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (P : MvPolynomial (T × Fin N) ℝ), P ∈ antisymSpace T N j →
    (∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val →
      ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
        ∀ x ∈ O ∩ diagHyperplane T N τ a b, eval x P = 0) →
    ∃ l ∈ antisymInv T N j, P = antisymDelta T N * l
def AntisymStability.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Om : T → Fin N → Fin N → Set (T × Fin N → ℝ)),
    (∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val →
      IsCompact (Om τ a b) ∧ Om τ a b ⊆ diagHyperplane T N τ a b ∧
      ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
        O ∩ diagHyperplane T N τ a b ⊆ Om τ a b) →
    ∃ C : ℝ, ∀ P ∈ antisymSpace T N j, ∃ l ∈ antisymInv T N j,
      ∀ M : ℝ, 0 ≤ M →
        (∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val → ∀ x ∈ Om τ a b, |eval x P| ≤ M) →
        ∀ m, |coeff m (P - antisymDelta T N * l)| ≤ C * M
def AntisymPerturbation.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (hj : 0 < j) (hjN : j < N) (h : MvPolynomial (T × Fin N) ℝ)
    (Kτ : T → Set (T × Fin N → ℝ)),
    (∀ τ : T, IsCompact (Kτ τ) ∧
      Kτ τ ⊆ diagHyperplane T N τ ⟨j - 1, by omega⟩ ⟨j, hjN⟩ ∧
      (∃ O : Set (T × Fin N → ℝ), IsOpen O ∧
        (O ∩ diagHyperplane T N τ ⟨j - 1, by omega⟩ ⟨j, hjN⟩).Nonempty ∧
        O ∩ diagHyperplane T N τ ⟨j - 1, by omega⟩ ⟨j, hjN⟩ ⊆ Kτ τ) ∧
      ∀ x ∈ Kτ τ, eval x h = 0) →
    ∃ C : ℝ, ∀ (P : MvPolynomial (T × Fin N) ℝ) (v ε : ℝ), P - v • h ∈ antisymSpace T N j →
      (∀ τ : T, ∀ x ∈ Kτ τ, |eval x P| ≤ ε) →
      ∃ l ∈ antisymInv T N j, ∀ m, |coeff m (P - v • h - antisymDelta T N * l)| ≤ C * ε
section Inhabitants
def antisymSample : MvPolynomial (Fin 1 × Fin 3) ℝ :=
  antisymDelta (Fin 1) 3 * ∑ p : Fin 1 × Fin 3, X p
end Inhabitants
end GroundTheory.Heights₂.Heights


