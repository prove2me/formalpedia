-- Prove2me | Definitions.Def_QuantumGroupCodes836_Addressability_Linear
-- name    : QuantumGroupCodes836_Addressability_Linear
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T17:06:51.821095+00:00
-- url     : https://prove2.me/theorems/bd8bc958-56e1-4640-9406-2c4caf772aab
-- title:
--   Finite-field codes, weighted Schur powers and coordinate operations
-- statement:
--   For a field $F$ and a finite coordinate set $I$, a linear code is an actual subspace $C\subseteq F^I$. Hamming weight counts nonzero coordinates, and the dual uses the field-valued Euclidean pairing. For an integer $a$, the Schur power is the span of coordinatewise $a$-fold products; the published Schur-square definition is reused at $a=2$.
--
--   $$u\star C^{\star a}\subseteq C^\perp,\qquad u_i\ne0.$$
--
--   Puncturing restricts words to the complement of the deleted set. Shortening first requires zero on the deleted set, then restricts. Group actions are specified faithful free permutation actions preserving the same code. Empty weight minima are infinite. These objects are shared by the classical and quantum results.
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), §§2.1.1–2.1.3, pp.4–6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Mathlib
import Definitions.Def_TwoFoldOPI_schurSquare

set_option autoImplicit false
noncomputable section

namespace QuantumGroupCodes836.Addressability

abbrev Code (F : Type*) [Field F] (I : Type*) := Submodule F (I → F)

def weight {F I : Type*} [Field F] [Fintype I] (v : I → F) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => v i ≠ 0).card

def dual {F I : Type*} [Field F] [Fintype I] (C : Code F I) : Code F I where
  carrier := {v | ∀ c ∈ C, ∑ i, v i * c i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw c hc
    simpa [add_mul, Finset.sum_add_distrib, hv c hc, hw c hc]
  smul_mem' := by
    intro a v hv c hc
    simpa [mul_assoc, ← Finset.mul_sum, hv c hc]

/-- Infinity, rather than zero, is the distance of the zero code. -/
def distance {F I : Type*} [Field F] [Fintype I] (C : Code F I) : ℕ∞ :=
  ⨅ (c : C) (_ : c ≠ 0), (weight (c : I → F) : ℕ∞)

def schurPower {F : Type*} [Field F] {n : ℕ} (C : Code F (Fin n)) (m : ℕ) :
    Code F (Fin n) :=
  if m = 2 then TwoFoldOPI.schurSquare C else
  Submodule.span F {v | ∃ c : Fin m → C, v = fun j => ∏ a, (c a : Fin n → F) j}

def MultiplicationWith {F : Type*} [Field F] {n : ℕ}
    (C : Code F (Fin n)) (m : ℕ) (u : Fin n → F) : Prop :=
  (∀ j, u j ≠ 0) ∧ ∀ v ∈ schurPower C m, (fun j => u j * v j) ∈ dual C

def Multiplication {F : Type*} [Field F] {n : ℕ} (C : Code F (Fin n)) (m : ℕ) : Prop :=
  ∃ u, MultiplicationWith C m u

def restrictLinear {F I : Type*} [Field F] (L : Set I) : (I → F) →ₗ[F] (L → F) where
  toFun v i := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def puncture {F I : Type*} [Field F] (C : Code F I) (L : Set I) : Code F {i : I // i ∉ L} :=
  C.map (restrictLinear Lᶜ)

def shorten {F I : Type*} [Field F] (C : Code F I) (L : Set I) : Code F {i : I // i ∉ L} :=
  (C ⊓ LinearMap.ker (restrictLinear L)).map (restrictLinear Lᶜ)

def permute {F I : Type*} [Field F] (σ : Equiv.Perm I) : (I → F) ≃ₗ[F] (I → F) where
  toFun v i := v (σ.symm i)
  invFun v i := v (σ i)
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

structure CodeAction (F I G : Type*) [Field F] [Group G] (C : Code F I) where
  coordinates : G →* Equiv.Perm I
  faithful : Function.Injective coordinates
  free : ∀ g i, coordinates g i = i → g = 1
  preserves : ∀ g c, c ∈ C → permute (coordinates g) c ∈ C

def Orbit {F I G : Type*} [Field F] [Group G] {C : Code F I}
    (A : CodeAction F I G C) (i : I) : Set I := {j | ∃ g, A.coordinates g i = j}

end QuantumGroupCodes836.Addressability


