-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
-- name    : Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:49:50.57857+00:00
-- url     : https://prove2.me/theorems/10d672ec-13f5-43d6-9163-bd4d0d8a31fd
-- title:
--   Log Vandermonde Variation Unbounded
-- statement:
--   Definitions and structural lemmas for Log Vandermonde Variation Unbounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeVariationUnbounded.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.StandardLattice
open Finset
def BlockDimensionIdentities : Prop :=
  ∀ (k m rS r : ℕ), 2 ≤ m → Even m → rS = m / 2 - 1 → r = k + 1 + 2 * rS →
    let blockOf : ℕ → ℕ := fun i => if i < rS then i else if i < rS + k + 1 then rS else i - k
    let dimN : ℕ := ((range r ×ˢ range r).filter
      (fun p : ℕ × ℕ => p.1 < p.2 ∧ blockOf p.1 ≠ blockOf p.2)).card
    (r : ℤ) = k + m - 1 ∧
    2 * (dimN : ℤ) = (r : ℤ) ^ 2 - ((k : ℤ) + 1) ^ 2 - 2 * rS ∧
    2 * ((r : ℤ) ^ 2 - dimN) - (k : ℤ) * (k - 1) = (r : ℤ) ^ 2 + 3 * k + 1 + 2 * rS ∧
    2 * (k : ℤ) ^ 2 - (k : ℤ) * (k - 1) = (k : ℤ) * (k + 1) ∧
    ((r : ℤ) ^ 2 + 3 * k + 1 + 2 * rS) - (k : ℤ) * (k + 1) = (m : ℤ) * (2 * k + m - 1)
def CardGeneralLinear : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ),
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * (n - 1) / 2) * (Fintype.card F : ℝ) ^ (n * (n + 1) / 2) *
        ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1))
def CardUnitriangular : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ),
    Nat.card {A : Matrix (Fin n) (Fin n) F // (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1} =
      Fintype.card F ^ (n * (n - 1) / 2)
def EulerProductBounds : Prop :=
  ∀ (q : ℝ), 3 ≤ q → ∀ n : ℕ,
    1 / 2 ≤ ∏ i ∈ range n, (1 - q⁻¹ ^ (i + 1)) ∧ ∏ i ∈ range n, (1 - q⁻¹ ^ (i + 1)) ≤ 1
def CardStabilizerVector : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (v : Fin n → F), v ≠ 0 →
    Fintype.card {A : GL (Fin n) F // Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v} *
      (Fintype.card F ^ n - 1) = Fintype.card (GL (Fin n) F)
def PrimeOrderFinrank : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n g : ℕ) (A : Matrix (Fin n) (Fin n) K),
    g.Prime → A ^ g = 1 → A ≠ 1 → g - 1 ≤ Module.finrank ℚ K * n
def PrimePowerSubgroupTrivial : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n g : ℕ) (Γ : Subgroup (GL (Fin n) K)),
    g.Prime → Finite Γ → (∃ e : ℕ, Nat.card Γ = g ^ e) → Module.finrank ℚ K * n < g - 1 → Γ = ⊥
noncomputable def vandLog {N : ℕ} (u : Fin N → ℝ) : ℝ :=
  ∑ a, ∑ b ∈ univ.filter (fun b => a < b), Real.log (u a - u b)
def WordPair (n : ℕ) (Δ : ℝ) (u u' : Fin (n + 2) → ℝ) : Prop :=
  0 < Δ ∧
  (∀ a b, a < b → 1 ≤ u a - u b) ∧ (∀ a b, a < b → 1 ≤ u' a - u' b) ∧
  (∀ i, |u i - u' i| ≤ Δ) ∧ u 0 = u' 0 ∧ u (Fin.last (n + 1)) = u' (Fin.last (n + 1)) ∧
  (∀ i j : Fin (n + 2), 1 ≤ i.val → j.val = i.val + 1 → j.val ≤ n →
    3 * Δ ≤ u i - u j ∧ 3 * Δ ≤ u' i - u' j)
def LogVandermondeVariation : Prop :=
  ∀ (n : ℕ) (Δ : ℝ) (u u' : Fin (n + 2) → ℝ), WordPair n Δ u u' →
    |vandLog u - vandLog u'| ≤ 6 * (n + 2) * (1 + Real.log (n + 2)) + 2 * Real.log (1 + Δ)
def LogVandermondeVariationOfLogLe : Prop :=
  ∀ (n : ℕ) (Δ : ℝ) (u u' : Fin (n + 2) → ℝ), WordPair n Δ u u' → Real.log (1 + Δ) ≤ n + 2 →
    |vandLog u - vandLog u'| ≤ 8 * (n + 2) * (1 + Real.log (n + 2))
def LogVandermondeVariationUnbounded : Prop :=
  ∀ M : ℝ, ∃ (Δ : ℝ) (u u' : Fin 4 → ℝ), 1 ≤ Δ ∧ WordPair 2 Δ u u' ∧ M ≤ |vandLog u - vandLog u'|
def CardBilinearLevel : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (M : ℕ) (β : F), 1 ≤ M → β ≠ 0 →
    Fintype.card {p : (Fin M → F) × (Fin M → F) // ∑ i, p.1 i * p.2 i = β} =
      Fintype.card F ^ (M - 1) * (Fintype.card F ^ M - 1)
def CardHermitianLevel : Prop :=
  ∀ (L : Type) [Field L] [Fintype L] [DecidableEq L] (q M : ℕ) (β : L),
    Fintype.card L = q ^ 2 → 1 ≤ M → β ≠ 0 → β ^ q = β →
    (Fintype.card {x : Fin M → L // ∑ i, x i ^ (q + 1) = β} : ℤ) =
      (q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M)
def VandermondeAppendNeg : Prop :=
  ∀ (R : Type) [CommRing R] (a m : ℕ) (v : Fin a → R) (b : Fin m → R),
    (∏ i, ∏ j ∈ univ.filter (fun j => i < j),
        ((Fin.append v (fun j => - b j) : Fin (a + m) → R) i -
          (Fin.append v (fun j => - b j) : Fin (a + m) → R) j)) =
      (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (v i - v j)) *
      (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (b j - b i)) *
      ∏ i, ∏ j, (v i + b j)
def ProdFactorialShift : Prop :=
  ∀ k r : ℕ, k ≤ r →
    (∏ M ∈ Ico (k + 1) (r + 1), (M - 1).factorial) * ∏ i ∈ range k, i.factorial =
      ∏ i ∈ range r, i.factorial
end Formalism.LogVandermondeBounds.StandardLattice


