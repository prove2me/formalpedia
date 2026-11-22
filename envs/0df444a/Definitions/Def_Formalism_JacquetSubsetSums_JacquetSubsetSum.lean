-- Prove2me | Definitions.Def_Formalism_JacquetSubsetSums_JacquetSubsetSum
-- name    : Formalism_JacquetSubsetSums_JacquetSubsetSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:23.952369+00:00
-- url     : https://prove2.me/theorems/3bfda710-7286-47e9-89d4-935239eafa33
-- title:
--   Jacquet Subset Sum
-- statement:
--   Definitions and structural lemmas for Jacquet Subset Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/JacquetSubsetSums/JacquetSubsetSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.PacketSums
def NoFixedSum : Prop :=
  ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ G V) (N : Subgroup G) [Fintype N],
    (∀ v : V, (∀ n ∈ N, τ n v = v) → v = 0) →
    ∀ x y : G, ∑ n : N, LinearMap.trace ℂ V (τ (x * (n : G) * y)) = 0
def GoodImpliesH : Prop :=
  ∀ (r : ℕ) (S : Type) (c : S → Type) [∀ v, Fintype (c v)] (d : ∀ v, c v → ℕ),
    (∀ v, ∑ i, d v i = r) →
    (∀ a : ℕ, 1 ≤ a → 2 * a ≤ r → ∃ v, ∀ J : Finset (c v), ∑ i ∈ J, d v i ≠ a) →
    ∀ a : ℕ, 0 < a → a < r → ∃ v, ∀ J : Finset (c v), ∑ i ∈ J, d v i ≠ a
def JacquetSubsetSum : Prop :=
  ∀ (k : Type) [Field k] (r s : ℕ) (b : Fin r → Fin s), Monotone b →
    ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (ρ : GL (Fin r) k → Y →ₗ[ℂ] Y),
    (∀ S : Finset (Fin r), (∃ i j, b i = b j ∧ i ∈ S ∧ j ∉ S) →
      ∀ y : Y, (∀ u : GL (Fin r) k,
        (∀ i j, (u : Matrix (Fin r) (Fin r) k) i j ≠ (1 : Matrix (Fin r) (Fin r) k) i j →
          b i = b j ∧ i ∈ S ∧ j ∉ S) → ρ u y = y) → y = 0) →
    ∀ (a : ℕ), a ≤ r → ∀ (φ : GL (Fin r) k → Y),
    (∀ q x : GL (Fin r) k, (∀ i j, b j < b i → (q : Matrix (Fin r) (Fin r) k) i j = 0) →
      φ (q * x) = ρ q (φ x)) →
    (∀ x n : GL (Fin r) k,
      (∀ i j, (n : Matrix (Fin r) (Fin r) k) i j ≠ (1 : Matrix (Fin r) (Fin r) k) i j →
        (i : ℕ) < a ∧ a ≤ (j : ℕ)) → φ (x * n) = φ x) →
    φ ≠ 0 → ∃ J : Finset (Fin s), a = ∑ c ∈ J, (Finset.univ.filter fun i => b i = c).card
def IwahoriNewton : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (ϖ : O), ϖ ∈ IsLocalRing.maximalIdeal O →
    ∀ (r : ℕ) (a : Fin r → ℕ), StrictAnti a →
    ∀ i₁ i₂ : Matrix (Fin r) (Fin r) O,
    (∀ i, IsUnit (i₁ i i)) → (∀ i, IsUnit (i₂ i i)) →
    (∀ i j, j < i → ϖ ∣ i₁ i j) → (∀ i j, j < i → ϖ ∣ i₂ i j) →
    ∀ k : ℕ, k ≤ r → ∃ u : Oˣ,
      (i₁ * Matrix.diagonal (fun i => ϖ ^ a i) * i₂).charpoly.coeff (r - k) =
        (u : O) * ϖ ^ (∑ j ∈ Finset.univ.filter (fun j : Fin r => r - k ≤ (j : ℕ)), a j)
def numK {r : ℕ} (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK] (μ : Fin r → ℤ)
    (β : Fin r → ℂ) : ℂ :=
  ∑ w : WK, ((Equiv.Perm.sign (w : Equiv.Perm (Fin r)) : ℤ) : ℂ) *
    ∏ i, β i ^ μ ((w : Equiv.Perm (Fin r))⁻¹ i)
def vdm {r : ℕ} (β : Fin r → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), (β i - β j)
def PacketSum : Prop :=
  ∀ (r : ℕ) (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK] (T : Finset (Equiv.Perm (Fin r))),
    Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin r)))⁻¹ * (p.1 : Equiv.Perm (Fin r))) →
    ∀ (μ : Fin r → ℤ) (α : Fin r → ℂ), (∀ i, α i ≠ 0) → Function.Injective α →
      ∑ y ∈ T, numK WK μ (fun i => α (y⁻¹ i)) / vdm (fun i => α (y⁻¹ i)) =
        (∑ w : Equiv.Perm (Fin r), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, α i ^ μ (w⁻¹ i)) / vdm α
def SignEven : Prop :=
  ∀ p q : ℕ, Odd (p + q) → (-1 : ℤ) ^ (p * q) = 1
def ConeCharIndep : Prop :=
  ∀ (r : ℕ) (c : (Multiplicative (Fin r → ℤ) →* ℂ) →₀ ℂ),
    (∀ a : Fin r → ℤ, StrictAnti a →
      (c.sum fun χ z => z * χ (Multiplicative.ofAdd a)) = 0) → c = 0
def SimpleCharIndep : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι : Type) [Finite ι] (W : ι → Type)
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, Module A (W i)]
    [∀ i, IsScalarTower ℂ A (W i)] [∀ i, FiniteDimensional ℂ (W i)],
    (∀ i, IsSimpleModule A (W i)) → (∀ i j, Nonempty (W i ≃ₗ[A] W j) → i = j) →
    LinearIndependent ℂ
      (fun i => fun h : A => LinearMap.trace ℂ (W i) (Algebra.lsmul ℂ ℂ (W i) h))
end Formalism.PacketSums


