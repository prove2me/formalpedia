-- Prove2me | Definitions.Def_Formalism_LatticeRigidity_StatementA
-- name    : Formalism_LatticeRigidity_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:07:47.13857+00:00
-- url     : https://prove2.me/theorems/b6556ed4-be9b-47d1-ab80-eeb45c7e1e31
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/StatementA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SA.A
open Matrix
variable {O K : Type} [CommRing O] [CommRing K] [Algebra O K]
def e (R : Type) [CommRing R] (n : ℕ) : Fin (n+1) → R := Pi.single (Fin.last n) 1
def IsInt (O : Type) {K : Type} [CommRing O] [CommRing K] [Algebra O K] {ι : Type}
    (v : ι → K) : Prop :=
  ∀ i, v i ∈ Set.range (algebraMap O K)
abbrev toK {n : ℕ} (Z : Matrix (Fin (n+1)) (Fin (n+1)) O) : Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Z.map (algebraMap O K)
noncomputable def kap (K : Type) [CommRing K] [Algebra O K] {n : ℕ}
    (Z : Matrix (Fin (n+1)) (Fin (n+1)) O) : K :=
  (toK (K := K) Z)⁻¹ (Fin.last n) (Fin.last n)
noncomputable def yp (K : Type) [CommRing K] [Algebra O K] {n : ℕ}
    (g Z₁ : Matrix (Fin (n+1)) (Fin (n+1)) O) : Fin (n+1) → K :=
  (toK (K := K) Z₁)⁻¹ *ᵥ ((toK (K := K) g)⁻¹ *ᵥ e K n - e K n)
noncomputable def xp (K : Type) [CommRing K] [Algebra O K] {n : ℕ}
    (g' Z₁ : Matrix (Fin (n+1)) (Fin (n+1)) O) : Fin (n+1) → K :=
  (e K n ᵥ* toK (K := K) g' - e K n) ᵥ* (toK (K := K) Z₁)⁻¹
def LL (K : Type) [CommRing K] [Algebra O K] {n : ℕ} (Z₁ Z₂ : Matrix (Fin (n+1)) (Fin (n+1)) O) :
    Set (Matrix (Fin (n+1)) (Fin (n+1)) O × Matrix (Fin (n+1)) (Fin (n+1)) O) :=
  {p | IsUnit p.1 ∧ IsUnit p.2 ∧ p.1 * Z₁ = Z₂ * p.2 ∧
    IsInt O (yp K p.1 Z₁) ∧ IsInt O (xp K p.2 Z₁)}
def LL' (K : Type) [CommRing K] [Algebra O K] {n : ℕ} (Z₁ Z₂ : Matrix (Fin (n+1)) (Fin (n+1)) O) :
    Set (Matrix (Fin (n+1)) (Fin (n+1)) O × Matrix (Fin (n+1)) (Fin (n+1)) O) :=
  {p | p ∈ LL K Z₁ Z₂ ∧ p.1 *ᵥ e O n = e O n ∧ e O n ᵥ* p.2 = e O n}
def KK {n : ℕ} (Z₁ : Matrix (Fin (n+1)) (Fin (n+1)) O) : Set (Matrix (Fin (n+1)) (Fin (n+1)) O) :=
  {M | IsUnit (1 + Z₁ * M)}
def kmul {n : ℕ} (Z₁ M M' : Matrix (Fin (n+1)) (Fin (n+1)) O) : Matrix (Fin (n+1)) (Fin (n+1)) O :=
  M + M' + M * Z₁ * M'
def act {n : ℕ} (Z₁ : Matrix (Fin (n+1)) (Fin (n+1)) O)
    (p : Matrix (Fin (n+1)) (Fin (n+1)) O × Matrix (Fin (n+1)) (Fin (n+1)) O)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) O) :
    Matrix (Fin (n+1)) (Fin (n+1)) O × Matrix (Fin (n+1)) (Fin (n+1)) O :=
  (p.1 * (1 + Z₁ * M), p.2 * (1 + M * Z₁))
def KapDiff : Prop :=
  ∀ (O K : Type) [CommRing O] [CommRing K] [Algebra O K], Function.Injective (algebraMap O K) →
  ∀ (n : ℕ) (Z₁ Z₂ g g' : Matrix (Fin (n+1)) (Fin (n+1)) O),
    IsUnit (toK (K := K) Z₁) → IsUnit (toK (K := K) Z₂) → (g, g') ∈ LL K Z₁ Z₂ →
    kap K Z₂ - kap K Z₁ =
        yp K g Z₁ (Fin.last n) + xp K g' Z₁ (Fin.last n) +
          xp K g' Z₁ ⬝ᵥ (toK (K := K) Z₁ *ᵥ yp K g Z₁) ∧
      kap K Z₂ - kap K Z₁ ∈ Set.range (algebraMap O K)
def KKGroup : Prop :=
  ∀ (O : Type) [CommRing O] (n : ℕ) (Z₁ : Matrix (Fin (n+1)) (Fin (n+1)) O),
    (0 : Matrix (Fin (n+1)) (Fin (n+1)) O) ∈ KK Z₁ ∧
    (∀ M M', 1 + Z₁ * kmul Z₁ M M' = (1 + Z₁ * M) * (1 + Z₁ * M')) ∧
    (∀ M M', M ∈ KK Z₁ → M' ∈ KK Z₁ → kmul Z₁ M M' ∈ KK Z₁) ∧
    (∀ M M' M'', kmul Z₁ (kmul Z₁ M M') M'' = kmul Z₁ M (kmul Z₁ M' M'')) ∧
    (∀ M, kmul Z₁ 0 M = M ∧ kmul Z₁ M 0 = M) ∧
    (∀ M ∈ KK Z₁, ∃ M' ∈ KK Z₁, kmul Z₁ M M' = 0 ∧ kmul Z₁ M' M = 0)
def KKAction : Prop :=
  ∀ (O K : Type) [CommRing O] [CommRing K] [Algebra O K], Function.Injective (algebraMap O K) →
  ∀ (n : ℕ) (Z₁ Z₂ : Matrix (Fin (n+1)) (Fin (n+1)) O),
    IsUnit (toK (K := K) Z₁) → IsUnit (toK (K := K) Z₂) →
    (∀ p ∈ LL K Z₁ Z₂, ∀ M ∈ KK Z₁, act Z₁ p M ∈ LL K Z₁ Z₂) ∧
    (∀ p, act Z₁ p 0 = p) ∧
    (∀ p M M', act Z₁ (act Z₁ p M) M' = act Z₁ p (kmul Z₁ M M'))
def LLCoker : Prop :=
  ∀ (O K : Type) [CommRing O] [CommRing K] [Algebra O K], Function.Injective (algebraMap O K) →
  ∀ (n : ℕ) (Z₁ Z₂ g g' : Matrix (Fin (n+1)) (Fin (n+1)) O),
    IsUnit (toK (K := K) Z₁) → IsUnit (toK (K := K) Z₂) → IsUnit g → IsUnit g' → g * Z₁ = Z₂ * g' →
    (IsInt O (yp K g Z₁) ↔ ∃ w : Fin (n+1) → O, Z₂ *ᵥ w = g *ᵥ e O n - e O n) ∧
    (IsInt O (xp K g' Z₁) ↔ ∀ x : Fin (n+1) → O,
        (e K n ᵥ* (toK (K := K) Z₂)⁻¹) ⬝ᵥ (toK (K := K) g *ᵥ (algebraMap O K ∘ x)) -
          (e K n ᵥ* (toK (K := K) Z₁)⁻¹) ⬝ᵥ (algebraMap O K ∘ x) ∈ Set.range (algebraMap O K))
def KKOrbit : Prop :=
  ∀ (O K : Type) [CommRing O] [CommRing K] [Algebra O K], Function.Injective (algebraMap O K) →
  ∀ (n : ℕ) (Z₁ Z₂ : Matrix (Fin (n+1)) (Fin (n+1)) O),
    IsUnit (toK (K := K) Z₁) → IsUnit (toK (K := K) Z₂) →
    ∀ p q, p ∈ LL K Z₁ Z₂ → q ∈ LL K Z₁ Z₂ →
      ((∃ M ∈ KK Z₁, q = act Z₁ p M) ↔
        ∀ x : Fin (n+1) → O, ∃ w : Fin (n+1) → O, Z₂ *ᵥ w = q.1 *ᵥ x - p.1 *ᵥ x)
def Primitive (R : Type) {Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (v : Q) : Prop :=
  ∃ f : Q →ₗ[R] R, f v = 1
def Transitivity : Prop :=
  ∀ (R : Type) [CommRing R], Set.Finite {m : Ideal R | m.IsMaximal} →
  ∀ (Q : Type) [AddCommGroup Q] [Module R Q] [Module.Free R Q] [Module.Finite R Q]
    (Rr : Submodule R Q) (v v' : Q), Primitive R v → Primitive R v' → v - v' ∈ Rr →
    ∃ k : Q ≃ₗ[R] Q, k v = v' ∧ ∀ x, k x - x ∈ Rr
def TransitivityLocal : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (Q : Type) [AddCommGroup Q] [Module R Q] [Module.Free R Q] [Module.Finite R Q]
    (Rr : Submodule R Q) (v v' : Q), Primitive R v → Primitive R v' → v - v' ∈ Rr →
    ∃ k : Q ≃ₗ[R] Q, k v = v' ∧ ∀ x, k x - x ∈ Rr
def TransitivityProd : Prop :=
  ∀ (R₁ R₂ : Type) [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
    (Q : Type) [AddCommGroup Q] [Module (R₁ × R₂) Q] [Module.Free (R₁ × R₂) Q]
    [Module.Finite (R₁ × R₂) Q]
    (Rr : Submodule (R₁ × R₂) Q) (v v' : Q), Primitive (R₁ × R₂) v → Primitive (R₁ × R₂) v' →
    v - v' ∈ Rr →
    ∃ k : Q ≃ₗ[R₁ × R₂] Q, k v = v' ∧ ∀ x, k x - x ∈ Rr
def OrbitMeets : Prop :=
  ∀ (O K : Type) [CommRing O] [CommRing K] [Algebra O K], Function.Injective (algebraMap O K) →
  Set.Finite {m : Ideal O | m.IsMaximal} →
  ∀ (n : ℕ) (Z₁ Z₂ : Matrix (Fin (n+1)) (Fin (n+1)) O),
    IsUnit (toK (K := K) Z₁) → IsUnit (toK (K := K) Z₂) → kap K Z₁ = kap K Z₂ →
    ∀ p ∈ LL K Z₁ Z₂, ∃ M ∈ KK Z₁, act Z₁ p M ∈ LL' K Z₁ Z₂
def blk {R : Type} {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (b c : Fin (m+1) → R) (d : R) :
    Matrix (Fin (m+1) ⊕ Unit) (Fin (m+1) ⊕ Unit) R :=
  Matrix.fromBlocks A (Matrix.of fun i (_ : Unit) => b i) (Matrix.of fun (_ : Unit) j => c j)
    (Matrix.of fun _ _ => d)
def BlockEq : Prop :=
  ∀ (R : Type) [CommRing R] (m : ℕ) (Z₁' Z₂' g₀ g₀' : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (β₁ β₂ α₁ α₂ x y : Fin (m+1) → R) (s₁ s₂ : R),
    IsUnit g₀ → IsUnit g₀' →
    (blk g₀ 0 x 1 * blk Z₁' β₁ α₁ s₁ = blk Z₂' β₂ α₂ s₂ * blk g₀' y 0 1 ↔
      g₀ * Z₁' = Z₂' * g₀' ∧ β₂ = g₀ *ᵥ β₁ - Z₂' *ᵥ y ∧ α₂ = (α₁ + x ᵥ* Z₁') ᵥ* g₀'⁻¹ ∧
        s₂ = s₁ + x ⬝ᵥ β₁ - α₂ ⬝ᵥ y)
def BlockInv : Prop :=
  ∀ (R : Type) [CommRing R] (m : ℕ) (Z₁' Z₂' g₀ g₀' : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (β₁ β₂ α₁ α₂ x y : Fin (m+1) → R) (s₁ s₂ : R),
    IsUnit Z₁' → IsUnit Z₂' → IsUnit g₀ → IsUnit g₀' →
    g₀ * Z₁' = Z₂' * g₀' → β₂ = g₀ *ᵥ β₁ - Z₂' *ᵥ y → α₂ = (α₁ + x ᵥ* Z₁') ᵥ* g₀'⁻¹ →
    s₂ = s₁ + x ⬝ᵥ β₁ - α₂ ⬝ᵥ y →
    let ev : Fin (m+1) → R := Pi.single (Fin.last m) 1
    let y' := Z₁'⁻¹ *ᵥ (g₀⁻¹ *ᵥ ev - ev)
    let x' := (ev ᵥ* g₀' - ev) ᵥ* Z₁'⁻¹
    s₁ - α₁ ⬝ᵥ (Z₁'⁻¹ *ᵥ β₁) = s₂ - α₂ ⬝ᵥ (Z₂'⁻¹ *ᵥ β₂) ∧
    α₁ ⬝ᵥ (Z₁'⁻¹ *ᵥ ev) - α₂ ⬝ᵥ (Z₂'⁻¹ *ᵥ ev) = -(α₁ ⬝ᵥ y') - x ⬝ᵥ (g₀⁻¹ *ᵥ ev) ∧
    ev ⬝ᵥ (Z₁'⁻¹ *ᵥ β₁) - ev ⬝ᵥ (Z₂'⁻¹ *ᵥ β₂) = -(x' ⬝ᵥ β₁) + ev ⬝ᵥ y
end Formalism.SA.A


