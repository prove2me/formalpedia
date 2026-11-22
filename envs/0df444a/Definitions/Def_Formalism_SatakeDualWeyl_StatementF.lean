-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_StatementF
-- name    : Formalism_SatakeDualWeyl_StatementF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:16:55.122807+00:00
-- url     : https://prove2.me/theorems/44d53340-529a-4329-8577-63f3c53b4a98
-- title:
--   Statement F
-- statement:
--   Definitions and structural lemmas for Statement F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/StatementF.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.UG
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
def ordL (x : L) : ℤ := if h : Valued.v x = 0 then 0 else -Multiplicative.toAdd (WithZero.unzero h)
def intL (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : Subring L :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer
def IsUnramInv (ϖ : L) (σ : L →+* L) (q : ℕ) : Prop :=
  (∀ x, σ (σ x) = x) ∧ (∀ x, Valued.v (σ x) = Valued.v x) ∧ σ ϖ = ϖ ∧
  Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
  (∃ x ∈ intL L, Valued.v (σ x - x) = 1) ∧ 2 ≤ q ∧
  Nat.card ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
    IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) = q ^ 2
def antiJ (L : Type) [Field L] (n : ℕ) : Matrix (Fin n) (Fin n) L :=
  fun i j => if i.val + j.val + 1 = n then 1 else 0
abbrev GU (σ : L →+* L) (n : ℕ) : Subgroup (GL (Fin n) L) := UJ σ (antiJ L n)
def KU (σ : L →+* L) (n : ℕ) : Subgroup (GU σ n) :=
  (intPts (intL L).subtype (GU σ n)).subgroupOf (GU σ n)
def IsBorelU {σ : L →+* L} {n : ℕ} (b : GU σ n) : Prop :=
  ∀ i j : Fin n, j < i → ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0
def IsUnipU {σ : L →+* L} {n : ℕ} (u : GU σ n) : Prop :=
  IsBorelU u ∧ ∀ i : Fin n, ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1
def tMat (ϖ : L) (n m : ℕ) (a : Fin m → ℤ) : Matrix (Fin n) (Fin n) L :=
  Matrix.diagonal fun i =>
    if h : i.val < m then ϖ ^ (a ⟨i.val, h⟩)
    else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then ϖ ^ (-(a ⟨n - 1 - i.val, h'.2⟩)) else 1
def chiDeltaU {σ : L →+* L} {n m : ℕ} (q : ℕ) (α : Fin m → ℂ) (b : GU σ n) : ℂ :=
  ∏ i : Fin m,
    if h : i.val < n then
      α i ^ (ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)) *
        (q : ℂ) ^ (-(ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ)))
    else 1
open Classical in

def SatU {σ : L →+* L} {n m : ℕ} (ϖ : L) (q : ℕ) (h : GU σ n → ℂ) (α : Fin m → ℂ) : ℂ :=
  ∑ᶠ a : Fin m → ℤ, (∏ i : Fin m, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
    ∑ᶠ x : GU σ n ⧸ KU σ n,
      if ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
          (((x.out : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
            tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
              (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
      then h x.out else 0
def IsSphericalU {σ : L →+* L} {n m : ℕ} (q : ℕ) (α : Fin m → ℂ) (φ : GU σ n → ℂ) : Prop :=
  ∀ b g k : GU σ n, IsBorelU b → k ∈ KU σ n → φ (b * g * k) = chiDeltaU q α b * φ g
def SphericalExistsU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ),
    IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) →
    ∃ φ : GU σ n → ℂ, IsSphericalU q α φ ∧ φ 1 = 1 ∧ ∀ ψ, IsSphericalU q α ψ → ψ = fun g => ψ 1 * φ g
def HeckeCommU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (k : Type) [CommRing k], IsUnramInv ϖ σ q →
    ∀ f₁ ∈ Hecke k (KU σ n), ∀ f₂ ∈ Hecke k (KU σ n), conv (KU σ n) f₁ f₂ = conv (KU σ n) f₂ f₁
def SatakeInert : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ),
    IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) →
    ∀ h ∈ Hecke ℂ (KU σ n), ∀ φ : GU σ n → ℂ, IsSphericalU q α φ →
      hAct (KU σ n) h φ = SatU ϖ q h α • φ
def SatWeyl : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ),
    IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) →
    ∀ h ∈ Hecke ℂ (KU σ n),
      (∀ π : Equiv.Perm (Fin m), SatU ϖ q h (α ∘ π) = SatU ϖ q h α) ∧
      (∀ i : Fin m, SatU ϖ q h (Function.update α i (α i)⁻¹) = SatU ϖ q h α)
def SatMul : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ),
    IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) →
    ∀ h₁ ∈ Hecke ℂ (KU σ n), ∀ h₂ ∈ Hecke ℂ (KU σ n),
      SatU ϖ q (conv (KU σ n) h₁ h₂) α = SatU ϖ q h₁ α * SatU ϖ q h₂ α
end Formalism.UG


