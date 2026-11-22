-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_StatementI
-- name    : Formalism_CyclotomicNorms_StatementI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:15.292321+00:00
-- url     : https://prove2.me/theorems/30e9897f-5ea5-49e1-b3f1-bf3a58bb2af1
-- title:
--   Statement I
-- statement:
--   Definitions and structural lemmas for Statement I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/StatementI.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open scoped ComplexOrder
noncomputable section
namespace Formalism.CyclotomicNorms
def Exc (g d ℓ : ℕ) : Prop := ℓ.Prime ∧ g ^ d < ℓ ^ (4 * padicValNat ℓ (g ^ d - 1))
def BB (N g : ℕ) : Set ℕ := {g} ∪ {ℓ | ∃ d, 1 ≤ d ∧ d ≤ N ∧ Exc g d ℓ}
def BBCount : Prop :=
  ∀ g : ℕ, 2 ≤ g →
    (∀ d : ℕ, 1 ≤ d → Set.Finite {ℓ | Exc g d ℓ} ∧ Set.ncard {ℓ | Exc g d ℓ} ≤ 3) ∧
    ∀ N : ℕ, Set.Finite (BB N g) ∧ Set.ncard (BB N g) ≤ 3 * N + 1
def RootsOfUnityCount : Prop :=
  ∀ ℓ w d : ℕ, ℓ.Prime → 1 ≤ w → 1 ≤ d →
    (ℓ ≠ 2 → Nat.card {x : ZMod (ℓ ^ w) // x ^ d = 1} ≤ d * ℓ ^ padicValNat ℓ d) ∧
    Nat.card {x : ZMod (ℓ ^ w) // x ^ d = 1} ≤ 2 * d
def ChoiceCount : Prop :=
  ∀ (Y : ℝ) (N g₁ : ℕ), 2 ≤ Y → 1 ≤ N → Y ≤ g₁ → (g₁ : ℝ) ≤ 2 * Y →
    ∀ S : Finset ℕ, (∀ g ∈ S, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ (BB N g ∩ BB N g₁).Nonempty) →
      (S.card : ℝ) ≤ (3 * N + 1) * (1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1))
def BlocksCycle : Prop :=
  ∀ (G Ω : Type) [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] (B : Finset (Finset Ω))
    (m p : ℕ) (g₀ : G),
    (∀ b ∈ B, b.card = m) → (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint b b') → (∀ x, ∃ b ∈ B, x ∈ b) →
    (∀ g : G, ∀ b ∈ B, b.image (fun x => g • x) ∈ B) →
    p.Prime → Fintype.card Ω < 2 * p →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).IsCycle →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).support.card = p →
    B.card = 1 ∨ B.card = Fintype.card Ω
def JordanTransitive : Prop :=
  ∀ (G Ω : Type) [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] (p : ℕ) (g₀ : G),
    MulAction.IsPretransitive G Ω → p.Prime → Fintype.card Ω < 2 * p →
    p + 3 ≤ Fintype.card Ω →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).IsCycle →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).support.card = p →
    alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range ∧ ¬ Group.IsSolvable G
def Restriction : Prop :=
  ∀ (G k V : Type) [Group G] [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (N : ℕ) (H : Subgroup G) [H.Normal] (I : Subgroup G) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → G → k) (φ : G) (π : Equiv.Perm (Fin N)) (p : ℕ),
    8 ≤ N → Finite (G ⧸ H) → Group.IsSolvable (G ⧸ H) → I ≤ H →
    (∀ W : Submodule k V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ i, ∀ y ∈ I, ρ y (e i) = χ i y • e i) →
    (∀ i j, i ≠ j → ∃ y ∈ I, χ i y ≠ χ j y) →
    (∀ y, y ∈ I ↔ φ * y * φ⁻¹ ∈ I) →
    (∀ i, ∀ y ∈ I, χ (π i) y = χ i (φ⁻¹ * y * φ)) →
    p.Prime → Fintype.card (Fin N) < 2 * p → p + 3 ≤ N → p ∈ π.cycleType →
    ∀ W : Submodule k V, (∀ h ∈ H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤
def IdemHyp {O K A : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup A] [Module K A] [Module O A] [IsScalarTower O K A] (e : A →ₗ[K] A) (c : O)
    (M : Submodule O A) : Prop :=
  e ∘ₗ e = e ∧ c ≠ 0 ∧ ∀ x ∈ M, c • e x ∈ M
def IdempotentLattice : Prop :=
  ∀ (O K A : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup A] [Module K A] [Module O A] [IsScalarTower O K A] (e : A →ₗ[K] A) (c : O)
    (M : Submodule O A), IdemHyp e c M →
    (∀ x ∈ M, c • e x ∈ M ∧ c • e x ∈ LinearMap.range e) ∧
    (∀ y ∈ M, y ∈ LinearMap.range e → ∃ x ∈ M, e x = y) ∧
    (∀ x ∈ M, ∃ u ∈ M, ∃ w ∈ M, u ∈ LinearMap.range e ∧
      w ∈ LinearMap.range (LinearMap.id - e) ∧ c • x = u + w)
def IdempotentDrop : Prop :=
  ∀ (O K A : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup A] [Module K A] [Module O A] [IsScalarTower O K A] (e f Z : A →ₗ[K] A) (c : O)
    (M : Submodule O A), IdemHyp e c M →
    f ∘ₗ e = e ∘ₗ f → (∀ x ∈ M, f x ∈ M) → Z ∘ₗ Z = Z → Z ∘ₗ e = e ∘ₗ Z → Z ∘ₗ f = f ∘ₗ Z →
    (∀ x ∈ M, f (Z x) ∈ M ∧ f (Z x) ∈ LinearMap.range Z) →
    ∀ x ∈ M, c • f (e (Z x)) ∈ M ∧ c • f (e (Z x)) ∈ LinearMap.range (e ∘ₗ Z)
def Discard : Prop :=
  ∀ (n : ℕ) (Q Pi : Matrix (Fin n) (Fin n) ℂ) (δ Dstar η : ℝ),
    Q.PosSemidef → Pi.IsHermitian → Pi * Pi = Pi → 0 ≤ δ → 0 < Dstar →
    (Pi.rank : ℝ) ≤ δ * Dstar → 0 ≤ η → η ≤ 1 →
    (Q * Q).trace.re ≤ (1 + η) * (Q.trace.re) ^ 2 / Dstar →
    (Pi * Q).trace.re ≤ Real.sqrt (2 * δ) * Q.trace.re ∧
    (((1 - Pi) * Q * (1 - Pi)) * ((1 - Pi) * Q * (1 - Pi))).trace.re ≤ (Q * Q).trace.re ∧
    (1 - Real.sqrt (2 * δ)) * Q.trace.re ≤ ((1 - Pi) * Q * (1 - Pi)).trace.re
def monicOf {K : Type} [Field K] {N : ℕ} (a : Fin N → K) : K[X] :=
  X ^ N + ∑ i : Fin N, C (a i) * X ^ (i : ℕ)
open Classical in

def SquarefreeShare : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ),
    ((univ.filter (fun a : Fin N → K => (monicOf a).coeff 0 ≠ 0 ∧ ¬ Squarefree (monicOf a))).card : ℝ)
      * Fintype.card K ≤
      2 * (univ.filter (fun a : Fin N → K => (monicOf a).coeff 0 ≠ 0)).card
end Formalism.CyclotomicNorms


