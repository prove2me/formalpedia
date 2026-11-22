-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_StatementB
-- name    : Formalism_SubspaceCounting_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:18.683012+00:00
-- url     : https://prove2.me/theorems/f66a2cf3-ae06-4529-86da-924b97b1f695
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/StatementB.lean

import Mathlib
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
namespace Formalism.G0
def window (n i L : ℕ) : Finset ℕ :=
  (Finset.range L).image fun j => (i + j) % n
def CondA (n : ℕ) (T : Finset ℕ) (L₂ K : ℕ) : Prop :=
  ∀ i < n, (T ∩ window n i L₂).card ≤ K
def GoodRun (n : ℕ) (T : Finset ℕ) (L₂ R i e : ℕ) : Prop :=
  ∃ u : Fin R → ℕ, StrictMono u ∧ (∀ l, u l ≤ e) ∧
    (∀ l, (i + u l) % n ∈ T) ∧ (∀ l, Even ((i + u l) % n)) ∧
    (∀ (l : Fin R) (h : l.val + 1 < R),
      L₂ < 2 * (u ⟨l.val + 1, h⟩ - u l) ∧
      ∀ d, u l < d → d < u ⟨l.val + 1, h⟩ → (i + d) % n ∉ T)
def CondB (n : ℕ) (T : Finset ℕ) (L₂ r N₁ : ℕ) : Prop :=
  ∀ i e : ℕ, i < n → e < n →
    N₁ ≤ ((Finset.range (e + 1)).filter fun d => (i + d) % n ∈ T).card →
    GoodRun n T L₂ (3 * r) i e
def CondC (n : ℕ) (T : Finset ℕ) (G : ℕ) : Prop :=
  ∀ i ∈ T, ∃ d : ℕ, 1 ≤ d ∧ d ≤ G ∧ (i + d) % n ∈ T
def GoodOrbit (n : ℕ) (T : Finset ℕ) (L₂ K r N₁ G : ℕ) : Prop :=
  CondA n T L₂ K ∧ CondB n T L₂ r N₁ ∧ CondC n T G ∧ N₁ ≤ T.card
def probNotGood (n : ℕ) (δ : ℝ) (L₂ K r N₁ G : ℕ) : ℝ := by
  classical
  exact ∑ T ∈ (Finset.range n).powerset,
    if 0 ∈ T ∧ ¬ GoodOrbit n T L₂ K r N₁ G then
      δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) else 0
def binLower (n : ℕ) (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, (n.choose j : ℝ) * δ ^ j * (1 - δ) ^ (n - j)
def ChoiceOfTops : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (L₂ K r N₁ G : ℕ), 2 ≤ n → Even n → 0 ≤ δ → 1 ≤ L₂ →
    (L₂ : ℝ) * δ ≤ 1 → 1 ≤ r → 3 * r ≤ N₁ →
    probNotGood n δ L₂ K r N₁ G ≤
      n * (L₂.choose K : ℝ) * δ ^ K +
      n * (1 - (1 / 2 : ℝ) ^ (3 * r) * (1 - L₂ * δ) ^ (3 * r)) ^ (N₁ / (3 * r) - 1) +
      n * (1 - δ) ^ G + binLower n δ N₁
def fTail (k' y : ℕ) : ℝ := Real.log ((y + k').choose k')
def tailSum {N : ℕ} (x : Fin N → ℕ) (u : ℕ) : ℕ :=
  ∑ l : Fin N, if u ≤ l.val then x l else 0
def TailConcavity : Prop :=
  ∀ (N k' X u₀ : ℕ) (α B : Fin N → ℕ) (hu : u₀ < N),
    (∀ l, k' ≤ B l) →
    (∀ (l : Fin N) (h : l.val + 1 < N), 4 * B ⟨l.val + 1, h⟩ ≤ B l) →
    (∀ u, tailSum α u ≤ tailSum B u) →
    tailSum α u₀ + X ≤ tailSum B u₀ →
    ∑ l, fTail k' (α l) ≤ ∑ l, fTail k' (B l) - (X : ℝ) * k' / (4 * B ⟨u₀, hu⟩)
def gaussBinom (q : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1)
def countAbove {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (j : ℕ) : ℕ :=
  Nat.card {U : Submodule F W // A ≤ U ∧ Module.finrank F U = j}
def countBelow {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (j : ℕ) : ℕ :=
  Nat.card {U : Submodule F W // U ≤ A ∧ Module.finrank F U = j}
def SubspaceCount : Prop :=
  ∀ {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W] (k : ℕ),
    countBelow (⊤ : Submodule F W) k = gaussBinom (Fintype.card F) (Module.finrank F W) k
def QVandermonde : Prop :=
  ∀ q m g n : ℕ,
    gaussBinom q (m + g) n =
      ∑ l ∈ Finset.range (n + 1), q ^ (l * (m + l - n)) * gaussBinom q m (n - l) * gaussBinom q g l ∧
    gaussBinom q (m + g) n =
      ∑ l ∈ Finset.range (n + 1), q ^ ((n - l) * (g - l)) * gaussBinom q m (n - l) * gaussBinom q g l
def TypeIIUp : Prop :=
  ∀ {F P Q : Type} [Field F] [Fintype F] [AddCommGroup P] [Module F P] [Finite P]
    [AddCommGroup Q] [Module F Q] [Finite Q] (f : P →ₗ[F] Q) (N g j : ℕ),
    Module.finrank F P = N → Module.finrank F Q = N + g →
    (countAbove (LinearMap.range f) j : ℤ) =
      ∑ l ∈ Finset.range (j + 1),
        (Fintype.card F : ℤ) ^ (l * (N + l - j)) * gaussBinom (Fintype.card F) g l *
          Nat.card {U : Submodule F P // U ≤ LinearMap.ker f ∧
            Module.finrank F U + (j - l) = N}
def TypeIIDown : Prop :=
  ∀ {F P Q : Type} [Field F] [Fintype F] [AddCommGroup P] [Module F P] [Finite P]
    [AddCommGroup Q] [Module F Q] [Finite Q] (f : P →ₗ[F] Q) (N g j : ℕ),
    Module.finrank F P = N → Module.finrank F Q = N + g →
    (Nat.card {U : Submodule F Q // LinearMap.range f ≤ U ∧ Module.finrank F U + j = N + g} : ℤ) =
      ∑ l ∈ Finset.range (j + 1),
        (Fintype.card F : ℤ) ^ ((j - l) * (g - l)) * gaussBinom (Fintype.card F) g l *
          countBelow (LinearMap.ker f) (j - l)
end Formalism.G0


