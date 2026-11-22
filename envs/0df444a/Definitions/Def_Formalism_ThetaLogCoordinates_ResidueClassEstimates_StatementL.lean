-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementL
-- name    : Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:07.247959+00:00
-- url     : https://prove2.me/theorems/e716e261-d513-4039-baf6-67ed46d1e2c0
-- title:
--   Statement L
-- statement:
--   Definitions and structural lemmas for Statement L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/StatementL.lean

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
open scoped BigOperators TensorProduct
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
def SaturatedBasisExtension : Prop :=
  ∀ {O M1 M2 : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M1] [Module O M1] [Module.Free O M1] [Module.Finite O M1]
    [AddCommGroup M2] [Module O M2] [Module.Free O M2] [Module.Finite O M2] (ϖ : O), Irreducible ϖ →
    ∀ (Sp : Set M2) (abelian₂ : Submodule O M1) (Δ : M1 →ₗ[O] M2),
      (∀ x, ϖ • x ∈ abelian₂ → x ∈ abelian₂) →
      (∀ x, (∃ y, Δ x = ϖ • y) → ∃ x', x = ϖ • x') →
      (∀ u ∈ abelian₂, Δ u ∈ Submodule.span O Sp ⊔ (Ideal.span {ϖ}) • (⊤ : Submodule O M2)) →
      ∃ (R : ℕ) (g : Fin R → M2), (∀ i, g i ∈ Sp) ∧ LinearIndependent O g ∧
        (∃ T : Submodule O M2, IsCompl (Submodule.span O (Set.range g)) T) ∧
        Submodule.span O Sp ≤ Submodule.span O (Set.range g) ⊔ (Ideal.span {ϖ}) • (⊤ : Submodule O M2) ∧
        Module.finrank O abelian₂ ≤ R
def IsSat {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (N : Submodule O M) : Prop :=
  ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ N → x ∈ N
def SaturatedSubmoduleProperties : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O],
    (∀ {M : Type} [AddCommGroup M] [Module O M] (N N' : Submodule O M), IsSat N → IsSat N' → IsSat (N ⊓ N')) ∧
    (∀ {M ι : Type} [AddCommGroup M] [Module O M] (b : Module.Basis ι O M) (s : Set ι),
      IsSat (Submodule.span O (b '' s))) ∧
    (∀ {M : Type} [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (N : Submodule O M),
      IsSat N ↔ ∃ T : Submodule O M, IsCompl N T) ∧
    (∀ {M M' : Type} [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
      [AddCommGroup M'] [Module O M'] [Module.Free O M'] [Module.Finite O M']
      (N : Submodule O M) (N' : Submodule O M'), IsSat N → IsSat N' →
      IsSat (LinearMap.range (TensorProduct.map N.subtype N'.subtype)) ∧
      Module.finrank O (LinearMap.range (TensorProduct.map N.subtype N'.subtype)) =
        Module.finrank O N * Module.finrank O N')
abbrev CoarseVar (I1 I2 : Type) : Type := I1 ⊕ (I2 ⊕ I2)
def phC (O : Type) [CommRing O] {I1 I2 : Type} (P : I1 ⊕ I2 → ℕ) (Q : I2 → ℕ) :
    MvPolynomial (CoarseVar I1 I2) O →ₐ[O] MvPolynomial (I1 ⊕ I2) O :=
  MvPolynomial.aeval fun x => match x with
    | Sum.inl i => MvPolynomial.X (Sum.inl i) ^ P (Sum.inl i)
    | Sum.inr (Sum.inl i) => MvPolynomial.X (Sum.inr i) ^ P (Sum.inr i)
    | Sum.inr (Sum.inr i) => MvPolynomial.X (Sum.inr i) ^ (P (Sum.inr i) * Q i)
def MonomialDigitExpansion : Prop :=
  ∀ (O : Type) [CommRing O] [Nontrivial O] (I1 I2 : Type) (P : I1 ⊕ I2 → ℕ) (Q : I2 → ℕ),
    (∀ i, 1 ≤ P i) → (∀ i, 1 ≤ Q i) →
    ∀ e : (I1 ⊕ I2) →₀ ℕ, ∃! ml : ((CoarseVar I1 I2) →₀ ℕ) × ((I1 ⊕ I2) →₀ ℕ),
      (∀ i, ml.1 (Sum.inr (Sum.inl i)) < Q i) ∧ (∀ i, ml.2 i < P i) ∧
      phC O P Q (MvPolynomial.monomial ml.1 1) * MvPolynomial.monomial ml.2 1 = MvPolynomial.monomial e 1
def CountL : Prop :=
  ∀ (k P n : ℕ), 1 ≤ k → 1 ≤ P →
    ∑ la ∈ (Finset.univ : Finset (Fin k → Fin P)).filter
        (fun la => (∑ c, (la c : ℕ)) ≤ n ∧ P ∣ n - ∑ c, (la c : ℕ)),
      ((n - ∑ c, (la c : ℕ)) / P + k - 1).choose (k - 1) = (n + k - 1).choose (k - 1)
def CountLa : Prop :=
  ∀ (k P n : ℕ), 1 ≤ k → 1 ≤ P →
    ((Finset.univ : Finset (Fin k → Fin P)).filter
      (fun la => (∑ c, (la c : ℕ)) % P = n % P)).card = P ^ (k - 1)
def ResidueClassLowerBound : Prop :=
  ∀ (r Q be c : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
        (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card : ℝ)
def FrobStep : Prop :=
  ∀ (p R : ℕ) (σ : Type) (f : MvPolynomial σ ℤ), p.Prime →
    ∃ h : MvPolynomial σ ℤ, MvPolynomial.expand (p ^ R) f = f ^ (p ^ R) + MvPolynomial.C (p : ℤ) * h
def DetPowNonzero : Prop :=
  ∀ (F : Type) [CommRing F] [Nontrivial F] (r : ℕ) (e : Fin r → ℕ), (∀ l, 1 ≤ e l) →
    (Matrix.of fun l c : Fin r => (MvPolynomial.X (l, c) : MvPolynomial (Fin r × Fin r) F) ^ e l).det ≠ 0
def CompareW : Prop :=
  ∀ (k Ns P n B : ℕ) (Y : ℝ), 1 ≤ k → 1 ≤ P → 1 ≤ Y →
    (n : ℝ) / P - 2 * k * Ns ≤ B → 7.2 * Y * (k : ℝ) ^ 2 * Ns ≤ (n : ℝ) / P →
    ((n + k - 1).choose (k - 1) : ℝ) * (1 - 2 / (7.2 * Y)) ≤
      (P : ℝ) ^ (k - 1) * ((B + k - 1).choose (k - 1) : ℝ)
def CompareA : Prop :=
  ∀ (k a a' : ℕ), 1 ≤ k → 1 ≤ a → a' ≤ a →
    ((a + k - 1).choose (k - 1) : ℝ) * (1 - k * ((a : ℝ) - a') / a) ≤ ((a' + k - 1).choose (k - 1) : ℝ)
def TotalLoss : Prop :=
  ∀ (J r N : ℕ) (Y : ℝ), 2 ≤ r → 3 * J * r ≤ N → 0 < Y →
    (J : ℝ) / (32 * Y) + J * r * (0.28 + r / 2) / Y + N / (32 * Y) + N / Y ≤ N * r / Y
def PlanesLower : Prop :=
  ∀ (q r K : ℕ), 2 ≤ q →
    (q : ℝ) ^ (r * K) ≤ ∏ i ∈ range r, (((q : ℝ) ^ (r + K - i) - 1) / ((q : ℝ) ^ (r - i) - 1))
end Formalism.InvariantFactorPaths.BranchingDimensions


