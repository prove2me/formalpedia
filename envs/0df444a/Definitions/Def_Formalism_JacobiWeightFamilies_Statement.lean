-- Prove2me | Definitions.Def_Formalism_JacobiWeightFamilies_Statement
-- name    : Formalism_JacobiWeightFamilies_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:36.387581+00:00
-- url     : https://prove2.me/theorems/1804bfc1-3b22-4e9f-8f26-f7bf596b48d3
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/JacobiWeightFamilies/Statement.lean

import Definitions.Def_Formalism_HalfLinks_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.WT
open Formalism Formalism.CMTypeGaloisData
def chiJ (d n : ℕ) : ℝ := (jacobiSym (n : ℤ) d : ℝ)
def DD (D z : ℝ) (M r : ℕ) : Finset ℕ :=
  (Icc ⌈D⌉₊ ⌊2 * D⌋₊).filter
    (fun d => d ≡ r [MOD 8 * M] ∧ Squarefree d ∧ ∀ p ∈ d.primeFactors, z < (p : ℝ))
def IsJacFamily (S : Finset ℕ) (χ : (d : ℕ) → DirichletCharacter ℂ d) : Prop :=
  ∀ d ∈ S, ∀ n : ℕ, χ d (n : ZMod d) = ((jacobiSym (n : ℤ) d : ℤ) : ℂ)
def L1 {N : ℕ} (χ : DirichletCharacter ℂ N) : ℝ :=
  if h : N = 0 then 0 else
    haveI : NeZero N := ⟨h⟩; (DirichletCharacter.LFunction χ 1).re
def ell {N : ℕ} (χ : DirichletCharacter ℂ N) : ℝ :=
  if h : N = 0 then 0 else
    haveI : NeZero N := ⟨h⟩;
    (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
def GJ (d : ℕ) (χ : DirichletCharacter ℂ d) (y : ℝ) : ℝ := Gch (chiJ d) (ell χ) y
def WParams (D : ℝ) (M r : ℕ) : Prop :=
  Odd M ∧ Squarefree M ∧ (M : ℝ) ≤ D ^ ((1 : ℝ) / 10) ∧ r % 4 = 3 ∧ Nat.Coprime r M ∧
    ∀ p : ℕ, p.Prime → p ∣ M → jacobiSym (p : ℤ) r = 1
def JacFamilyExists : Prop :=
  ∀ S : Finset ℕ, (∀ d ∈ S, Odd d) → ∃ χ : (d : ℕ) → DirichletCharacter ℂ d, IsJacFamily S χ
def WeightThm : Prop :=
  ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (z : ℝ) (M r : ℕ),
    x ≤ z → z ≤ x ^ 4 → WParams (Real.exp (C0 * Real.log x ^ 2)) M r →
    ∀ χ : (d : ℕ) → DirichletCharacter ℂ d, IsJacFamily (DD (Real.exp (C0 * Real.log x ^ 2)) z M r) χ →
      0 < (∑ d ∈ DD (Real.exp (C0 * Real.log x ^ 2)) z M r, L1 (χ d)) ∧
      ∀ y : ℝ, 1 ≤ y → y ≤ (Real.exp (C0 * Real.log x ^ 2)) ^ ((1 : ℝ) / 10) →
        (∑ d ∈ DD (Real.exp (C0 * Real.log x ^ 2)) z M r, L1 (χ d) * GJ d (χ d) y)
          ≤ C * (Real.log y + y * (C0 * Real.log x ^ 2) ^ 2 *
              (Real.exp (-(C0 * Real.log x ^ 2 / (10 * Real.log z))) + C0 * Real.log x ^ 2 / z))
            * (∑ d ∈ DD (Real.exp (C0 * Real.log x ^ 2)) z M r, L1 (χ d))
def WeightCor : Prop :=
  ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ m : ℕ, 0 < m → (m : ℝ) ≤ x →
    ∀ (z : ℝ) (M r : ℕ),
    x ^ 3 ≤ z → z ≤ x ^ 4 → WParams (Real.exp (C0 * Real.log x ^ 2)) M r →
    ∀ χ : (d : ℕ) → DirichletCharacter ℂ d, IsJacFamily (DD (Real.exp (C0 * Real.log x ^ 2)) z M r) χ →
    ∀ E : ℝ, (∀ d ∈ DD (Real.exp (C0 * Real.log x ^ 2)) z M r, chebyshevWeightedAverage m x Gz - chebyshevWeightedAverage m x (GJ d (χ d)) ≤ E) →
      chebyshevWeightedAverage m x Gz ≤ E + C * Real.log x
def WeightedSieveImpliesRH : Prop :=
  ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 →
  (∀ ε : ℝ, 0 < ε → ∃ C K x₀ : ℝ, 1 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
    ∃ (m k f : ℕ) (B D' z : ℝ) (M r : ℕ) (χ : (d : ℕ) → DirichletCharacter ℂ d),
      HalfSize (1 / 2) ε K x B D' m k f ∧
      x ^ 3 ≤ z ∧ z ≤ x ^ 4 ∧
      WParams (Real.exp (C0 * Real.log x ^ 2)) M r ∧
      IsJacFamily (DD (Real.exp (C0 * Real.log x ^ 2)) z M r) χ ∧
      ∀ d ∈ DD (Real.exp (C0 * Real.log x ^ 2)) z M r,
        ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (_ : DecidableEq G)
          (H : HalfLinksCore G C ε (1 / 2) x B D' m k f),
          2 * x * (∑ p ∈ H.host.Bad.filter Nat.Prime, Real.log p / p) ≤ K * x ^ ((1 : ℝ) / 2 + ε) ∧
          (∑ ψ ∈ H.host.chars, H.host.coef ψ * chebyshevWeightedAverage m x (Gch (H.host.chi ψ) (H.ell ψ)))
            ≤ chebyshevWeightedAverage m x (GJ d (χ d))) →
  RiemannHypothesis
end Formalism.WT


