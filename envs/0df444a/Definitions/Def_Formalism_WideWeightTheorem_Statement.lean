-- Prove2me | Definitions.Def_Formalism_WideWeightTheorem_Statement
-- name    : Formalism_WideWeightTheorem_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:17.712037+00:00
-- url     : https://prove2.me/theorems/4e0c7214-87b9-4db8-89f7-7c520d1b47e5
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WideWeightTheorem/Statement.lean

import Definitions.Def_Formalism_JacobiWeightFamilies_Statement
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
namespace Formalism.WeightedSieveThreeParameter
open Formalism Formalism.CMTypeGaloisData Formalism.WT
def Par3 (C0 x z D : ℝ) : Prop :=
  0 < D ∧ x ^ 3 ≤ z ∧ C0 * Real.log z * Real.log x ≤ Real.log D ∧ Real.log D ≤ x ^ ((1 : ℝ) / 10)
def gavg {n : ℕ} (w y : Fin n → ℝ) (f : ℝ → ℝ) : ℝ := ∑ j, w j * f (y j)
def AvgCondition {n : ℕ} (w y : Fin n → ℝ) (z : ℝ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ (∑ j, w j) ≤ 1 ∧ ∀ j, 1 ≤ y j ∧ y j ≤ z
def WeightThm' : Prop :=
  ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (D z : ℝ) (M r : ℕ),
    Par3 C0 x z D → WParams D M r →
    ∀ χ : (d : ℕ) → DirichletCharacter ℂ d, IsJacFamily (DD D z M r) χ →
      0 < (∑ d ∈ DD D z M r, L1 (χ d)) ∧
      ∀ y : ℝ, 1 ≤ y → y ≤ z →
        (∑ d ∈ DD D z M r, L1 (χ d) * GJ d (χ d) y)
          ≤ C * (Real.log (2 * y) + y / x ^ 2) * (∑ d ∈ DD D z M r, L1 (χ d))
def WeightThm3Wide : Prop :=
  ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (D z : ℝ) (M r : ℕ),
    Par3 C0 x z D → WParams D M r →
    ∀ χ : (d : ℕ) → DirichletCharacter ℂ d, IsJacFamily (DD D z M r) χ →
      0 < (∑ d ∈ DD D z M r, L1 (χ d)) ∧
      ∀ y : ℝ, 1 ≤ y → y ≤ D ^ ((1 : ℝ) / 10) →
        (∑ d ∈ DD D z M r, L1 (χ d) * GJ d (χ d) y)
          ≤ C * (Real.log (2 * y) + y * Real.log D ^ 2 *
              (Real.exp (-(Real.log D / (10 * Real.log z))) + Real.log D / z))
            * (∑ d ∈ DD D z M r, L1 (χ d))
def WeightCor' : Prop :=
  ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (D z : ℝ) (M r : ℕ),
    Par3 C0 x z D → WParams D M r →
    ∀ χ : (d : ℕ) → DirichletCharacter ℂ d, IsJacFamily (DD D z M r) χ →
    ∀ (n : ℕ) (w y : Fin n → ℝ), AvgCondition w y z → ∀ E B : ℝ, 0 ≤ B →
      (∀ d ∈ DD D z M r, gavg w y Gz - gavg w y (GJ d (χ d)) ≤ E + B * |ell (χ d)|) →
        gavg w y Gz ≤ E + C * (∑ j, w j * (Real.log (2 * y j) + y j / x ^ 2)) + C * B * Real.log D ^ 2
def WeightCorEx : Prop :=
  ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (D z : ℝ) (M r : ℕ),
    Par3 C0 x z D → WParams D M r →
    ∀ χ : (d : ℕ) → DirichletCharacter ℂ d, IsJacFamily (DD D z M r) χ →
    ∀ (n : ℕ) (w y : Fin n → ℝ), AvgCondition w y z → ∀ (Ex : Finset ℕ) (E B κ : ℝ),
      Ex ⊆ DD D z M r → (Ex.card : ℝ) ≤ κ * (DD D z M r).card → 0 ≤ E → 0 ≤ B →
      (∀ d ∈ DD D z M r \ Ex, gavg w y Gz - gavg w y (GJ d (χ d)) ≤ E + B * |ell (χ d)|) →
        gavg w y Gz ≤ E + C * (∑ j, w j * (Real.log (2 * y j) + y j / x ^ 2)) + C * B * Real.log D ^ 2
          + C * κ * (∑ j, w j * y j) * Real.log D ^ 2
def ChebyshevWeightedAverageOverJacobiFamily : Prop :=
  ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ m : ℕ, 0 < m → (m : ℝ) ≤ x →
    ∀ (D z : ℝ) (M r : ℕ), Par3 C0 x z D → 4 * x * (m : ℝ) ^ 2 ≤ z → WParams D M r →
    ∀ χ : (d : ℕ) → DirichletCharacter ℂ d, IsJacFamily (DD D z M r) χ →
    ∀ (Ex : Finset ℕ) (E B κ : ℝ),
      Ex ⊆ DD D z M r → (Ex.card : ℝ) ≤ κ * (DD D z M r).card → 0 ≤ E → 0 ≤ B →
      (∀ d ∈ DD D z M r \ Ex, chebyshevWeightedAverage m x Gz - chebyshevWeightedAverage m x (GJ d (χ d)) ≤ E + B * |ell (χ d)|) →
        chebyshevWeightedAverage m x Gz ≤ E + C * Real.log x + C * B * Real.log D ^ 2 + C * κ * x * Real.log D ^ 2
def WeightedSieveImpliesRHThreeParameter : Prop :=
  ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 →
  (∀ ε : ℝ, 0 < ε → ∃ C K x₀ : ℝ, 1 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
    ∃ (m k f : ℕ) (B D' D z : ℝ) (M r : ℕ) (χ : (d : ℕ) → DirichletCharacter ℂ d) (Ex : Finset ℕ) (Bw κ : ℝ),
      HalfSize (1 / 2) ε K x B D' m k f ∧
      Par3 C0 x z D ∧ 4 * x * (m : ℝ) ^ 2 ≤ z ∧
      WParams D M r ∧
      IsJacFamily (DD D z M r) χ ∧
      Ex ⊆ DD D z M r ∧ (Ex.card : ℝ) ≤ κ * (DD D z M r).card ∧
      0 ≤ Bw ∧ Bw * Real.log D ^ 2 ≤ K * x ^ ((1 : ℝ) / 2 + ε) ∧
      κ * x * Real.log D ^ 2 ≤ K * x ^ ((1 : ℝ) / 2 + ε) ∧
      ∀ d ∈ DD D z M r \ Ex,
        ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (_ : DecidableEq G)
          (H : HalfLinksCore G C ε (1 / 2) x B D' m k f),
          2 * x * (∑ p ∈ H.host.Bad.filter Nat.Prime, Real.log p / p) ≤ K * x ^ ((1 : ℝ) / 2 + ε) ∧
          (∑ ψ ∈ H.host.chars, H.host.coef ψ * chebyshevWeightedAverage m x (Gch (H.host.chi ψ) (H.ell ψ)))
            ≤ chebyshevWeightedAverage m x (GJ d (χ d)) + Bw * |ell (χ d)|) →
  RiemannHypothesis
end Formalism.WeightedSieveThreeParameter


