-- Prove2me | Definitions.Def_Formalism_MonomialMeanResidues_MonomialMean
-- name    : Formalism_MonomialMeanResidues_MonomialMean
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:17.494148+00:00
-- url     : https://prove2.me/theorems/c5dd64fb-ac23-4b44-9d79-d7062bc44095
-- title:
--   Monomial Mean
-- statement:
--   Definitions and structural lemmas for Monomial Mean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMean.lean

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CombinedAverageDegreeBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.HermiteSiegelSlopes
def Averages : Prop :=
  ∀ D T : ℕ, 1 ≤ D → D + 1 ≤ T →
    ∑ a ∈ range (T - D), (a + D - 1).choose (D - 1) = (T - 1).choose D ∧
    (D + 1) * ∑ a ∈ range (T - D), a * (a + D - 1).choose (D - 1)
      = D * (T - D - 1) * (T - 1).choose D
def MonomialMean : Prop :=
  ∀ (D a : ℕ) (i : Fin D), 1 ≤ D →
    Fintype.card (Sym (Fin D) a) = (a + D - 1).choose (D - 1) ∧
    D * ∑ α : Sym (Fin D) a, Multiset.count i (α : Multiset (Fin D))
      = a * (a + D - 1).choose (D - 1)
def RaBound : Prop :=
  ∀ D T a : ℕ, 1 ≤ D → D + 1 ≤ T → a < T - D → (a + D - 1).choose (D - 1) ≤ T ^ D
def RhoChain : Prop :=
  ∀ n D j0 δ Λ h ℓ C Θ ρ0 ρ1 : ℝ, 1 ≤ n → 1 ≤ D → 1 ≤ j0 → 1 ≤ δ → 1 ≤ Λ → 26 ≤ C →
    Θ = n * D * j0 * δ * (2 + |h| + Real.log Λ) → 1 ≤ ℓ → ℓ ≤ 2 * Θ ^ 20 →
    ρ0 = 8 * D * δ * n * ℓ * Λ → ρ1 = ρ0 * (1 + 1 / (8 * D * δ)) →
    2 ≤ Θ ∧ 1 ≤ ρ1 ∧ Real.log ρ1 ≤ Real.log ρ0 + 1 / (8 * D * δ) ∧
    Real.log ρ1 ≤ Real.log Λ + C * Real.log Θ ∧
    Real.log D ≤ Real.log Λ + C * Real.log Θ ∧
    26 * Real.log 2 ≤ Real.log Λ + C * Real.log Θ
def EtaBounds : Prop :=
  ∀ (D N n : ℕ) (δ h hS lρ0 g : ℝ) (lam : Fin D → ℝ), 1 ≤ D → 1 ≤ N → N ≤ n → 1 ≤ δ →
    g = ((D : ℝ) + 1) * (Real.log n + 1) / 2 + 1 →
    (∀ i, lam i ≤ lρ0 + 1 / (8 * D * δ)) →
    ((D : ℝ) + 1) * δ * h + D * δ * lρ0
        - δ * (((D : ℝ) + 1) * (harmonic (N - 1) : ℝ) / 2 + Real.log 2 / δ + 1 / 8) ≤ hS →
    hS ≤ ((D : ℝ) + 1) * δ * h + δ * ∑ i, lam i →
    ((D : ℝ) + 1) * h + D * ((∑ i, lam i) / D) - g ≤ hS / δ ∧
    hS / δ ≤ ((D : ℝ) + 1) * h + D * ((∑ i, lam i) / D)
def GradedSum : Prop :=
  ∀ (D T : ℕ) (δ h J g lamb η cA : ℝ) (lA degGr : ℕ → ℝ), 1 ≤ D → D + 1 ≤ T → 0 ≤ δ → 0 ≤ g →
    ((D : ℝ) + 1) * h + D * lamb - g ≤ η → η ≤ ((D : ℝ) + 1) * h + D * lamb →
    (∀ a < T - D, lA a ≤ cA) →
    (∀ a < T - D, ((a + D - 1).choose (D - 1) : ℝ) * δ *
        (-J + ((T : ℝ) - a - D - 3) * η - a * lamb - lA a) ≤ degGr a) →
    ((T - 1).choose D : ℝ) * δ *
        (((T : ℝ) - 3 * ((D : ℝ) + 1)) * h - J - 2 * D * lamb - ((T : ℝ) / ((D : ℝ) + 1) - 1) * g - cA)
      ≤ ∑ a ∈ range (T - D), degGr a
def ConstAbsorb : Prop :=
  ∀ (D T : ℕ) (lρ1 lρ : ℝ), 1 ≤ D → 1 ≤ T → lρ1 ≤ lρ → Real.log D ≤ lρ → 26 * Real.log 2 ≤ lρ →
    2 * D * lρ1 + D * (Real.log D / 2 + lρ1)
        + Real.log (34 * (2 ^ (D + 1) * Real.pi ^ D / ((D - 1).factorial : ℝ)) * (T : ℝ) ^ D) / 2
      ≤ 4 * D * (lρ + Real.log T)
def HSClaim : Prop :=
  ∀ (D T : ℕ) (δ d h J g lamb η lρ1 lρ lβ lΛD lΛT C0 rkP cor degP degQ degMT : ℝ)
    (lA degGr : ℕ → ℝ),
    1 ≤ D → D + 1 ≤ T → 0 < δ → 0 < d → 0 ≤ g → 0 ≤ lβ → 0 ≤ lΛD → 0 ≤ lΛT → 4 ≤ C0 →

    0 ≤ lρ1 → lρ1 ≤ lρ → Real.log D ≤ lρ → 26 * Real.log 2 ≤ lρ → lamb ≤ lρ1 →
    ((D : ℝ) + 1) * h + D * lamb - g ≤ η → η ≤ ((D : ℝ) + 1) * h + D * lamb →

    (∀ a < T - D, lA a ≤ ((T : ℝ) + D + 1) / 2 * lβ
        + Real.log (34 * (2 ^ (D + 1) * Real.pi ^ D / ((D - 1).factorial : ℝ))
            * ((a + D - 1).choose (D - 1) : ℝ)) / 2
        + D * (Real.log D / 2 + lρ1)) →
    (∀ a < T - D, ((a + D - 1).choose (D - 1) : ℝ) * δ *
        (-J + ((T : ℝ) - a - D - 3) * η - a * lamb - lA a) ≤ degGr a) →

    0 ≤ rkP → 0 ≤ cor → rkP + cor = d - ((T - 1).choose D : ℝ) * δ →
    -(rkP * (((T : ℝ) - D) * (lβ / 2 + lρ1) + lΛD)) ≤ degP →
    -(cor * lΛT) ≤ degQ →
    (∑ a ∈ range (T - D), degGr a) + degP + degQ ≤ degMT →
    (1 - (1 - ((T - 1).choose D : ℝ) * δ / d)) *
        ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - C0 * (D : ℝ) ^ 2 * (lρ + Real.log T)
          - ((T : ℝ) + D + 1) * lβ - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2))
      - (1 - ((T - 1).choose D : ℝ) * δ / d) *
        ((T : ℝ) * (Real.log 2 + lρ + lβ / 2) + lΛD + lΛT) ≤ degMT / d
def RhoSplit : Prop :=
  ∀ n D j0 δ Λ h C : ℝ, 1 ≤ n → 1 ≤ D → 1 ≤ j0 → 1 ≤ δ → 1 ≤ Λ → 0 ≤ C →
    Real.log Λ + C * Real.log (n * D * j0 * δ * (2 + |h| + Real.log Λ)) ≤
      (Real.log Λ + C * Real.log (n * D * j0 * δ * (1 + Real.log Λ))) + C * Real.log (2 + |h|)
def HSJoint : Prop :=
  ∀ (D T : ℕ) (δ d h J g lamb η lρ1 lρ l0 lβ lΛD lΛT C0 z rkP cor degP degQ degMT : ℝ)
    (lA degGr : ℕ → ℝ),
    1 ≤ D → D + 1 ≤ T → 0 < δ → 0 < d → 0 ≤ g → 0 ≤ lβ → 0 ≤ lΛD → 0 ≤ lΛT → 4 ≤ C0 →
    0 ≤ lρ1 → lρ1 ≤ lρ → Real.log D ≤ lρ → 26 * Real.log 2 ≤ lρ → lamb ≤ lρ1 →
    ((D : ℝ) + 1) * h + D * lamb - g ≤ η → η ≤ ((D : ℝ) + 1) * h + D * lamb →
    (∀ a < T - D, lA a ≤ ((T : ℝ) + D + 1) / 2 * lβ
        + Real.log (34 * (2 ^ (D + 1) * Real.pi ^ D / ((D - 1).factorial : ℝ))
            * ((a + D - 1).choose (D - 1) : ℝ)) / 2
        + D * (Real.log D / 2 + lρ1)) →
    (∀ a < T - D, ((a + D - 1).choose (D - 1) : ℝ) * δ *
        (-J + ((T : ℝ) - a - D - 3) * η - a * lamb - lA a) ≤ degGr a) →
    0 ≤ rkP → 0 ≤ cor → rkP + cor = d - ((T - 1).choose D : ℝ) * δ →
    -(rkP * (((T : ℝ) - D) * (lβ / 2 + lρ1) + lΛD)) ≤ degP →
    -(cor * lΛT) ≤ degQ →
    (∑ a ∈ range (T - D), degGr a) + degP + degQ ≤ degMT →

    1 - ((T - 1).choose D : ℝ) * δ / d ≤ z → z ≤ 1 / 2 →
    lρ ≤ l0 + C0 * Real.log (2 + |h|) → 0 ≤ l0 →
    ((T - 1).choose D : ℝ) * δ *
        ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h|
          - (C0 * (C0 * (D : ℝ) ^ 2 + 2 * z * T)) * Real.log (2 + |h|)
          - (J + C0 * (D : ℝ) ^ 2 * (l0 + Real.log T) + ((T : ℝ) + D + 1) * lβ
              + ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2))
          - 2 * z * ((T : ℝ) * (Real.log 2 + l0 + lβ / 2) + lΛD + lΛT)) ≤ degMT
end Formalism.HermiteSiegelSlopes


