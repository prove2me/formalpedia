-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_StatementC
-- name    : Formalism_ThetaSupremumBounds_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:44.544349+00:00
-- url     : https://prove2.me/theorems/96dbab74-b2a6-4f7d-9f0d-30333ea30d52
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/StatementC.lean

import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
noncomputable section
namespace Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
def SizeAtEmbedding : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (r g0 : ℕ) (ν : Pl → Fin r → ℝ) (n : Pl → ℕ) (Om : Pl → ℝ)
    (Ksq kc Msq Th0sq hh : ℝ),
    0 < Ksq → 0 < kc → 0 < Msq → 0 < Th0sq → 0 < hh → (∀ τ, 0 < Om τ) →
    Ksq ≤ hh * ((kc ^ 2 * Msq * Th0sq) * ∏ τ, ((Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i))))) →
    Real.log Ksq ≤ (∑ τ, ((∑ i, ph (ν τ i)) - (n τ : ℝ) * Real.log (Om τ))) + Real.log Th0sq +
      (Real.log Msq + 2 * Real.log kc + (∑ τ, (1 + 2 * (g0 : ℝ) * Real.log (2 * (n τ : ℝ) + 2))) +
        Real.log hh)
def DiHyp (J Pl : Type) [Fintype J] [Fintype Pl] (hK eK : J → ℝ) (phν nν : J → Pl → ℝ)
    (logOm f m N L La dC C0 : ℝ) : Prop :=
  (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) ∧
  (∀ j, eK j ≤ C0 * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L))
def DiCondition : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' hK : J → ℝ)
    (logOm v f m N L La dC logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),

    (∀ j s, logK j s ≤
      (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s +
      ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * MainNotions j s + (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) +
        (logh j + logh' j))) →

    (∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ)) →

    (∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm) →

    (∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →

    (Fintype.card Pl : ℝ) ≤ f → (∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ dC →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) ≤ C0 →
    ∃ eK : J → ℝ,
      DiHyp J Pl hK eK (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i)
        logOm f m N L La dC C0
def MsqBound : Prop :=
  ∀ (g : ℕ) (h v : ℝ), 0 < v → 1 / v ≤ h →
    (4 : ℝ) ^ g * (2 + 8 * (g : ℝ) / h) ^ g ≤ (8 + 32 * (g : ℝ) * v) ^ g
def StepDiProd : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (n : J → Pl → ℕ) (g0 : J → ℕ)
    (Ksq kc : J → Emb → ℝ) (Om : Pl → Emb → ℝ) (th0sq : Emb → ℝ) (hcl hcl' hK : J → ℝ)
    (logOm v f m N L La dC logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),
    (∀ j τ, ∑ i, ν j τ i = (n j τ : ℝ)) →
    (∀ j s, 0 < Ksq j s) → (∀ j s, 0 < kc j s) → (∀ τ s, 0 < Om τ s) → (∀ s, 0 < th0sq s) →
    (∀ j, 0 < hcl j) → (∀ j, 0 < hcl' j) → 0 < v →

    (∀ j s, Ksq j s ≤ (hcl j * hcl' j) *
      ((kc j s ^ 2 * (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j) *
          th0sq s ^ (Fintype.card Pl * g0 j)) *
        ∏ τ, ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i)))))) →
    (∀ j, hK j = (∑ s, Real.log (Ksq j s)) / (Fintype.card Emb : ℝ)) →
    (∀ τ, (∑ s, Real.log (Om τ s)) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j s, Real.log (kc j s) ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, Real.log (th0sq s)) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, Real.log (hcl j) ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, Real.log (hcl' j) ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (Fintype.card Pl : ℝ) ≤ f → (∀ j, (g0 j : ℝ) ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ dC →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (n j τ : ℝ) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) ≤ C0 →
    ∃ eK : J → ℝ,
      DiHyp J Pl hK eK (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i)
        logOm f m N L La dC C0
def PeriodValue : Prop :=
  ∀ d v rdE A1 Z LL0 p_power_smul_sub_sum logOmK logOm : ℝ, 0 < d → 0 < v → rdE = 2 * v →
    Z = Real.log (2 / Real.sqrt d) + (A1 + Real.log π) →
    Z = Real.log (2 * π) + LL0 →
    LL0 = -p_power_smul_sub_sum - Real.log (d / π) + Real.eulerMascheroniConstant + Real.log 2 →
    logOmK = A1 →
    logOm = logOmK - Real.log rdE + Real.log (Real.sqrt d) →
    A1 = LL0 + Real.log d / 2 ∧
    logOmK = Real.eulerMascheroniConstant + Real.log (2 * π / Real.sqrt d) - p_power_smul_sub_sum ∧
    logOm = Real.eulerMascheroniConstant + Real.log (π / v) - p_power_smul_sub_sum
end Formalism.DimensionVariation


