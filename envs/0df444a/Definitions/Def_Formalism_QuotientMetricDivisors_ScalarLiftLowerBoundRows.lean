-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundRows
-- name    : Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundRows
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:33.03303+00:00
-- url     : https://prove2.me/theorems/199a8442-1ef4-46a2-8792-692000235d07
-- title:
--   Scalar Lift Lower Bound Rows
-- statement:
--   Definitions and structural lemmas for Scalar Lift Lower Bound Rows, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/ScalarLiftLowerBoundRows.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField IsDedekindDomain
noncomputable section
namespace Formalism.DivisionValues
def LevelLogs : Prop :=
  ∀ (L b g1 g2 Yg T DF m CY CT : ℝ),
    1 ≤ L → b = Real.exp L →
    0 < g1 → g1 ≤ 2 * Yg → 0 < g2 → g2 ≤ 2 * Yg → Real.log Yg ≤ CY * L →
    0 < T → T ≤ b ^ (CT * m) →
    0 < DF → DF ^ 2 ≤ g1 →
      Real.log (g1 * g2) ≤ (2 * CY + 2) * L ∧ Real.log T ≤ CT * m * L ∧
      Real.log DF ≤ (CY + 1) / 2 * L
def LPrimeBound : Prop :=
  ∀ (x L b a rd La g nV L' Cg Cn : ℝ),
    1 ≤ x → 0 ≤ L → b = Real.exp L → a = x * b → 1 ≤ rd → La = Real.log (a * rd) →
    0 < g → Real.log g ≤ Cg * L → 0 < nV → Real.log nV ≤ Cn * Real.log x → 0 ≤ Cg → 0 ≤ Cn →
    L' = Real.log (b * rd * g * nV) →
      L' ≤ (1 + Cg + Cn) * La ∧ L ≤ La
def ReduceDi : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb]
    (logK mid : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (hK : J → ℝ) (phν nν : J → Pl → ℝ)
    (logOm f m N L La dC logg logT C1 C2 C3 C4 : ℝ),

    (∀ j s, logK j s ≤ (∑ ρ, (phν j ρ - nν j ρ * logOmτ ρ s)) + mid j s +
      C1 * f * m ^ 2 * N ^ 2 * (L + (logg + logT))) →

    (∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ)) →
    (∀ ρ, (∑ s, logOmτ ρ s) / (Fintype.card Emb : ℝ) = logOm) →

    (∀ j, (∑ s, mid j s) / (Fintype.card Emb : ℝ) ≤ C2 * f * N ^ 2 * L) →

    logg ≤ C3 * L → logT ≤ C4 * m * L →
    0 ≤ f → 1 ≤ m → 0 ≤ L → L ≤ La → 0 ≤ dC → 0 ≤ C1 → 0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 →
    ∃ eK : J → ℝ,
      (∀ j, hK j ≤ (∑ ρ, (phν j ρ - nν j ρ * logOm)) + eK j) ∧
      (∀ j, eK j ≤ (C2 + C1 * (1 + C3 + C4)) * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L))
def ScalarLiftLowerBound : Prop :=
  ∀ (J Pl Emb Frm : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Frm]
    [Nonempty Frm]
    (loglam : J → Frm → Emb → ℝ) (Hp Hm : J → Pl → ℕ) (mlam f m nV N L' La C1 C2 : ℝ),

    (∀ j π s, (∑ ρ, Real.log ((Hp j ρ : ℝ) * (Hm j ρ : ℝ))) - C1 * f * nV ^ 2 * L' ≤ loglam j π s) →
    (∀ j ρ, 0 < Hp j ρ) → (∀ j ρ, 0 < Hm j ρ) →
    0 ≤ nV → nV ≤ N → L' ≤ C2 * La → 0 ≤ La → 0 ≤ f → 0 ≤ C1 → 0 ≤ C2 →
    (Fintype.card J : ℝ) = m →
    mlam = (∑ s, Finset.univ.inf' Finset.univ_nonempty (fun π : Frm => ∑ j, loglam j π s)) /
      (Fintype.card Emb : ℝ) →
      (∀ j π s, (∑ ρ, Real.log (Hp j ρ : ℝ)) - C1 * C2 * f * N ^ 2 * La ≤ loglam j π s) ∧
      (∑ j, ∑ ρ, Real.log (Hp j ρ : ℝ)) - C1 * C2 * m * f * N ^ 2 * La ≤ mlam
def PhFactorialOne : Prop :=
  ∀ n : ℕ, 1 ≤ n → Formalism.LatticeIndexTer.ph (n : ℝ) + 1 ≤ Real.log (n.factorial : ℝ)
def HookRowsLower : Prop :=
  ∀ (n : ℕ) (r : Fin n → ℕ) (c' : Fin n → ℝ) (w S sh A logH : ℝ),
    (∑ i, Real.log ((r i).factorial : ℝ)) ≤ logH →
    (∀ i, 1 ≤ w + c' i - sh ∧ w + c' i - sh ≤ (r i : ℝ) ∧ c' i ≤ S) →
    0 ≤ sh → w + S ≤ A →
      (∑ i, (Formalism.LatticeIndexTer.ph (w + c' i) + 1)) - (n : ℝ) * sh * Real.log A ≤ logH
def ScalarLiftLowerBoundRows : Prop :=
  ∀ (J Pl Emb Frm : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Frm]
    [Nonempty Frm] (n : ℕ)
    (loglam : J → Frm → Emb → ℝ) (Hp Hm : J → Pl → ℕ) (r : J → Pl → Fin n → ℕ)
    (c' : J → Pl → Fin n → ℝ) (w : J → Pl → ℝ)
    (mlam f m nV N L' La A Sc cs C1 C2 : ℝ),

    (∀ j π s, (∑ ρ, Real.log ((Hp j ρ : ℝ) * (Hm j ρ : ℝ))) - C1 * f * nV ^ 2 * L' ≤ loglam j π s) →
    (∀ j ρ, 0 < Hp j ρ) → (∀ j ρ, 0 < Hm j ρ) →
    0 ≤ nV → nV ≤ N → L' ≤ C2 * La → 0 ≤ La → 0 ≤ f → 0 ≤ C1 → 0 ≤ C2 →
    (Fintype.card J : ℝ) = m →
    mlam = (∑ s, Finset.univ.inf' Finset.univ_nonempty (fun π : Frm => ∑ j, loglam j π s)) /
      (Fintype.card Emb : ℝ) →

    (∀ j ρ, (∑ i, Real.log ((r j ρ i).factorial : ℝ)) ≤ Real.log (Hp j ρ : ℝ)) →

    (∀ j ρ i, 1 ≤ w j ρ + c' j ρ i - cs * N ∧ w j ρ + c' j ρ i - cs * N ≤ (r j ρ i : ℝ) ∧
      c' j ρ i ≤ Sc) →
    (∀ j ρ, w j ρ + Sc ≤ A) → La = Real.log A → (n : ℝ) ≤ N → (Fintype.card Pl : ℝ) ≤ f → 0 ≤ cs →
      (∑ j, ∑ ρ, ∑ i, (Formalism.LatticeIndexTer.ph (w j ρ + c' j ρ i) + 1)) -
        (C1 * C2 + cs) * m * f * N ^ 2 * La ≤ mlam
def ReduceDiii : Prop :=
  ∀ (Pl Emb : Type) [Fintype Pl] [Fintype Emb] [Nonempty Emb] (TT : Finset Pl)
    [DecidablePred (· ∈ TT)]
    (logP orth : Emb → ℝ) (aT nτ D1 : Pl → ℝ)
    (hP logT La L m f N S η b' C1 C2 C3 C4 : ℝ),

    (∀ s, logP s ≤ -((∑ τ, nτ τ) * logT) + orth s) →
    (∀ s, orth s ≤ C3 * (∑ τ, (N * D1 τ + N ^ 2)) * La) →
    hP = (∑ s, logP s) / (Fintype.card Emb : ℝ) →
    (∀ τ ∈ TT, aT τ - C1 * (b' + S + m * η + N) ≤ nτ τ) →
    (∀ τ, τ ∉ TT → -(C1 * (S + m * η + N)) ≤ nτ τ) →
    (∀ τ, D1 τ ≤ C4 * (S + m * η) + (if τ ∈ TT then C4 * b' else 0)) →

    0 ≤ logT → logT ≤ C2 * m * L → 0 ≤ L → L ≤ La → 0 ≤ m → m ≤ N →
    0 ≤ S → 0 ≤ η → 0 ≤ b' → (Fintype.card Pl : ℝ) ≤ f →
    0 ≤ C1 → 0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 →
      hP ≤ -(∑ t ∈ TT, aT t * logT) +
        (C1 * C2 + C3 * (C4 + 1)) *
          ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La
def PrimeLogSum : Prop :=
  ∀ (Y : ℝ), 1 ≤ Y → ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y + Real.log 4
def PlaceLogSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ell : HeightOneSpectrum (𝓞 K) → ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Y : ℝ), 1 ≤ Y →
    (∀ w ∈ S, (ell w).Prime ∧ ((ell w : ℕ) : 𝓞 K) ∈ w.asIdeal ∧ (ell w : ℝ) ≤ Y) →
      ∑ w ∈ S, lw w * ((vw w ((ell w : ℕ) : K) : ℝ) * (1 / (ell w : ℝ))) ≤ Real.log Y + Real.log 4
def OnCutoff : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ell : HeightOneSpectrum (𝓞 K) → ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x eps L b B0 xe m f k W Sc η w'' DF Cd CD C0 : ℝ),
    (∀ w ∈ S, (ell w).Prime ∧ ((ell w : ℕ) : 𝓞 K) ∈ w.asIdeal ∧ (ell w : ℝ) ≤ Cd * DF) →
    1 ≤ Cd → 1 ≤ DF → Real.log DF ≤ CD * L →
    L = x ^ eps → 1 ≤ L → B0 = f * m * b * x ^ eps →
    1 ≤ m → 0 ≤ f → 1 ≤ k → 0 ≤ W → W ≤ 2 * f * b →
    0 ≤ Sc → 0 ≤ η → k * Sc ≤ w'' → w'' ≤ b → k * η ≤ b → 0 ≤ C0 → Real.log k + 1 ≤ xe →
      ∑ w ∈ S, lw w * ((vw w ((ell w : ℕ) : K) : ℝ) *
          (C0 * Real.log k * m * W / (ell w : ℝ) + C0 * f * k * (Sc + η) / (ell w : ℝ))) ≤
        2 * C0 * (Real.log Cd + CD + Real.log 4) * (Real.log k + 1) * B0 ∧
      ∑ w ∈ S, lw w * ((vw w ((ell w : ℕ) : K) : ℝ) *
          (C0 * Real.log k * m * W / (ell w : ℝ) + C0 * f * k * (Sc + η) / (ell w : ℝ))) ≤
        2 * C0 * (Real.log Cd + CD + Real.log 4) * xe * B0
end Formalism.DivisionValues


