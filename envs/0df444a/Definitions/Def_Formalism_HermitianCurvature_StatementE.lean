-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementE
-- name    : Formalism_HermitianCurvature_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:49.996907+00:00
-- url     : https://prove2.me/theorems/ffe74ed0-22df-48e9-b5ce-435c60bb7dd7
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementE.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.E
open Real Polynomial MeasureTheory
def MiddleThird : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (α β Y : ℝ), 12 ≤ β - α → (∀ s, -lam s ∉ Set.Ioo α β) →
    α + (β - α) / 3 ≤ Y → Y ≤ β - (β - α) / 3 →
    |(∏ s, (Y + 1 + lam s)) / ∏ s, (Y + lam s)| ≤ Real.exp (3 * n / (β - α)) ∧
    |(∏ s, (Y + lam s)) / ∏ s, (Y + 1 + lam s)| ≤ Real.exp (4 * n / (β - α))
def CauchyTheta : Prop :=
  ∀ (σ ε : ℝ), 4 ≤ σ → 0 < ε → ∀ (p : ℕ) (u : ℝ),
    |iteratedDeriv p (fun v : ℝ => (1 + ε * Real.exp (-v)) ^ (-σ)) u| ≤
      Real.exp 1 * p.factorial * (4 * σ) ^ p * (1 + ε * Real.exp (-u)) ^ (-σ)
def AMarkov : Prop :=
  ∀ (p : ℝ[X]) (d : ℕ) (M : ℝ), p.natDegree ≤ d → (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) →
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (d : ℝ) ^ 2 * M
def MarkovVector : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (d : ℕ) (a : Fin (d + 1) → H)
    (t₀ L M : ℝ), 0 < L →
    (∀ t ∈ Set.Icc t₀ (t₀ + L), ‖∑ k : Fin (d + 1), t ^ (k : ℕ) • a k‖ ≤ M) →
    ∀ (q : ℕ), ∀ t ∈ Set.Icc t₀ (t₀ + L),
      ‖iteratedDeriv q (fun s : ℝ => ∑ k : Fin (d + 1), s ^ (k : ℕ) • a k) t‖ ≤ (2 * (d : ℝ) ^ 2 / L) ^ q * M
def Bdd {Λ : Type} (f : Λ → ℂ) : Prop := ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B
def MeanPosDef : Prop :=
  ∀ (Λ : Type) [AddCommGroup Λ] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (LIM : (Λ → ℂ) → ℂ),
    (∀ f g, Bdd f → Bdd g → LIM (f + g) = LIM f + LIM g) →
    (∀ (c : ℂ) f, Bdd f → LIM (c • f) = c * LIM f) →
    (∀ f, Bdd f → (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) → 0 ≤ (LIM f).re) →
    (∀ f (σ : Λ), Bdd f → LIM (fun x => f (x + σ)) = LIM f) →
    ∀ (u : Λ → H) (B : ℝ), (∀ x, ‖u x‖ ≤ B) → ∀ (S : Finset Λ) (c : Λ → ℂ),
      0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S,
        LIM (fun x => inner ℂ (u x) (u (x + (σ - σ')))) * c σ * starRingEnd ℂ (c σ')).re
def HerglotzLSC : Prop :=
  ∀ (d : ℕ) (N : (Fin d → ℝ) → ℝ) (A : (Fin d → ℤ) → ℂ),
    (∀ z, 0 ≤ N z) → LowerSemicontinuous N → Integrable N →
    (∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re) →
    Summable (fun σ : Fin d → ℤ =>
      ‖(∫ z, (N z : ℂ) * Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (z j : ℂ))) + A σ‖) →
    ∀ (z₀ : Fin d → ℝ) (S : Finset (Fin d → ℤ)),
      ∑ m ∈ S, N (fun j => z₀ j + (m j : ℝ)) ≤
        ∑' σ : Fin d → ℤ,
          ‖(∫ z, (N z : ℂ) * Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (z j : ℂ))) + A σ‖
end Formalism.FourierDecayAlt.E


