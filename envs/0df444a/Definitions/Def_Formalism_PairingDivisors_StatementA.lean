-- Prove2me | Definitions.Def_Formalism_PairingDivisors_StatementA
-- name    : Formalism_PairingDivisors_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:41.524118+00:00
-- url     : https://prove2.me/theorems/18066f39-7ca8-4f9d-ae92-81a59774f272
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/StatementA.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
noncomputable section
namespace Formalism.PairingDivisionLocalBalance
def ValAdd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (a b : K),
    a ≠ 0 → b ≠ 0 → a + b ≠ 0 → min (vw w a) (vw w b) ≤ vw w (a + b)
def CharSumVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (ι : Type) [Fintype ι]
    (a ζ : ι → K) (N : ℝ),
    (∀ i, ∃ n : ℕ, 0 < n ∧ ζ i ^ n = 1) →
    (∀ i, a i = 0 ∨ -N ≤ (vw w (a i) : ℝ)) →
    (∑ i, a i * ζ i = 0 ∨ -N ≤ (vw w (∑ i, a i * ζ i) : ℝ))
def eq {k : Type} [Field k] (q : ℕ) (s : ℕ) (Y : k) : k :=
  (1 - Y * ((q : k) ^ s)⁻¹) * (1 - Y⁻¹ * ((q : k) ^ s)⁻¹) + ((q : k) - 1) * (((q : k) ^ s)⁻¹) ^ 2
def EqLocal : Prop :=
  ∀ (q s : ℕ) (Y : ℂ), 2 ≤ q → 1 ≤ s → ‖Y‖ = 1 →
    Summable (fun p : ℕ × ℕ =>
      (Y * ((q : ℂ) ^ s)⁻¹) ^ (p.1 + 1) * (Y⁻¹ * ((q : ℂ) ^ s)⁻¹) ^ (p.2 + 1)) ∧
    1 + ((q : ℂ) - 1) * ∑' p : ℕ × ℕ,
      (Y * ((q : ℂ) ^ s)⁻¹) ^ (p.1 + 1) * (Y⁻¹ * ((q : ℂ) ^ s)⁻¹) ^ (p.2 + 1) =
      eq q s Y * ((1 - Y * ((q : ℂ) ^ s)⁻¹)⁻¹ * (1 - Y⁻¹ * ((q : ℂ) ^ s)⁻¹)⁻¹)
def EqSymm : Prop :=
  ∀ (k : Type) [Field k] (q s : ℕ) (Y : k), Y ≠ 0 →
    eq q s Y = eq q s Y⁻¹ ∧
    eq q s Y = 1 - (Y + Y⁻¹) * ((q : k) ^ s)⁻¹ + (q : k) * (((q : k) ^ s)⁻¹) ^ 2
def EqIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (q s : ℕ) (Y : K),
    1 ≤ q → Y ≠ 0 → vw w (q : K) = 0 → vw w Y = 0 →
    (eq q s Y = 0 ∨ 0 ≤ vw w (eq q s Y))
def RemoveQ : Prop :=
  ∀ (k : Type) [Field k] (P : Type) [DecidableEq P] (Q : Finset P) (unr : P → Prop) [DecidablePred unr]
    (val : Finset P → k) (c Lval : k) (e : P → k) (q1 : P),
    (∀ Q' ⊆ Q, val Q' = c * Lval * ∏ q ∈ Q'.filter unr, e q) → q1 ∈ Q → unr q1 →
    val Q = e q1 * val (Q.erase q1)
def UpperStays : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (P : Type) (R : Finset P)
    (y y' : K) (e : P → K) (B : ℝ),
    y ≠ 0 → y = y' * ∏ q ∈ R, e q → (∀ q ∈ R, 0 ≤ vw w (e q)) → (vw w y : ℝ) ≤ B →
    (vw w y' : ℝ) ≤ B
def GaussUnit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (G G' : 𝓞 K) (q : ℕ),
    1 ≤ q → (G : K) * (G' : K) = (q : K) → vw w (q : K) = 0 → vw w (G : K) = 0
def RatioVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (a a' : K) (g : ℤ),
    a ≠ 0 → a' ≠ 0 → vw w (a / a') = (vw w a + g) - (vw w a' + g)
end Formalism.PairingDivisionLocalBalance


