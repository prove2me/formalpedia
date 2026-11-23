-- Prove2me | Definitions.Def_Formalism_PairingDivisors_StatementX
-- name    : Formalism_PairingDivisors_StatementX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:30.591905+00:00
-- url     : https://prove2.me/theorems/e9eb8b8e-49f2-4bbe-bd07-1aad2413d828
-- title:
--   Statement X
-- statement:
--   Definitions and structural lemmas for Statement X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/StatementX.lean

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
def HtLe {K : Type} [Field K] [NumberField K] [StarRing K] (g : Pl K → ℤ) (z : K) (B : ℝ) : Prop :=
  (Function.support fun w : Pl K => lw w * |((vw w z + g w : ℤ) : ℝ)|).Finite ∧
  ∑ᶠ w : Pl K, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ B
def cmFactor {K : Type} [Field K] {I : Type} [Fintype I] (al : I → Bool) (x u y : I → K) : K :=
  ∏ i, (if al i then u i * y i / x i else (u i * y i / x i)⁻¹)
def CMFactorBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (I : Type) [Fintype I] (al : I → Bool) (T : Finset (Pl K)) (g : I → Pl K → ℤ)
    (x x1 x2 : I → K) (y u : Pl K → I → K) (ch : Pl K → Bool)
    (S Se : Finset ℕ) (N0 : I → ℕ → ℝ) (ep : ℕ → ℝ) (B : I → ℝ),
    (∀ i, x i ≠ 0 ∧ x1 i ≠ 0 ∧ x2 i ≠ 0) → (∀ w i, y w i ≠ 0 ∧ u w i ≠ 0) →

    (∀ i, HtLe (g i) (x i) (B i) ∧ HtLe (g i) (x1 i) (B i) ∧ HtLe (g i) (x2 i) (B i)) →

    (∀ i, ∀ l ∈ S, 0 ≤ N0 i l) → (∀ l ∈ Se, 0 ≤ ep l) →

    (∀ w ∈ T, ∀ i, vw w (u w i) = 0) →

    (∀ w ∈ T, ∀ i, - wt S (N0 i) w ≤ ((vw w (y w i) + g i w : ℤ) : ℝ) ∧
      ((vw w (y w i) + g i w : ℤ) : ℝ) ≤
        ((vw w (if ch w then x1 i else x2 i) + g i w : ℤ) : ℝ) + wt Se ep w) →
    (∀ w ∈ T, (vw w (cmFactor al x (u w) (y w)) : ℝ) ≤
      ∑ i, (|((vw w (x i) + g i w : ℤ) : ℝ)| + |((vw w (x1 i) + g i w : ℤ) : ℝ)|
          + |((vw w (x2 i) + g i w : ℤ) : ℝ)|)
        + ∑ i, (wt S (N0 i) w + wt Se ep w)) ∧
    ∑ w ∈ T, lw w * (vw w (cmFactor al x (u w) (y w)) : ℝ) ≤
      ∑ i, (3 * B i + ∑ l ∈ S, N0 i l * Real.log l)
        + (Fintype.card I : ℝ) * ∑ l ∈ Se, ep l * Real.log l
def Export : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (I : Type) [Fintype I] (al : I → Bool) (T : Finset (Pl K)) (g : I → Pl K → ℤ)
    (x x1 x2 : I → K) (y u : Pl K → I → K) (ch : Pl K → Bool)
    (S Se : Finset ℕ) (N0 : I → ℕ → ℝ) (B : I → ℝ) (nI f b L xx CB CN : ℝ),
    (∀ i, x i ≠ 0 ∧ x1 i ≠ 0 ∧ x2 i ≠ 0) → (∀ w i, y w i ≠ 0 ∧ u w i ≠ 0) →
    (∀ i, HtLe (g i) (x i) (B i) ∧ HtLe (g i) (x1 i) (B i) ∧ HtLe (g i) (x2 i) (B i)) →
    (∀ i, ∀ l ∈ S, 0 ≤ N0 i l) → (∀ l ∈ Se, l.Prime) →
    (∀ w ∈ T, ∀ i, vw w (u w i) = 0) →
    (∀ w ∈ T, ∀ i, - wt S (N0 i) w ≤ ((vw w (y w i) + g i w : ℤ) : ℝ) ∧
      ((vw w (y w i) + g i w : ℤ) : ℝ) ≤
        ((vw w (if ch w then x1 i else x2 i) + g i w : ℤ) : ℝ)
          + wt Se (fun l => 1 / (l : ℝ) ^ 2) w) →

    0 ≤ f → 0 ≤ b → 0 ≤ L → 1 ≤ xx → 0 ≤ CB → 0 ≤ CN →
    (Fintype.card I : ℝ) ≤ nI →
    (∀ i, B i ≤ CB * f * b * (L + Real.log xx)) →
    (∀ i, ∑ l ∈ S, N0 i l * Real.log l ≤ CN * f * b * (L + Real.log xx)) →
    ∑ w ∈ T, lw w * (vw w (cmFactor al x (u w) (y w)) : ℝ) ≤
      nI * ((3 * CB + CN) * f * b * (L + Real.log xx) + 1)
end Formalism.PairingDivisionLocalBalance


