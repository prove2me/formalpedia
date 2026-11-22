-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
-- name    : Formalism_LogVandermondeBounds_MultinomialPowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:42:11.201807+00:00
-- url     : https://prove2.me/theorems/f41007a0-8b85-4dd4-bf97-5071022a978b
-- title:
--   Multinomial Power Bound
-- statement:
--   Definitions and structural lemmas for Multinomial Power Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/MultinomialPowerBound.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.flipTwoThree
open Finset
def Interlace {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : Prop :=
  Antitone lam ∧ ∀ i : Fin n, lam i.succ ≤ nu i ∧ nu i ≤ lam i.castSucc
def B0 {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : ℤ := ∑ i, (nu i - lam i.succ)
def len {n : ℕ} (lam : Fin (n + 1) → ℤ) (i : Fin n) : ℤ := lam i.castSucc - lam i.succ
noncomputable def Iset {n : ℕ} (lam : Fin (n + 1) → ℤ) (b : ℤ) (i : Fin n) : Finset ℤ :=
  Icc (lam i.succ) (lam i.succ + min (len lam i) b)
def ev {n : ℕ} (nu' : Fin n → ℤ) (x : ℤ) : ℤ := ∏ j, (nu' j - (j : ℤ) - x)
noncomputable def sep {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu nu' : Fin n → ℤ) : ℤ :=
  ∏ i, ∏ y ∈ (Iset lam (B0 lam nu) i).erase (nu i), ev nu' (y - (i : ℤ))
def InterlacingSeparation : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ), Interlace lam nu →
    (∀ nu' : Fin n → ℤ, Interlace lam nu' → B0 lam nu' = B0 lam nu →
      ∀ i, nu' i ∈ Iset lam (B0 lam nu) i) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint ((Iset lam (B0 lam nu) i).image (fun y => y - (i : ℤ)))
      ((Iset lam (B0 lam nu) j).image (fun y => y - (j : ℤ)))) ∧
    sep lam nu nu ≠ 0 ∧
    |sep lam nu nu| ≤ (lam 0 - lam (Fin.last n) + n + 1) ^
      (n * ∑ i, (min (len lam i) (B0 lam nu)).toNat) ∧
    (∀ nu' : Fin n → ℤ, Interlace lam nu' → B0 lam nu' = B0 lam nu → nu' ≠ nu → sep lam nu nu' = 0)
def MinRatioPowerExponentialBound : Prop :=
  ∀ (n g : ℕ), 1 ≤ g →
    let e : ℝ := if n = 0 then 1 else min 1 ((g : ℝ) / n)
    (e ^ g)⁻¹ * (1 + e) ^ (n + g) ≤ (2 * Real.exp 1 * max 1 ((n : ℝ) / g)) ^ g
def GammaIntegralBound : Prop :=
  ∀ (v : ℝ) (g : ℕ), 0 ≤ v →
    MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g) (Set.Ioi 0) ∧
    ∫ u in Set.Ioi (0 : ℝ), Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g ≤
      (1 + 4 * g * v / Real.pi) ^ g
def AmgmSumLowerBoundOfProd : Prop :=
  ∀ (f : ℕ) (v : ℝ) (x : Fin f → ℝ), 1 ≤ f → 0 < v → (∀ i, 0 < x i) →
    ((2 * v) ^ f)⁻¹ ≤ ∏ i, x i → (f : ℝ) / v ≤ 2 * ∑ i, x i
noncomputable def hookF {N : ℕ} (nu : Fin N → ℕ) : ℝ :=
  (∏ i : Fin N, ((nu i + N - 1 - i : ℕ).factorial : ℝ)) /
    ∏ i : Fin N, ∏ j ∈ univ.filter (fun j => i < j), (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ)
def HookProductBounds : Prop :=
  ∀ (N : ℕ) (nu : Fin (N + 1) → ℕ), Antitone nu →
    hookF nu ≤ ∏ i : Fin (N + 1), ((nu i + N - i : ℕ).factorial : ℝ) ∧
    ∑ i : Fin (N + 1), Real.log ((nu i + N - i : ℕ).factorial : ℝ)
        - ((N : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + N + 1) ≤ Real.log (hookF nu) ∧
    hookF nu / ∏ i : Fin (N + 1), ((nu i).factorial : ℝ) ≤ ((nu 0 : ℝ) + N + 1) ^ ((N + 1) ^ 2)
def MultinomialPowerBound : Prop :=
  ∀ (k : ℕ) (α : Fin k → ℕ),
    ((∑ i, α i).factorial : ℝ) / ∏ i, ((α i).factorial : ℝ) ≤ (k : ℝ) ^ (∑ i, α i)
end Formalism.LogVandermondeBounds.flipTwoThree


