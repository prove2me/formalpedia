-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_StretchedExponentialDominance
-- name    : Formalism_PadicSubsetSums_CentralIdempotents_StretchedExponentialDominance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:36.551627+00:00
-- url     : https://prove2.me/theorems/b76e065d-3e0d-4bfa-ad5c-c9a9b54287b7
-- title:
--   Stretched Exponential Dominance
-- statement:
--   Definitions and structural lemmas for Stretched Exponential Dominance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/StretchedExponentialDominance.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
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
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
def StretchedExponentialDominance : Prop :=
  ∀ C ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
    x ^ C * Real.exp (-x ^ (ε / 6)) ≤ 1 / 20 * Real.exp (-x ^ (ε / 7))
def SubsetSumCountReformulated : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (deg : ι → ℕ) (i : ℕ), (∀ c, 1 ≤ deg c) →
    ((Finset.univ : Finset ι).powerset.filter (fun I => ∑ c ∈ I, deg c = i)).card
      ≤ (∑ c, deg c).choose i
def TorusCountBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (deg : ι → ℕ) (g k : ℕ) (c : ℕ → ℝ) (n : ℝ),
    (∀ x, 1 ≤ deg x) → 1 ≤ g → 1 ≤ k →
    (∀ i, c i = (((Finset.univ : Finset ι).powerset.filter
      (fun I => ∑ x ∈ I, deg x = i)).card : ℝ)) →
    n = (∑ i ∈ Finset.range k, c i * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + c k →
    (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) ≤ n ∧
      n ≤ (g : ℝ) ^ k * (1 + 1 / (g : ℝ)) ^ (∑ x, deg x)
def TorusWeightArithmetic : Prop :=
  ∀ (d : Multiset ℕ) (g k : ℕ) (n : ℝ), (∀ x ∈ d, 1 ≤ x) → 2 ≤ g → 1 ≤ k → k + 1 ≤ d.sum →
    2 * d.sum ≤ g → (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) ≤ n →
    n ≤ (g : ℝ) ^ k * (1 + 1 / (g : ℝ)) ^ d.sum →
    (1 - 1 / (g : ℝ)) / (g : ℝ) ^ d.sum ≤
        n / ((g : ℝ) ^ k * (d.map (fun x => (g : ℝ) ^ x - 1)).prod) ∧
      n / ((g : ℝ) ^ k * (d.map (fun x => (g : ℝ) ^ x - 1)).prod) ≤
        (1 + 6 * (d.sum : ℝ) / g) / (g : ℝ) ^ d.sum
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


