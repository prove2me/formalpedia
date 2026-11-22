-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
-- name    : Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:43:21.615995+00:00
-- url     : https://prove2.me/theorems/1cf4bd40-aa65-4b7d-85f4-abc41fb23747
-- title:
--   Local Conditions Global Form
-- statement:
--   Definitions and structural lemmas for Local Conditions Global Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LocalConditionsGlobalForm.lean

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
def OnExport2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ), 0 < D →
  ∀ (Tup : Type) (μ : HeightOneSpectrum (𝓞 K) → Tup) (J : Type) [Fintype J] (d : J → ℕ),
    (∀ j, d j = D) →
  ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K))
    (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K))
    (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e0 r0 ε0 F0 errl Jx : HeightOneSpectrum (𝓞 K) → J → ℝ)
    (vU0 gq : HeightOneSpectrum (𝓞 K) → ℝ) (dK EA Rb EJ : J → ℝ) (δq E3 : ℝ), 0 < δq →
    (∀ w ∈ S, ∀ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) ≤
      (ramw w : ℝ) * ((e0 w j + vU0 w) * (d j : ℝ) + (r0 w j + dK j * vU0 w) / δq + ε0 w j)) →
    (∀ w ∈ S, ∀ j, (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) ≤
      (ramw (conjPl w) : ℝ) * ((e0 (conjPl w) j + vU0 (conjPl w)) * (d j : ℝ) +
        (r0 (conjPl w) j + dK j * vU0 (conjPl w)) / δq + ε0 (conjPl w) j)) →
    (∀ j, dK j / δq ≤ 3 * (D : ℝ)) →
    (∀ w ∈ S, 0 ≤ vU0 w ∧ vU0 (conjPl w) = vU0 w ∧ 4 * vU0 w ≤ gq w) →
    (∀ w ∈ S, ∀ j, e0 w j + e0 (conjPl w) j - 2 * F0 w j + 2 * gq w ≤ errl w j) →
    (∀ w ∈ S, ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2) →
    (∀ j, ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w j) ≤ EA j) →
    (∀ j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ w ∈ S', lw w * ((ramw w : ℝ) * r0 w j) ≤ Rb j) →
    (∀ j, ∑ w ∈ S, lw w * Jx w j ≤ EJ j) →
    ∑ w ∈ S, lw w * ((ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)) ≤ E3 →
      (∀ w ∈ S, ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
        (∑ j, (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)))) +
          2 / ellw w ^ 2) * D) ∧
      (∀ j, ∑ w ∈ S, lw w * ((ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))) +
          Jx w j) ≤ EA j + 2 * Rb j / (δq * (D : ℝ)) + EJ j) ∧
      ∑ w ∈ S, lw w * (2 / ellw w ^ 2) ≤ E3
end Formalism.EigenvalueLevelCeiling


