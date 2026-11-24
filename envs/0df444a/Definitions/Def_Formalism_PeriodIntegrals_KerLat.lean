-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_KerLat
-- name    : Formalism_PeriodIntegrals_KerLat
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:10:29.794869+00:00
-- url     : https://prove2.me/theorems/016740fd-5594-4d2b-96a7-a11ea3f4647c
-- title:
--   Ker Lat
-- statement:
--   Definitions and structural lemmas for Ker Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/KerLat.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace PI.KerLat
def PerPair : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Module.finrank ℚ K = 2 → (∃ k : K, (φ k).im ≠ 0) → cc ≠ ⊥ → δ ≠ 0 →
      ∃ L : PeriodPair, L.lattice.toAddSubgroup = AddSubgroup.closure {w : ℂ | ∃ c ∈ cc, w = δ * φ (c : K)}
def ExistsTwoTorsionOffKernels : Prop :=
  ∀ (L : PeriodPair) (d : ℕ), d % 8 = 7 →
    (∀ w ∈ L.lattice, ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * w ∈ L.lattice) →
      ∃ t : ℂ, 2 * t ∈ L.lattice ∧ ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ L.lattice ∧
        ((1 - Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ L.lattice
end PI.KerLat


