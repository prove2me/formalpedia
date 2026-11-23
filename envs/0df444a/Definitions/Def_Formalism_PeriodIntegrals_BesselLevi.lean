-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
-- name    : Formalism_PeriodIntegrals_BesselLevi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:24.673034+00:00
-- url     : https://prove2.me/theorems/76224d88-b16b-4eb5-bfd6-7c7052c0bcd4
-- title:
--   Bessel Levi
-- statement:
--   Definitions and structural lemmas for Bessel Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/BesselLevi.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.QuantumDeterminants
namespace PI.BesselLevi
def BesselLevi : Prop :=
  ∀ (k r : ℕ) (T : ℝ), 0 < T → ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
    s ∈ UH (Hpk k r) →
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0) →
    (∀ i : Fin (2 * r + k + 1), r ≤ i.val →
      (s *ᵥ (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))) i =
        (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) i) →
    s ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))
end PI.BesselLevi


