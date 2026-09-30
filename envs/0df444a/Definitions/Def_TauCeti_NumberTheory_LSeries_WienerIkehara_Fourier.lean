-- Prove2me | Definitions.Def_TauCeti_NumberTheory_LSeries_WienerIkehara_Fourier
-- name    : TauCeti_NumberTheory_LSeries_WienerIkehara_Fourier
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:45:22.831097+00:00
-- url     : https://prove2.me/theorems/a96c0b4d-3e00-4d44-83c3-9ec7647fc5fb
-- title:
--   Borel measurable structure on the complex unit circle
-- statement:
--   Let $\mathbb T$ be the complex unit circle with the topology inherited from $\mathbb C$:
--
--   $$
--   \mathbb T=\{z\in\mathbb C:|z|=1\}.
--   $$
--
--   Equip $\mathbb T$ with its Borel sigma-algebra. The measurable-space structure is the one inherited by this subtype of $\mathbb C$, and its Borel-space instance records agreement with the given topology.
--
--   These foundational instances provide the measurable setting for the circle-valued Fourier characters used in the Wiener–Ikehara argument. The Fourier identities themselves are separate theorem nodes.
--
--   These declarations reuse the source of the **Tau Ceti contributors**, [at the original module](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Fourier.lean), licensed under Apache 2.0 (commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Fourier.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.Deriv

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Fourier identities for Wiener--Ikehara

The Fourier proof of Wiener--Ikehara starts by testing a Dirichlet series against an integrable
function on a vertical line. This file records the two exact identities used in that step. The
first exchanges the Dirichlet series with the integral. The second computes the contribution of
the simple pole at `s = 1`. Their combination expresses the difference as the integral of the
pole-subtracted remainder, a function agreeing with `LSeries a - A / (s - 1)` on the open
vertical line `Re s = sigma`; nothing about its boundary behaviour is asserted or used here.

## Main results

* `TauCeti.LSeries.tsum_term_mul_fourier_eq_integral` is the Fourier identity for a
  convergent Dirichlet series.
* `TauCeti.LSeries.integral_exp_mul_fourier_eq` computes the pole term.
* `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral` combines the two when a named
  function agrees with the pole-subtracted remainder on the vertical line.

## Provenance

The proofs are adapted from `PrimeNumberTheoremAnd/Wiener.lean` in the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`. The source declarations are `first_fourier`,
`second_fourier`, and `limiting_fourier_aux`. The statements here use Mathlib's
`LSeriesSummable` directly, remove the source project's local `nterm` wrapper, and rely on
Mathlib's APIs together with the local vertical-line continuity theorem
`TauCeti.LSeries.continuous_LSeries_vertical`.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

 section

namespace TauCeti.LSeries

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexConjugate Real Topology

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {x sigma t : ℝ}

private instance : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

private instance : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)











/-! ### The simple-pole term -/









/-! ### Subtracting the pole -/



end TauCeti.LSeries

end
end


