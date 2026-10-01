-- Prove2me | Definitions.Def_ChapterCoherentPositionSpace
-- name    : ChapterCoherentPositionSpace
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T09:43:29.133106+00:00
-- url     : https://prove2.me/theorems/7f04964f-5fb8-413f-bb11-25ed5e168d6b
-- title:
--   Chapter CoherentPositionSpace
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCoherentPositionSpace.lean`): generated def bundle for ChapterCoherentPositionSpace. See BookProof/ChapterCoherentPositionSpace.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCoherentPositionSpace.lean

import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention" — the position-space realization of the
overlap

`ChapterCoherentOverlap` takes the Bargmann–Fock reproducing kernel
`⟨q|k⟩ = exp (-‖q‖²/2 - ‖k‖²/2 + ⟪q,k⟫)` as the *definition* of the coherent-state
overlap.  This module derives the same kernel from the concrete **position-space
wave functions** of the corresponding minimum-uncertainty wave packets, so that
the kernel is no longer a definition but the value of an honest `L²(ℝ)` inner
product.

With `ℏ = m = ω = 1`, the coherent state displaced to the position `a` has the
normalized wave function

  `ψ_a(x) = π^{-1/4} exp (-(x - a)²/2)`,

and the module proves:

* `gaussianPacket_sq_integral` — `∫ ψ_a(x)² dx = 1`: the packet is normalized;
* `gaussianPacket_inner` — **the headline**: `∫ ψ_a(x) ψ_b(x) dx = exp (-(a-b)²/4)`,
  a pure function of the distance between the two packet centres;
* `gaussianPacket_inner_sq_eq_coherentOverlap` — squaring gives the Born
  probability `|⟨ψ_a|ψ_b⟩|² = exp (-(a-b)²/2)`, which is exactly the real
  coherent-overlap kernel of `ChapterCoherentOverlap` at the parameters `a, b`;
* `packetBorn_eq_scoreSoftmax` — consequently the position-space Born weights of a
  query packet against a family of key packets are the Softmax of minus the squared
  distances at inverse temperature `1/2`.

Conventions: the physics parameter of a coherent state is `α = (a + i p)/√2`, so
the fidelity `|⟨α|β⟩|² = exp (-|α - β|²)` becomes `exp (-(a-b)²/2)` in terms of the
positions `a, b` of two zero-momentum packets; this is the convention under which
the real kernel of `ChapterCoherentOverlap` is recovered on the nose.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace BookProof.ChapterCoherentPositionSpace

open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

/-! ## The normalized Gaussian wave packet -/

/-- The normalization constant `π^{-1/4}` of the ground-state wave packet, written
as `1 / √(√π)`. -/
def packetNorm : ℝ := (Real.sqrt (Real.sqrt Real.pi))⁻¹







/-- The **position-space wave function of the coherent state centred at `a`**
(zero momentum), `ψ_a(x) = π^{-1/4} exp (-(x - a)²/2)`. -/
def gaussianPacket (a x : ℝ) : ℝ := packetNorm * Real.exp (-(x - a) ^ 2 / 2)



/-! ## The Gaussian integral -/





/-! ## The overlap of two packets -/











/-! ## Recovering the Bargmann kernel and the Softmax weights -/



/-- The **position-space attention weights**: the Born weight of the key packet
centred at `k j` against the query packet centred at `q`. -/
def packetBorn {m : ℕ} (q : ℝ) (k : Fin m → ℝ) (j : Fin m) : ℝ :=
  (∫ x : ℝ, gaussianPacket q x * gaussianPacket (k j) x) ^ 2 /
    ∑ l, (∫ x : ℝ, gaussianPacket q x * gaussianPacket (k l) x) ^ 2



end BookProof.ChapterCoherentPositionSpace

end


