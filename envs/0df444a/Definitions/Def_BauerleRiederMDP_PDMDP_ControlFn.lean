-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn
-- name    : BauerleRiederMDP_PDMDP_ControlFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:10.963806+00:00
-- url     : https://prove2.me/theorems/ba339251-4612-4b78-ad52-e52eb5e56b58
-- title:
--   Control functions $A$ and their σ-algebra (8.1)
-- statement:
--   The set of **control functions** is $A:=\{\alpha:\mathbb R_+\to U\text{ measurable}\}$. It carries the coarsest σ-algebra such that
--   $$
--   \alpha\mapsto\int_0^\infty e^{-t}\,w(t,\alpha_t)\,dt
--   $$
--   is measurable for all bounded and measurable $w:\mathbb R_+\times U\to\mathbb R$.
--
--   In the embedded discrete-time model of a Piecewise Deterministic Markov Decision Process, $A$ is the action space: at a jump time the decision maker fixes the whole control function up to the next jump.
--
--   **Formalization Note** Time is `ℝ`, and every object of the mission reads $\alpha$ on $t\ge0$ only.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (8.1) and the σ-algebra of A, p.244

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.PDMDP

/-- The set of **control functions** `A := {α : ℝ₊ → U measurable}` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (8.1), p.244,
PDF 255).

**Formalization Note** Time is `ℝ`; every object of the chapter reads `α` on `t ≥ 0` only, so the
values at negative times carry no information. -/
def ControlFn (U : Type*) [MeasurableSpace U] : Type _ := {α : ℝ → U // Measurable α}

/-- The σ-algebra of `A` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.244, PDF 255): the coarsest σ-algebra such that
`α ↦ ∫_0^∞ e^{-t} w(t, α_t) dt` is measurable for all bounded and measurable
`w : ℝ₊ × U → ℝ`. -/
noncomputable instance instMeasurableSpaceControlFn (U : Type*) [MeasurableSpace U] :
    MeasurableSpace (ControlFn U) :=
  ⨆ w : {w : ℝ × U → ℝ // Measurable w ∧ ∃ C : ℝ, ∀ p, |w p| ≤ C},
    MeasurableSpace.comap
      (fun α : ControlFn U => ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * w.1 (t, α.1 t))
      inferInstance

end BauerleRiederMDP.PDMDP


