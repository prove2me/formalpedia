-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_IsStronglyStable
-- name    : CrossLayerControl_ECCA_IsStronglyStable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:48:52.791646+00:00
-- url     : https://prove2.me/theorems/169259fd-abb7-4b44-8d14-d99d48d7a97f
-- title:
--   Strong stability of a queue (Definition 3.1)
-- statement:
--   A queue with backlog $U(t)$ is strongly stable if
--   $$\limsup_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\mathbb E\{U(\tau)\}<\infty.$$
--
--   This is the paper's notion of stability throughout.
--
--   **Formalization Note** The $\limsup$ is taken in the extended reals, so unbounded averages give $+\infty$.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Definition 3.1, p. 24

import Mathlib

open MeasureTheory Filter

namespace CrossLayerControl.ECCA

/-- **Strong stability of a queue, Definition 3.1.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Definition 3.1, p. 24: "A queue is called strongly stable if:
limsup_{t→∞} (1/t) Σ_{τ=0}^{t−1} E{U(τ)} < ∞."

For a backlog process `U τ ω` on `(Ω, Pr)`, `IsStronglyStable Pr U` asserts
`limsup_{t→∞} (1/t) Σ_{τ<t} E[U(τ)] < +∞`.

**Formalization Note.** The `limsup` is taken in `EReal` (extended reals), so an unbounded sequence
of averages has `limsup = +∞` and is correctly not strongly stable; a real-valued `limsup` would
return a junk value there. -/
def IsStronglyStable {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) (U : ℕ → Ω → ℝ) : Prop :=
  limsup (fun t : ℕ => (((t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, U τ ω ∂Pr : ℝ) : EReal)) atTop < ⊤

end CrossLayerControl.ECCA


