-- Prove2me | Definitions.Def_TeschlODE_HigherDim_IsTrappingRegion
-- name    : TeschlODE_HigherDim_IsTrappingRegion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:23:24.127104+00:00
-- url     : https://prove2.me/theorems/8f4744c8-5327-458c-a1e0-066e08672d37
-- title:
--   Trapping region — open connected $E$, $\overline E$ compact, $\Phi_t(\overline E) \subset E$ for $t > 0$
-- statement:
--   Let $\Phi$ be a flow on $M$ with maximal intervals $I_x$. An open connected set $E$ whose closure $\overline{E}$ is compact is called a **trapping region** for the flow if
--   $$\Phi_t(\overline{E}) \subset E \qquad \text{for all } t > 0 .$$
--
--   **Formalization Note.** For the local flow, $\Phi_t(\overline E)$ is only defined if $\overline E \subseteq M$ and every $x \in \overline E$ is alive at time $t$; both are part of the definition ($\overline E \subseteq M$, and $t \in I_x$, $\Phi(t, x) \in E$ for all $x \in \overline E$, $t > 0$). Mathlib's `IsConnected` includes nonemptiness, which the book's Lemma 8.5 needs ($\Lambda$ nonempty).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 232, §8.1, definition of a trapping region

import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.1, p. 232: a trapping region for the flow is an open connected set `E` whose
closure is compact (and contained in the phase space `M`, where the flow lives) with
`Φ_t(Ē) ⊂ E` for all `t > 0`: every `x ∈ Ē` has `t ∈ I x` and `Φ t x ∈ E` for all `t > 0`.
`IsConnected` includes nonemptiness. -/
def IsTrappingRegion {X : Type*} [NormedAddCommGroup X] (M : Set X) (I : X → Set ℝ)
    (Φ : ℝ → X → X) (E : Set X) : Prop :=
  IsOpen E ∧ IsConnected E ∧ IsCompact (closure E) ∧ closure E ⊆ M ∧
    ∀ x ∈ closure E, ∀ t : ℝ, 0 < t → t ∈ I x ∧ Φ t x ∈ E

end TeschlODE.HigherDim


