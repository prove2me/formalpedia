-- Prove2me | Definitions.Def_BreakingSample_Perturbed_Absorbing
-- name    : BreakingSample_Perturbed_Absorbing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:04.597519+00:00
-- url     : https://prove2.me/theorems/0f9b86e0-79f1-42ec-902a-0e9bfdc3dc23
-- title:
--   (39), (41), and (42) — state-action absorbing MDP and separation net
-- statement:
--   For a designated state-action pair $(s,a)$ and real number $u$, the absorbing MDP replaces only the transition row at $(s,a)$ by a point mass at $s$ and replaces only its reward by $u$. All other transitions and rewards remain those of the original MDP. The module also defines the finite grid $\mathcal N_\eta$ of display (42) and the event $B_\omega$ that one action at every state exceeds every other action in optimal $Q$ value by at least $\omega$:
--
--   $$B_\omega:\quad \forall s\;\exists a_0\;\forall a\ne a_0,\quad Q^\star(s,a_0)-Q^\star(s,a)\ge\omega.$$
--
--   These objects make the leave-one-row-out and policy-separation lemmas precise.
--
--   **Formalization Note** When $\omega>0$, the witnessing action is the unique maximizer, as in the paper's event involving its chosen optimal policy.
-- source:
--   arXiv:2005.12900v8, (39), p. 15; (41)–(42), p. 16

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model

namespace BreakingSample.Perturbed

/-- The kernel of the (s,a)-absorbing MDP `M_{s,a,u}` of (39), arXiv:2005.12900v8, p. 15: the row `(s,a)`
becomes the point mass at `s`; every other row is that of `P`. -/
def absorbKernel {S A : Type*} [DecidableEq S] [DecidableEq A] (P : S → A → S → ℝ) (s : S) (a : A) :
    S → A → S → ℝ :=
  fun s₁ a₁ s₂ => if s₁ = s ∧ a₁ = a then (if s₂ = s then 1 else 0) else P s₁ a₁ s₂

/-- The reward of `M_{s,a,u}` (p. 15): `u` at `(s,a)`, unchanged elsewhere. -/
def absorbReward {S A : Type*} [DecidableEq S] [DecidableEq A] (r : S → A → ℝ) (s : S) (a : A)
    (u : ℝ) : S → A → ℝ :=
  fun s₁ a₁ => if s₁ = s ∧ a₁ = a then u else r s₁ a₁

/-- The net (42), p. 16: `{−n ε, …, −ε, 0, ε, …, n ε}` for the largest integer `n` with
`n ε < 1/(1−γ)`. -/
def epsNet (γ ε : ℝ) : Set ℝ :=
  {u | ∃ k : ℤ, u = k * ε ∧ |(k : ℝ)| * ε < 1 / (1 - γ)}

/-- The separation event `B_ω` of (41), p. 16, for the MDP `(P, r, γ)`: at every state one action beats
every other action by at least `ω` in `Q⋆`. -/
def IsSeparated {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ ω : ℝ) : Prop :=
  ∀ s, ∃ a₀, ∀ a, a ≠ a₀ → optQ P r γ s a + ω ≤ optQ P r γ s a₀

end BreakingSample.Perturbed


