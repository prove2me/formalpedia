-- Prove2me | Definitions.Def_WildeQIT_EntManip_IsAchievableRate
-- name    : WildeQIT_EntManip_IsAchievableRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:39:17.259115+00:00
-- url     : https://prove2.me/theorems/1ff9918b-9042-46d5-81c2-bc1858180c23
-- title:
--   Achievable rate of entanglement manipulation
-- statement:
--   Let $|\psi\rangle_{AB},|\varphi\rangle_{AB}\in\mathcal H_A\otimes\mathcal H_B$. A real number $E$ is an **achievable rate** of entanglement manipulation for $\psi\to\varphi$ when for every $\varepsilon\in(0,1)$ and $\delta>0$ there is $N$ such that for every $n\ge N$ there are $m\in\mathbb N$ with
--
--   $$
--   \frac mn\ge E-\delta
--   $$
--
--   and an $(n,m/n,\varepsilon)$ entanglement manipulation protocol. The **entanglement manipulation limit** $E(\psi\to\varphi)$ is the supremum of all achievable rates.
--
--   **Formalization Note** The book says "an $(n,E-\delta,\varepsilon)$ protocol"; the rate $m/n$ is a ratio of integers, so the requirement is read as $m/n\ge E-\delta$ (an exact $m/n=E-\delta$ is impossible for irrational or negative $E-\delta$, and would make no rate achievable). "Sufficiently large $n$" is $\exists N\,\forall n\ge N$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §19.3, p. 540

import Mathlib
import Definitions.Def_WildeQIT_EntManip_IsManipProtocol

namespace WildeQIT.EntManip

/-- **Achievable rate of entanglement manipulation** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, §19.3, p. 540): "a particular rate `E` of entanglement manipulation is
achievable if there exists an `(n, E − δ, ε)` entanglement manipulation protocol for all
`ε ∈ (0, 1)`, `δ > 0`, and sufficiently large `n`." The entanglement manipulation limit
`E(ψ → φ)` is the supremum of all achievable rates.

**Formalization Note** "Rate `E − δ`" is read as `m/n ≥ E − δ`: the number `m` of output copies is
an integer, so the rate `m/n` can only be required to reach `E − δ` (an exact `m/n = E − δ` is
impossible for irrational `E − δ`). "Sufficiently large `n`" is `∃ N, ∀ n ≥ N`. -/
def IsAchievableRate {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ φ : a × b → ℂ) (E : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ m : ℕ, E - δ ≤ (m : ℝ) / n ∧ IsManipProtocol ψ φ n m ε

end WildeQIT.EntManip


