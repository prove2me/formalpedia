-- Prove2me | Definitions.Def_WildeQIT_QErasure_IsAchievableRate
-- name    : WildeQIT_QErasure_IsAchievableRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:38:55.901691+00:00
-- url     : https://prove2.me/theorems/8d706877-4b6f-40a5-a5f7-0d0e1c1a7993
-- title:
--   Achievable rate of quantum communication
-- statement:
--   The rate of a quantum communication code with $A_1$ of dimension $m$ and block length $n$ is $Q=\frac1n\log\dim\mathcal H_{A_1}$, the number of qubits transmitted per channel use. A rate $Q$ is **achievable** for $\mathcal N$ if for all $\varepsilon\in(0,1)$ and $\delta>0$ there is $N_0$ such that for every $n\ge N_0$ there exists an $(n,Q-\delta,\varepsilon)$ quantum communication code, i.e. a code meeting the error criterion $\varepsilon$ whose rate is $Q-\delta$.
--
--   **Formalization Note** The rate requirement is read as $n(Q-\delta)\le\log_2 m$ with $m\ge1$: the rate of a code is the logarithm of an integer divided by $n$, so a rate of exactly $Q-\delta$ is in general unavailable, and a code of larger rate yields codes of every smaller dimension by restricting the encoder to a subspace. Logarithms are base 2.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.1, (24.3), p. 659

import Definitions.Def_WildeQIT_QErasure_QCode_IsGood
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.1, p. 659, (24.3)
(achievable rates of quantum communication).
-/

namespace WildeQIT.QErasure

/-- **Achievable rate of quantum communication** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §24.1, p. 659): "The rate `Q` of this scheme is equal to the number of qubits
transmitted per channel use: `Q ≡ (1/n) log dim(H_{A₁})` (24.3). A rate `Q` is achievable for `N` if
there exists an `(n, Q − δ, ε)` quantum communication code for all `ε ∈ (0, 1)`, `δ > 0`, and
sufficiently large `n`."

**Formalization Note.** `dim(H_{A₁}) = m ≥ 1` (a system that carries a state). "An `(n, Q − δ, ε)`
code" is read as a code of rate at least `Q − δ`, i.e. `n (Q − δ) ≤ log₂ m`: the rate `(1/n) log₂ m`
of a code is the logarithm of an integer, so a rate of exactly `Q − δ` is in general not available,
and a code of larger rate yields one of every smaller integer dimension by restricting the encoder
to a subspace. Logarithms are base 2 (qubits). -/
def IsAchievableRate {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (Q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ m : ℕ, 1 ≤ m ∧ (n : ℝ) * (Q - δ) ≤ Real.logb 2 m ∧
      ∃ c : QCode a b n m, c.IsGood N ε

end WildeQIT.QErasure


