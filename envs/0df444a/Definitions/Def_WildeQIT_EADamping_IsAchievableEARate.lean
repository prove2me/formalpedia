-- Prove2me | Definitions.Def_WildeQIT_EADamping_IsAchievableEARate
-- name    : WildeQIT_EADamping_IsAchievableEARate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:39:04.349276+00:00
-- url     : https://prove2.me/theorems/8f5ab39a-6ed4-46eb-b4e7-82e213e41660
-- title:
--   Achievable rate of entanglement-assisted classical communication
-- statement:
--   An $(n,C,\varepsilon)$ entanglement-assisted classical code has rate $C=\frac1n\log|\mathcal M|$ and maximal error probability $p_e^*=\max_{m\in\mathcal M}p_e(m)\le\varepsilon$. A rate $C$ of entanglement-assisted classical communication is **achievable** for a channel $\mathcal N$ if for all $\varepsilon\in(0,1)$ and $\delta>0$ there is $N_0$ such that for every $n\ge N_0$ there is an $(n,C-\delta,\varepsilon)$ entanglement-assisted classical code:
--
--   $$
--   |\mathcal M|\ge 2^{n(C-\delta)}\quad\text{and}\quad \max_m p_e(m)\le\varepsilon .
--   $$
--
--   The **entanglement-assisted classical capacity** $C_{EA}(\mathcal N)$ is the supremum of all achievable rates.
--
--   **Formalization Note** "Rate $C-\delta$" is read as at least $2^{n(C-\delta)}$ messages, the reading under which codes exist when $2^{n(C-\delta)}$ is not an integer. Logarithms are base 2. The message set is `Fin k`, so $|\mathcal M|=k$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §21.1, pp. 589–590, (21.8)–(21.9)

import Definitions.Def_WildeQIT_EADamping_EACode_errorProb
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.1, pp. 589–590,
(21.8)–(21.9) (achievable rates of entanglement-assisted classical communication; the capacity
`C_EA(N)` is their supremum).
-/

namespace WildeQIT.EADamping

/-- **Achievable rate of entanglement-assisted classical communication** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, §21.1, p. 590): "A rate `C` of entanglement-assisted
classical communication is achievable if there exists an `(n, C − δ, ε)` entanglement-assisted
classical code for all `ε ∈ (0, 1)`, `δ > 0`, and sufficiently large `n`." An `(n, C, ε)` code has
rate `(1/n) log |M|` (21.9) and maximal error probability `max_m p_e(m) ≤ ε` (21.8). The
entanglement-assisted classical capacity `C_EA(N)` is the supremum of all achievable rates.

**Formalization Note.** "Rate `C − δ`" is read as `|M| ≥ 2^{n(C−δ)}` (at least that many messages),
the reading under which codes exist for non-integer `2^{n(C−δ)}`; logarithms are base 2 (bits).
The message set is `Fin k`, `|M| = k`. -/
def IsAchievableEARate {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ k : ℕ, (2 : ℝ) ^ ((n : ℝ) * (C - δ)) ≤ k ∧
      ∃ c : EACode a b n k, ∀ m, c.errorProb N m ≤ ε

end WildeQIT.EADamping


