-- Prove2me | Definitions.Def_WildeQIT_ErasureClassical_IsAchievableRate
-- name    : WildeQIT_ErasureClassical_IsAchievableRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:14.16011+00:00
-- url     : https://prove2.me/theorems/0faf557a-681f-42a2-85d9-2b280f865841
-- title:
--   Achievable rate of classical communication over a quantum channel
-- statement:
--   Let $\mathcal N$ be a quantum channel. A rate $C$ of classical communication is **achievable** for $\mathcal N$ if for all $\delta>0$, all $\varepsilon\in(0,1)$ and all sufficiently large $n$ there exists an $(n,C-\delta,\varepsilon)$ code: a code for $n$ channel uses with a nonempty message set $\mathcal M$ of rate
--
--   $$
--   \frac1n\log|\mathcal M|\;\ge\;C-\delta
--   $$
--
--   and maximal probability of error $p_e^*\le\varepsilon$.
--
--   Encoders may use states entangled across the $n$ channel uses, and the decoder is an arbitrary POVM over all $n$ outputs.
--
--   **Formalization Note** "Sufficiently large $n$" is `∀ᶠ n in atTop`. Logarithms are base 2. The rate of an $(n,C-\delta,\varepsilon)$ code is read as at least $C-\delta$, since $|\mathcal M|$ is an integer; removing messages never increases the maximal error, so this reading defines the same set of achievable rates.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.2.1, (20.14)–(20.15), p. 562

import Definitions.Def_WildeQIT_ErasureClassical_errorProb
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.2.1, p. 562,
eqs. (20.14)–(20.15) and the definition of an achievable rate.
-/

namespace WildeQIT.ErasureClassical

/-- **Achievable rate of classical communication** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, §20.2.1, p. 562): "The rate `C` of communication is
`C ≡ (1/n) log |M|` (20.15), and the code has `ε ∈ [0, 1]` error if `p*_e ≤ ε`", where
`p*_e ≡ max_{m∈M} p_e(m)` (20.14). "A rate `C` of classical communication is achievable for a
channel `N` if there exists an `(n, C − δ, ε)` code for all `δ > 0`, `ε ∈ (0, 1)`, and
sufficiently large `n`."

**Formalization Note.** "Sufficiently large `n`" is `∀ᶠ n in atTop`. An `(n, C − δ, ε)` code is
read as a code for `n` channel uses with a nonempty message set `Fin M`, rate
`(1/n) log₂ M ≥ C − δ`, and maximal error probability at most `ε` (every `p_e(m) ≤ ε`): the
message-set size is an integer, so the rate `C − δ` is met up to rounding up. Logarithms are
base 2 (bits). -/
def IsAchievableRate {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ᶠ n : ℕ in Filter.atTop, ∃ M : ℕ, ∃ c : ClassicalCode a b n M,
      0 < M ∧ R - δ ≤ Real.logb 2 M / n ∧ ∀ m, errorProb N c m ≤ ε

end WildeQIT.ErasureClassical


