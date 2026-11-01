-- Prove2me | Definitions.Def_WildeQIT_Schumacher_IsAchievableRate
-- name    : WildeQIT_Schumacher_IsAchievableRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:52.220827+00:00
-- url     : https://prove2.me/theorems/373d2e2c-b5ba-4271-b252-cb5d279eb1a8
-- title:
--   Achievable quantum compression rate
-- statement:
--   A quantum compression rate $R$ is achievable for the source $\rho$ if for every $\delta > 0$ and every $\varepsilon \in (0,1)$ there is an $N$ such that for every $n \ge N$ an $(n, R+\delta, \varepsilon)$ quantum compression code exists.
--
--   **Formalization Note** "Sufficiently large $n$" is $\exists N\,\forall n \ge N$, with $N$ depending on $\delta$ and $\varepsilon$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §18.1, p. 523

import Definitions.Def_WildeQIT_Schumacher_IsCompressionCode

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §18.1, p. 523.
-/

namespace WildeQIT.Schumacher

/-- **Achievable quantum compression rate** (Wilde, arXiv:1106.1445v8, §18.1, p. 523): "a
quantum compression rate `R` is achievable if there exists an `(n, R + δ, ε)` quantum compression
code for all `δ > 0`, `ε ∈ (0, 1)`, and sufficiently large `n`."

**Formalization Note.** "Sufficiently large `n`" is `∃ N, ∀ n ≥ N`, with `N` depending on `δ`
and `ε`. -/
def IsAchievableRate {a : Type} [Fintype a] [DecidableEq a] (ρ : Matrix a a ℂ) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N : ℕ, ∀ n ≥ N,
    ∃ C : CompressionCode a n, IsCompressionCode ρ (R + δ) ε C

end WildeQIT.Schumacher


