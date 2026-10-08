-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_IsStrictNash
-- name    : YoungConventions_AdaptivePlay_IsStrictNash
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:20.215981+00:00
-- url     : https://prove2.me/theorems/c3d05365-eee1-4244-a8f4-6512e972f849
-- title:
--   Strict pure strategy Nash equilibrium (§4, p. 62)
-- statement:
--   In a game with players $i$, strategy sets $S_i$ and payoffs $u_i$, a strategy tuple $s \in \prod_j S_j$ is a **strict pure strategy Nash equilibrium** if every unilateral deviation strictly lowers the deviator's payoff:
--   $$u_i(y, s_{-i}) < u_i(s) \qquad \text{for every player } i \text{ and every } y \in S_i \text{ with } y \neq s_i .$$
--
--   Equivalently, each $s_i$ is the unique best reply of player $i$ to $s_{-i}$. Strict equilibria are the strategy tuples that, played $m$ times in succession, form the conventions of adaptive play.
--
--   **Formalization Note** The paper uses the standard notion without a display; its argument on p. 62 ("It must also be a unique best reply to $s_{-i}$") confirms the reading.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 62 (PDF p. 7)

import Mathlib

namespace YoungConventions.AdaptivePlay

/-- **Strict pure strategy Nash equilibrium** (Young 1993, *The Evolution of Conventions*,
Econometrica 61:57–84, §4, p. 62, PDF p. 7: "a strict pure strategy Nash equilibrium").

The pure strategy tuple `s ∈ ∏ Sᵢ` is a strict Nash equilibrium if every unilateral deviation
strictly lowers the deviator's payoff: for every player `i` and every `y ∈ Sᵢ` with `y ≠ sᵢ`,
`uᵢ(y, s₋ᵢ) < uᵢ(s)`. Equivalently, each `sᵢ` is the *unique* best reply to `s₋ᵢ`, which is how the
paper's argument on p. 62 uses the term.

**Formalization Note.** The paper uses the standard notion without a display. The profile
`(y, s₋ᵢ)` is `Function.update s i y`. -/
def IsStrictNash {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ i : ι, ∀ y : S i, y ≠ s i → u i (Function.update s i y) < u i s

end YoungConventions.AdaptivePlay


