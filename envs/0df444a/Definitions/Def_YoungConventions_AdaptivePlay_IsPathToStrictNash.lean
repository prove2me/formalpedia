-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_IsPathToStrictNash
-- name    : YoungConventions_AdaptivePlay_IsPathToStrictNash
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:59:47.525272+00:00
-- url     : https://prove2.me/theorems/1cb4a785-70e5-4b93-982b-3c52c553a1f8
-- title:
--   Best-reply path of length $n$ from $s$ to a strict Nash equilibrium (§4, p. 64)
-- statement:
--   For a strategy tuple $s$ and $n \in \mathbb N$, there is a **best-reply path of length $n$ from $s$ to a strict Nash equilibrium** if there are strategy tuples $f_0, f_1, \dots, f_n$ with
--   $$f_0 = s, \qquad f_j \to f_{j+1} \text{ an edge of the best-reply graph for } j = 0, \dots, n-1, \qquad f_n \text{ a strict pure Nash equilibrium.}$$
--
--   This is the object whose shortest length defines $L(s)$.
--
--   **Formalization Note** The path is a function on $\{0, \dots, n\}$ (`Fin (n + 1)`); its length is the number $n$ of edges, and vertices may repeat.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9), definition of L(s)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_BestReplyEdge
import Definitions.Def_YoungConventions_AdaptivePlay_IsStrictNash

namespace YoungConventions.AdaptivePlay

/-- **Directed path of length `n` in the best-reply graph from `s` to a strict Nash equilibrium**
(Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84, §4, p. 64, PDF p. 9, in the
definition of `L(s)`: "a shortest directed path in the best reply graph from `s` to a strict Nash
equilibrium").

`IsPathToStrictNash u s n` holds iff there are vertices `s = f₀, f₁, …, fₙ` with an edge
`fⱼ → fⱼ₊₁` of the best-reply graph for every `j < n`, and `fₙ` a strict pure Nash equilibrium.

**Formalization Note.** The path is a function `f : Fin (n + 1) → ∏ Sᵢ`; its length is the number
`n` of edges. Vertices may repeat (a walk); this does not change the shortest length. -/
def IsPathToStrictNash {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) (n : ℕ) : Prop :=
  ∃ f : Fin (n + 1) → ∀ i, S i,
    f 0 = s ∧ IsStrictNash u (f (Fin.last n)) ∧
      ∀ j : Fin n, BestReplyEdge u (f j.castSucc) (f j.succ)

end YoungConventions.AdaptivePlay


