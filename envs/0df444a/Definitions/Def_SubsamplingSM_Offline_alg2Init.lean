-- Prove2me | Definitions.Def_SubsamplingSM_Offline_alg2Init
-- name    : SubsamplingSM_Offline_alg2Init
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:54:07.404289+00:00
-- url     : https://prove2.me/theorems/f8cfe8eb-2c8e-434b-8753-8aafc112e570
-- title:
--   Initial state of Algorithm 2
-- statement:
--   Algorithm 2 starts with $N'=N$, $S=\emptyset$, $O=O_0$, $O_u=S_u=\emptyset$ for every $u\in N$, and no element with $Y_u=1$.
--
--   **Formalization Note** The paper starts from $O=\mathrm{OPT}$, an optimal solution. Here the starting set $O_0$ is a parameter, and the lemmas assume only $O_0\in\mathcal I$; the optimality of OPT is used only when Theorem 1 is assembled.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 2, Line 1, p. 9

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_Alg2State

namespace SubsamplingSM.Offline

/-- **Initial state of Algorithm 2.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 2, Line 1, p. 9: "Let `N′ ← N`, `S ← ∅`, `O ← OPT`, and `Ou ← ∅`,
`Su ← ∅` for each `u ∈ N`."

`alg2Init O₀` has `S = ∅`, `O = O₀`, `N′ = N`, `O_u = S_u = ∅` for all `u`, and no `u` with
`Y_u = 1`.

**Formalization Note.** The paper starts from `O = OPT`; here the starting set `O₀` is a
parameter, and the statements assume only `O₀ ∈ I` (paper.md generalization 7: Lemmas 5–10
never use the optimality of OPT). -/
def alg2Init {α : Type*} [Fintype α] (O₀ : Finset α) : Alg2State α :=
  { S := ∅, O := O₀, N' := Finset.univ, Ou := fun _ => ∅, Su := fun _ => ∅, Ys := ∅ }

end SubsamplingSM.Offline


