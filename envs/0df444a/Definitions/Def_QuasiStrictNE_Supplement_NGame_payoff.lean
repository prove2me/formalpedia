-- Prove2me | Definitions.Def_QuasiStrictNE_Supplement_NGame_payoff
-- name    : QuasiStrictNE_Supplement_NGame_payoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:39:09.651665+00:00
-- url     : https://prove2.me/theorems/576d0c89-a337-4b58-8992-ea43eb06aaa8
-- title:
--   Expected payoff $P_{i,a}(\nu_{-i})$ of a pure action
-- statement:
--   Let $G$ be an $n$-player game with payoffs $u_i$, and let $\nu = (\nu_0,\dots,\nu_{n-1})$ be a profile of vectors $\nu_j \in \mathbb R^{k_j}$ (in use, mixed strategies). The **expected payoff** of action $a$ of player $i$ is
--
--   $$
--   P_{i,a}(\nu_{-i}) \;=\; \sum_{s:\ s_i = a} \Bigl(\prod_{j \ne i} \nu_j(s_j)\Bigr)\, u_i(s),
--   $$
--
--   the sum running over all pure profiles in which player $i$ plays $a$. It depends only on the strategies $\nu_{-i}$ of the other players.
--
--   This is the quantity $P_{i,a}$ of the proof of Theorem 2 and defines best responses in $n$-player games.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), proof of Theorem 2, p.19 ("let P_{i,a} denote the expected payoff if player i chooses action a")

import Mathlib
import Definitions.Def_QuasiStrictNE_Supplement_NGame

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **Expected payoff of a pure action against the other players' mixed strategies** (Hansen & Nie,
*On Existence and Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, proof of
Theorem 2, p.19: "let `P_{i,a}` denote the expected payoff if player i chooses action a from action
set `Aᵢ`", written `P_{i,a}(ν_{−i})`).

For a profile `ν` of vectors `ν j : Fin (k j) → ℝ` (in use, mixed strategies), the expected payoff of
action `a` of player `i` is
`P_{i,a}(ν_{−i}) = ∑_{s : s i = a} (∏_{j ≠ i} ν j (s j)) · u i s`,
the sum over all pure profiles in which player `i` plays `a`. It depends only on `ν_{−i}`.

**Formalization Note** The payoff `u i s ∈ ℚ` is cast to `ℝ`. The product is over `j ∈ Fin n`,
`j ≠ i` (`Finset.univ.erase i`). -/
noncomputable def NGame.payoff {n : ℕ} (G : NGame n) (ν : (j : Fin n) → Fin (G.k j) → ℝ)
    (i : Fin n) (a : Fin (G.k i)) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : ((j : Fin n) → Fin (G.k j)) => s i = a),
    (∏ j ∈ Finset.univ.erase i, ν j (s j)) * (G.u i s : ℝ)

end QuasiStrictNE.Supplement


