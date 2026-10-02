-- Prove2me | Definitions.Def_TheoryOfGames_Decomposition_Constituent
-- name    : TheoryOfGames_Decomposition_Constituent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T04:11:58.209901+00:00
-- url     : https://prove2.me/theorems/28a3fc07-4c92-4ae0-ac61-b88d48fb8193
-- title:
--   The J-constituent of a game (41:4) and decomposability with respect to J, I − J (41:3)
-- statement:
--   Let $I$ be a finite set of players, $v$ a real function on the subsets of $I$, and $J \subseteq I$, $K = I - J$.
--
--   1. **$J$-constituent** ((41:4), 43.1). The $J$-constituent $\Delta$ of $\Gamma$ is the game whose set of players is $J$ itself, with characteristic function
--   $$v_\Delta(S) = v(S) \quad \text{for } S \subseteq J.$$
--   2. **Decomposability** (41.2.1, 41.3.1, 42.5.2). The game is *decomposable with respect to $J$ and $K$* if there are constant-sum games $\Delta$ with the set of players $J$ and $\mathrm{H}$ with the set of players $K$ — that is, functions $v_\Delta$ on the subsets of $J$ and $v_{\mathrm H}$ on the subsets of $K$, each satisfying (42:6:a)–(42:6:c) — such that (41:3) holds:
--   $$v(R) = v_\Delta(S) + v_{\mathrm H}(T), \qquad S = R \cap J,\ T = R \cap K \quad (41{:}2),$$
--   for every $R \subseteq I$.
--
--   Decomposability is the "implicit" property of 41.3.2 (existence of the unknown constituents $\Delta$, $\mathrm H$); (42:G) turns it into the explicit condition (41:6).
--
--   **Formalization Note** A subset of $J$ is a `Finset` of the subtype `↥J`; `constituent v J` evaluates $v$ on its image in $I$. Decomposability is formalized on the level of characteristic functions, as the book does from 41.3.1 on; by (42:D) every function satisfying (42:6:a)–(42:6:c) is the characteristic function of a constant-sum game, so no strategic data are needed.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 340, 41.2.1; pp. 341–342, 41.3.1, (41:1)–(41:3); p. 342, 41.3.2, (41:4), (41:5); p. 352, 42.5.2; p. 353, 43.1

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum

namespace TheoryOfGames.Decomposition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The characteristic function of the `J`-constituent `Δ` of the game `v` (41:4), 43.1: the game
whose set of players is `J` itself, with `v_Δ(S) = v(S)` for `S ⊆ J`. A subset of `J` is a
`Finset` of the subtype `↥J`; it is mapped back into `I = ι` to evaluate `v`. -/
def constituent (v : Finset ι → ℝ) (J : Finset ι) : Finset J → ℝ :=
  fun S => v (S.map (Function.Embedding.subtype (· ∈ J)))

/-- Decomposability of the constant-sum game `v` with respect to the complementary sets `J` and
`K = I - J = Jᶜ` (41.2.1, 41.3.1, 42.5.2), on the level of characteristic functions: there are
constant-sum games `Δ` with the set of players `J` and `H` with the set of players `K` (their
characteristic functions `v_Δ`, `v_H` satisfying (42:6:a)–(42:6:c)) such that (41:3) holds,
`v(R) = v_Δ(S) + v_H(T)` where `S = R ∩ J`, `T = R ∩ K` (41:2). -/
def IsDecomposable (v : Finset ι → ℝ) (J : Finset ι) : Prop :=
  ∃ (vΔ : Finset J → ℝ) (vH : Finset (Jᶜ : Finset ι) → ℝ),
    IsConstantSum vΔ ∧ IsConstantSum vH ∧
      ∀ R : Finset ι, v R = vΔ (R.subtype (· ∈ J)) + vH (R.subtype (· ∈ Jᶜ))

end TheoryOfGames.Decomposition


