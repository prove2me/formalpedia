-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_Support
-- name    : OAI_Probability_ThorpShuffle_Support
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:22:32.946817+00:00
-- url     : https://prove2.me/theorems/5ed88fd7-b507-428b-9ee1-da72a5f47bcf
-- title:
--   Counting positions, deck states, coin vectors and coin histories of the Thorp shuffle
-- statement:
--   Let $Q_d=\{0,1\}^d$ be the set of positions of a deck of $2^d$ cards. The states of the deck are the permutations in $\mathrm{Sym}(Q_d)$. For a deck of $2^{d+1}$ cards, a coin vector is a function $c:Q_d\to\{0,1\}$ (one coin per pair of positions), and a history of length $t$ is a sequence of $t$ coin vectors. This module records their cardinalities: for all $d,t\in\mathbb{N}$,
--
--   1. the number of positions is $|Q_d|=2^d$;
--   2. the number of deck states is $|\mathrm{Sym}(Q_d)|=(2^d)!$;
--   3. the number of coin vectors for $2^{d+1}$ cards is $2^{2^d}$;
--   4. the number of histories of length $t$ for $2^{d+1}$ cards is $2^{2^dt}$.
--
--   In formulas,
--   $$
--   |Q_d|=2^d,\qquad|\mathrm{Sym}(Q_d)|=(2^d)!,\qquad\bigl|\{0,1\}^{Q_d}\bigr|=2^{2^d},\qquad\bigl|(\{0,1\}^{Q_d})^{t}\bigr|=2^{2^d\,t}.
--   $$
--
--   These counts are the normalizing constants of the uniform averages over coins and histories that appear throughout the analysis of the Thorp shuffle.
--
--   **Formalization Note** The statements are the simp lemmas `card_position`, `card_state`, `card_coins_succ` and `card_history_succ`. They are stated for the Lean types `Position d`, `State d`, `Coins (d + 1)` and `History (d + 1) t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/Support.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/Support.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh

namespace OAI

universe uΩ uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

@[simp] theorem card_position (d : ℕ) : Fintype.card (Position d) = 2 ^ d := by
  simp [Position]

@[simp] theorem card_state (d : ℕ) : Fintype.card (State d) = (2 ^ d).factorial := by
  classical
  rw [Fintype.card_perm, card_position]

@[simp] theorem card_coins_succ (d : ℕ) : Fintype.card (Coins (d + 1)) = 2 ^ (2 ^ d) := by
  simp [Coins]

@[simp] theorem card_history_succ (d t : ℕ) :
    Fintype.card (History (d + 1) t) = 2 ^ (2 ^ d * t) := by
  simp [History, ← pow_mul]

end Thorp

end

end OAI


