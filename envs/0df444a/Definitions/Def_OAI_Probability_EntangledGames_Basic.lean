-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_Basic
-- name    : OAI_Probability_EntangledGames_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:48:12.025698+00:00
-- url     : https://prove2.me/theorems/18f6f521-0b1e-4e79-8feb-17a8939859bc
-- title:
--   Deterministic constant-answer strategy for a two-player nonlocal game
-- statement:
--   A finite-dimensional entangled strategy for a two-player game with question sets $X,Y$ and finite answer sets $A,B$ consists of local dimensions $d_A,d_B\ge 1$, a unit vector $\psi\in\mathbb{C}^{d_A}\otimes\mathbb{C}^{d_B}$ (coordinates $\psi_{(i,i')}$ with $\sum_{i,i'}|\psi_{(i,i')}|^2=1$), and, for every question $x\in X$, a family $(M^x_a)_{a\in A}$ of positive semidefinite $d_A\times d_A$ matrices with $\sum_a M^x_a=I$, and likewise for every $y\in Y$ a family $(N^y_b)_{b\in B}$ of positive semidefinite $d_B\times d_B$ matrices with $\sum_b N^y_b=I$. The probability of the answers $(a,b)$ on the questions $(x,y)$ is given by the Born rule
--   $$p(a,b\mid x,y)=\operatorname{Re}\,\bigl\langle\psi,(M^x_a\otimes N^y_b)\,\psi\bigr\rangle .$$
--
--   Given answers $a_0\in A$ and $b_0\in B$, the **deterministic strategy** $S_{a_0,b_0}$ is the strategy with $d_A=d_B=1$, state $\psi=1\in\mathbb{C}\otimes\mathbb{C}\cong\mathbb{C}$, and the scalar measurement operators
--   $$M^x_a=\begin{cases}1,&a=a_0,\\0,&a\neq a_0,\end{cases}\qquad N^y_b=\begin{cases}1,&b=b_0,\\0,&b\neq b_0,\end{cases}\qquad(x\in X,\ y\in Y).$$
--   Whatever the questions, Alice answers $a_0$ and Bob answers $b_0$ with certainty: $p(a,b\mid x,y)=1$ if $(a,b)=(a_0,b_0)$ and $0$ otherwise. The question sets $X,Y$ are arbitrary (no finiteness is needed) and are ignored by the strategy.
--
--   This strategy is a canonical element of the space of strategies. It shows that the set of strategies is nonempty, both for a single game and for its $k$-fold parallel repetition (where questions and answers are $k$-tuples and one takes constant answer tuples), so the entangled value and the threshold value, which are suprema of success probabilities over all strategies, are suprema over nonempty sets.
--
--   **Formalization Note** In the Lean structure `Strategy X Y A B` the local dimensions are stored as `dimA + 1` and `dimB + 1`; here `dimA = dimB = 0`. The constructor `Strategy.deterministic a₀ b₀` requires `Fintype` and `DecidableEq` instances on the answer types `A` and `B`; the obligations (unit state, positivity, completeness) are discharged inside the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace ThresholdParallelRepetition

open scoped Kronecker
open Matrix

namespace Strategy
variable {X Y A B : Type} [Fintype A] [Fintype B]

end Strategy

namespace Strategy

def deterministic {X Y A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a₀ : A) (b₀ : B) : Strategy X Y A B where
  dimA := 0
  dimB := 0
  state := fun _ => 1
  state_unit := by simp
  alice := fun _ a => if a = a₀ then 1 else 0
  bob := fun _ b => if b = b₀ then 1 else 0
  alice_pos := by
    intro _ a
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  bob_pos := by
    intro _ b
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  alice_total := by intro _; simp
  bob_total := by intro _; simp

end Strategy

end ThresholdParallelRepetition

end

end OAI


