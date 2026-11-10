-- Prove2me | Definitions.Def_OnlineTransportation1195_Main_Computation
-- name    : OnlineTransportation1195_Main_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:36:15.008754+00:00
-- url     : https://prove2.me/theorems/a0f37515-c870-404e-bf79-312c9cd5c1a7
-- title:
--   Tree input and output interfaces for charged real arithmetic computation
-- statement:
--   Use the referenced finite real RAM, whose scalar arithmetic, memory accesses, pointer operations and comparisons are charged one instruction each. Programs have rational literals and successful executions divide only by positive operands. Min is implementable by comparison and branching. No instruction computes a tree walk, an optimum or a root patch for free.
--
--   The finite input is $n$, root label, the parent/weight/deadline triple at every vertex, then a supplied DFS list length and its vertex labels. Arbitrary real weights and deadlines are retained. Unused memory is initially zero. Theorem 1.3 supplies no DFS and zero placeholder deadlines; its output length and every vertex must be written in designated negative-address cells. Lemma 3.3 instead outputs $s$ and $t$ in cells $-1,-2$.
--
--   $$\text{executed instructions}\le C(n+1)^d$$
--
--   has one constant and exponent before all instances in the relevant theorem. The walk length obeys the same bound. This is an explicit reading of the source's polynomial arithmetic computation, not a bit-complexity claim for an encoding of arbitrary reals. No time bound or mathematical correctness is bundled into a program.
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Theorem 1.3 computational clause and Lemma 3.3 computation on p.12, PDF / printed p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_RedPatches
import Definitions.Def_SmaleNinth_RealRAM

namespace OnlineTransportation1195.Main

/-- Polynomial-time means uniform real arithmetic/comparison computation.
Only rational program literals are used. No tree search or optimization oracle
exists. Min is implemented by comparison/branching in the published scalar RAM. -/
def RationalProgram (P : SmaleNinth.RAMProgram) : Prop :=
  ∀ i ∈ P, ∀ j c, i = .const j c → ∃ q : ℚ, c = (q : ℝ)

/-- Successful runs divide only by positive values. The original RAM's zero
division totalization therefore cannot produce a spurious construction. -/
def PositiveDivisions (P : SmaleNinth.RAMProgram) (input : ℤ → ℝ) (fuel : ℕ) : Prop :=
  ∀ t < fuel, ∀ a b c,
    P[(SmaleNinth.RAMRun P input t).pc]? = some (.div a b c) →
      0 < (SmaleNinth.RAMRun P input t).regs c

/-- Finite input tape: n, root, then (parent, weight, deadline) per vertex,
then the supplied DFS vertex-list length and its vertices. Root weight/deadline
are ignored mathematically. No computed x, patch, budget or solution is input. -/
noncomputable def treeInput {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (L : List (Fin n)) : ℤ → ℝ :=
  let cells : List ℝ := [(n : ℝ), (T.root.val : ℝ)] ++
    (List.finRange n).flatMap (fun v => [((T.parent v).val : ℝ), T.W v, d v]) ++
    [(L.length : ℝ)] ++ L.map (fun v => (v.val : ℝ))
  fun z => if 0 ≤ z then cells.getD z.toNat 0 else 0

/-- Output memory: cell -1 contains the vertex-list length, cell -2-i its
i-th vertex label. Equality checks every output coordinate, so no decoding or
solution is supplied free by the input encoding. -/
def OutputsWalk {n : ℕ} (s : SmaleNinth.RAMConfig) (L : List (Fin n)) : Prop :=
  s.mem (-1) = (L.length : ℝ) ∧
    ∀ i : Fin L.length, s.mem (-2 - (i.val : ℤ)) = ((L.get i).val : ℝ)

end OnlineTransportation1195.Main


