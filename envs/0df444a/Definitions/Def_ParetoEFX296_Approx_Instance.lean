-- Prove2me | Definitions.Def_ParetoEFX296_Approx_Instance
-- name    : ParetoEFX296_Approx_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:59.140179+00:00
-- url     : https://prove2.me/theorems/bff22a16-1894-4884-95cd-7699674db091
-- title:
--   Theorem 2 table, named allocations, utility profiles, and square symmetries
-- statement:
--   There are four agents $1,2,3,4$ and nine goods $x,y,a,b,c,d,e,p,q$. For $K\in\mathbb N$, the table $v=\mathrm{inst}(K)$ is
--   $$\begin{array}{c|rrrrrrrrr}&x&y&a&b&c&d&e&p&q\\1&3K&2K+2&K&K&1&1&K&2&1\\2&2K+2&3K&1&K&K&1&K&1&2\\3&3K&2K+2&1&1&K&K&K&2&1\\4&2K+2&3K&K&1&1&K&K&1&2\end{array}.$$
--   Write $u(A)=(v_1(A_1),v_2(A_2),v_3(A_3),v_4(A_4))$. The constructed complete allocations are $B_1=(x,bce,yp,adq)$, $B_2=(abe,y,cdp,xq)$, and $C=(x,yb,cep,adq)$. Swapping the large goods exchanges the owners of $x,y$ and fixes every other good.
--
--   A square symmetry is a pair of permutations $(r,s)$ of agents and goods preserving every table entry: $v_{r(i)}(s(g))=v_i(g)$. It sends $A$ to the allocation $g\mapsto r(A(s^{-1}(g)))$. These definitions supply the paper's named comparison allocations and its relabellings; they assert no existence or domination result. Agent constructors retain the printed labels. Values are real, and positivity is a conclusion of the goal for $K\ge6$.
-- source:
--   Sepideh Mahabadi, Prasanna Ramakrishnan, Jakub Tarnawski, Pareto Inefficiency of EFX, STOC 2027 submission #296 (October 2026), source.pdf SHA-256 5f34a4a4b942d95889f3403900ad796cd81a27e83d783e5ab04012fab5385ee1, p.9, Theorem 2 table; pp.10–11, Step 2, Cases 1–2; p.6, square representation (adapted to the p.9 table); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/296.pdf

import Mathlib
import Definitions.Def_ParetoEFX296_Approx_Setting

namespace ParetoEFX296.Approx

inductive Agent where
  | one | two | three | four
  deriving DecidableEq

instance : Fintype Agent where
  elems := {.one, .two, .three, .four}
  complete := by intro i; cases i <;> simp

inductive Good where
  | x | y | a | b | c | d | e | p | q
  deriving DecidableEq

instance : Fintype Good where
  elems := {.x, .y, .a, .b, .c, .d, .e, .p, .q}
  complete := by intro g; cases g <;> simp

/-- All 36 entries of Theorem 2's table (p.9), in the order x y a b c d e p q. -/
def inst (K : ℕ) : Agent → Good → ℝ
  | .one, .x => 3 * (K : ℝ)
  | .one, .y => 2 * (K : ℝ) + 2
  | .one, .a => K
  | .one, .b => K
  | .one, .c => 1
  | .one, .d => 1
  | .one, .e => K
  | .one, .p => 2
  | .one, .q => 1
  | .two, .x => 2 * (K : ℝ) + 2
  | .two, .y => 3 * (K : ℝ)
  | .two, .a => 1
  | .two, .b => K
  | .two, .c => K
  | .two, .d => 1
  | .two, .e => K
  | .two, .p => 1
  | .two, .q => 2
  | .three, .x => 3 * (K : ℝ)
  | .three, .y => 2 * (K : ℝ) + 2
  | .three, .a => 1
  | .three, .b => 1
  | .three, .c => K
  | .three, .d => K
  | .three, .e => K
  | .three, .p => 2
  | .three, .q => 1
  | .four, .x => 2 * (K : ℝ) + 2
  | .four, .y => 3 * (K : ℝ)
  | .four, .a => K
  | .four, .b => 1
  | .four, .c => 1
  | .four, .d => K
  | .four, .e => K
  | .four, .p => 1
  | .four, .q => 2

/-- Utility profile with the paper's one-based agent labels. -/
def profile (u₁ u₂ u₃ u₄ : ℝ) : Agent → ℝ
  | .one => u₁
  | .two => u₂
  | .three => u₃
  | .four => u₄

noncomputable def utility (K : ℕ) (A : Allocation Agent Good) (i : Agent) : ℝ :=
  value (inst K) i (bundle A i)

/-- B in Case 1 (p.10): (x, bce, yp, adq). -/
def B₁ : Allocation Agent Good
  | .x => .one
  | .b | .c | .e => .two
  | .y | .p => .three
  | .a | .d | .q => .four

/-- B in Case 2 (p.10): (abe, y, cdp, xq). -/
def B₂ : Allocation Agent Good
  | .a | .b | .e => .one
  | .y => .two
  | .c | .d | .p => .three
  | .x | .q => .four

/-- C in Case 2 (p.11): (x, yb, cep, adq). -/
def C : Allocation Agent Good
  | .x => .one
  | .y | .b => .two
  | .c | .e | .p => .three
  | .a | .d | .q => .four

/-- Swap the owners of x and y, leaving the other seven goods fixed. -/
def swapLarge (A : Allocation Agent Good) : Allocation Agent Good
  | .x => A .y
  | .y => A .x
  | g => A g

/-- A relabelling preserving the table, as used by the square symmetries on pp.9–10.
This stores ONLY permutations and entry preservation, never any theorem conclusion. -/
structure SquareSymmetry (K : ℕ) where
  agents : Equiv.Perm Agent
  goods : Equiv.Perm Good
  preserves : ∀ i g, inst K (agents i) (goods g) = inst K i g

/-- Transport owners by the permutations: the bundle at σ(i) is the image of A_i. -/
def relabel {K : ℕ} (σ : SquareSymmetry K) (A : Allocation Agent Good) :
    Allocation Agent Good :=
  fun g => σ.agents (A (σ.goods.symm g))

end ParetoEFX296.Approx


