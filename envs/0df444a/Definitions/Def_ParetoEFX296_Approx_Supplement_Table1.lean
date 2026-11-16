-- Prove2me | Definitions.Def_ParetoEFX296_Approx_Supplement_Table1
-- name    : ParetoEFX296_Approx_Supplement_Table1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:31:21.320206+00:00
-- url     : https://prove2.me/theorems/c25f777a-1255-44b7-8199-fb83f0458f0d
-- title:
--   Theorem 1 table — four agents, eight goods $x,y,a,b,c,d,p,q$
-- statement:
--   Theorem 1 concerns the four agents $1,2,3,4$ and the eight indivisible goods $x,y,a,b,c,d,p,q$: two **large** goods $x,y$, four **medium** goods $a,b,c,d$ and two **small** goods $p,q$. There is no ninth good. The additive valuation $v_i(g)$ of agent $i$ for good $g$ is given by the table
--   $$\begin{array}{c|rrrrrrrr}&x&y&a&b&c&d&p&q\\\hline 1&7&6&3&3&1&1&2&1\\2&6&7&1&3&3&1&1&2\\3&7&6&1&1&3&3&2&1\\4&6&7&3&1&1&3&1&2\end{array}$$
--   and the value of a bundle $S$ is $v_i(S)=\sum_{g\in S}v_i(g)$ (the published additive extension). All 32 entries are positive integers.
--
--   This instance is the paper's counterexample showing that EFX and Pareto optimality are incompatible even when every agent values every good. It is a fixed table, different from the parameterized nine-good table of Theorem 2.
--
--   **Formalization Note** The goods form a new finite type `Good8` with exactly eight constructors; the agents are the published four-constructor type `Agent` of the Theorem 2 instance (constructors `one, two, three, four` for the printed labels $1,2,3,4$). Entries are real numbers so that the published `value`, `IsAlphaEFX` and `IsParetoOptimal` apply unchanged.
-- source:
--   Sepideh Mahabadi, Prasanna Ramakrishnan, Jakub Tarnawski, Pareto Inefficiency of EFX, STOC 2027 submission #296 (October 2026), source.pdf SHA-256 5f34a4a4b942d95889f3403900ad796cd81a27e83d783e5ab04012fab5385ee1, p.3, Theorem 1 table (repeated p.5, §3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/296.pdf

import Mathlib
import Definitions.Def_ParetoEFX296_Approx_Instance

namespace ParetoEFX296.Approx.Supplement

/-- The eight goods of Theorem 1 (p.3): large `x, y`, medium `a, b, c, d`, small `p, q`.
There is no good `e`; this carrier is distinct from the nine-good `Good` of Theorem 2. -/
inductive Good8 where
  | x | y | a | b | c | d | p | q
  deriving DecidableEq

instance : Fintype Good8 where
  elems := {.x, .y, .a, .b, .c, .d, .p, .q}
  complete := by intro g; cases g <;> simp

/-- All 32 entries of Theorem 1's table (p.3, repeated p.5), in the order x y a b c d p q,
for the four agents `one, two, three, four` (printed labels 1, 2, 3, 4). -/
def v1 : Agent → Good8 → ℝ
  | .one, .x => 7
  | .one, .y => 6
  | .one, .a => 3
  | .one, .b => 3
  | .one, .c => 1
  | .one, .d => 1
  | .one, .p => 2
  | .one, .q => 1
  | .two, .x => 6
  | .two, .y => 7
  | .two, .a => 1
  | .two, .b => 3
  | .two, .c => 3
  | .two, .d => 1
  | .two, .p => 1
  | .two, .q => 2
  | .three, .x => 7
  | .three, .y => 6
  | .three, .a => 1
  | .three, .b => 1
  | .three, .c => 3
  | .three, .d => 3
  | .three, .p => 2
  | .three, .q => 1
  | .four, .x => 6
  | .four, .y => 7
  | .four, .a => 3
  | .four, .b => 1
  | .four, .c => 1
  | .four, .d => 3
  | .four, .p => 1
  | .four, .q => 2

end ParetoEFX296.Approx.Supplement


