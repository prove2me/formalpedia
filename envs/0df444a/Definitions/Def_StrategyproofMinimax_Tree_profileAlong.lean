-- Prove2me | Definitions.Def_StrategyproofMinimax_Tree_profileAlong
-- name    : StrategyproofMinimax_Tree_profileAlong
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T22:05:50.143164+00:00
-- url     : https://prove2.me/theorems/f41a44a8-53d0-49f3-b97c-a831209993ba
-- title:
--   The hard location profiles x⁰, x¹, …, xᵏ of Appendix B
-- statement:
--   Let $2m^k$ divide $n$ and put $q=n/(2m^k)$. Half of the agents, $n/2=q\,m^k$ of them, are **left agents**; each has an **address**, a word of length $k$, and every left vertex on level $k$ is the address of exactly $q$ agents. The other $n/2$ agents are **right agents**.
--
--   The profile $x^0$ puts every left agent at $l^0$ and every right agent at $r^0$. Given a path $l^0,l^1,\dots,l^d$ of left vertices ($l^{j+1}$ a child of $l^j$, $d<k$), the profile $x^{d+1}$ is obtained from $x^d$ by moving the $n/(2m^d)$ agents at $l^d$ to its $m$ children on level $d+1$, $n/(2m^{d+1})$ to each, each agent to the child that begins its address. Concretely, in $x^{d+1}$ a left agent with address $a$ sits at the prefix of $a$ of length $j+1$, where $j$ is the length of the longest common prefix of $a$ and the word $(l^1,\dots,l^d)$; right agents stay at $r^0$. Thus $x^1$ has $n/(2m)$ agents at each left vertex on level 1, and $x^k$ depends only on the path to $l^{k-1}$.
--
--   **Formalization Note.** Agents are $0,\dots,n-1$ (`Fin n`); agent $i$ is a left agent iff $\lfloor i/q\rfloor<m^k$ (i.e. $i<n/2$), and its address is the base-$m$ digit word of $\lfloor i/q\rfloor$. `profileZero m k n` is $x^0$, and `profileAlong m k n v` is $x^{d+1}$ for the word $v=(l^1,\dots,l^d)$; so for a left vertex $l^k$ on level $k$ with word $u$, $x^k$ is `profileAlong m k n u.dropLast`. Because each move of one agent is a single unilateral deviation, $x^{d+1}$ is reached from $x^d$ by a chain of `Function.update`s.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), pp. 524–525, Appendix B (profiles x⁰, x¹, x², …, xᵏ)

import Mathlib
import Definitions.Def_StrategyproofMinimax_Tree_HardTree

namespace StrategyproofMinimax.Tree

/-- Address of agent `i ∈ {0, …, n - 1}` in the hard profiles of Appendix B. With
`q = n / (2mᵏ)`, agent `i` is a left agent if `⌊i / q⌋ < mᵏ`, i.e. (when `2mᵏ ∣ n`) if
`i < n / 2`; its address is then the word of length `k` whose letters are the base-`m` digits of
`⌊i / q⌋`, so every left vertex on level `k` is the address of exactly `q` agents. The other
`n / 2` agents are right agents (`none`). -/
def address (m k n : ℕ) (i : Fin n) : Option (List (Fin m)) :=
  if h : (i : ℕ) / (n / (2 * m ^ k)) < m ^ k then
    some (List.ofFn ((finFunctionFinEquiv (m := m) (n := k)).symm ⟨(i : ℕ) / (n / (2 * m ^ k)), h⟩))
  else none

/-- `spreadPos v a`: where a left agent with address `a` sits once the agents have been moved
down the path `l⁰, l¹, …, l^d` given by the word `v = (l¹, …, l^d)` and the agents at `l^d` have
been moved to its children: the agent sits at `a.take (j + 1)`, where `j` is the length of the
longest common prefix of `v` and `a`. -/
def spreadPos {m : ℕ} : List (Fin m) → List (Fin m) → List (Fin m)
  | [], a => a.take 1
  | _ :: _, [] => []
  | c :: v, b :: a => if b = c then b :: spreadPos v a else [b]

/-- The profile `x⁰` of Appendix B (p. 524): the `n / 2` left agents at `l⁰`, the `n / 2` right
agents at `r⁰`. -/
noncomputable def profileZero (m k n : ℕ) : Fin n → HardTree m k := fun i =>
  match address m k n i with
  | some _ => vertex .left []
  | none => vertex .right []

/-- The profile `x^(d+1)` of Appendix B (pp. 524–525) along the path `l⁰, l¹, …, l^d`, given by the
word `v = (l¹, …, l^d)` of length `d`: it is obtained from `x^d` by moving the `n / (2mᵈ)` agents
at `l^d` to its `m` children on level `d + 1`, `n / (2m^(d+1))` to each. So `profileAlong m k n []`
is `x¹` (the left agents spread over the `m` left vertices on level 1), and for a left vertex `lᵏ`
on level `k` given by the word `u`, `profileAlong m k n u.dropLast` is `xᵏ`. The right agents stay
at `r⁰` throughout. -/
noncomputable def profileAlong (m k n : ℕ) (v : List (Fin m)) : Fin n → HardTree m k := fun i =>
  match address m k n i with
  | some a => vertex .left (spreadPos v a)
  | none => vertex .right []

end StrategyproofMinimax.Tree


