-- Prove2me | Definitions.Def_FixpNash_WeakApprox_NashFunction
-- name    : FixpNash_WeakApprox_NashFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:26.665464+00:00
-- url     : https://prove2.me/theorems/dc59da6d-c6c0-4702-8ccc-1af8fc6ddf23
-- title:
--   pp. 12, 16 — the gains g_{i,j}, Nash's function F_Γ and weak ε′-approximate fixed points
-- statement:
--   Let $\Gamma$ be a finite game in normal form: a finite set of players $i$, for each player a finite set $S_i$ of pure strategies, and for each player $i$ a payoff function $u_i$ on the pure strategy profiles $S=\prod_i S_i$. A mixed profile $x$ assigns to every player $i$ a probability distribution $x_i=(x_{i,j})_{j\in S_i}$ on $S_i$; $u_i(x)$ is the expected payoff of player $i$ when the players randomize independently, and $u_i((i{:}j);x_{-i})$ is the expected payoff of $i$ when $i$ plays the pure strategy $j$ and every other player keeps its mixed strategy from $x$. $D_\Gamma$ denotes the set of mixed profiles.
--
--   1. The **gain** of player $i$ switching to its pure strategy $j$ is
--   $$g_{i,j}(x)=u_i((i{:}j);x_{-i})-u_i(x).$$
--   2. **Nash's function** $F_\Gamma$ has the $(i,j)$ component
--   $$F_\Gamma(x)_{(i,j)}=\frac{x_{i,j}+\max\{0,g_{i,j}(x)\}}{1+\sum_{l\in S_i}\max\{0,g_{i,l}(x)\}}.$$
--   3. A **weak $\varepsilon'$-approximate fixed point** of $F_\Gamma$ is a point $x\in D_\Gamma$ with $|F_\Gamma(x)-x|_\infty<\varepsilon'$, that is, $|F_\Gamma(x)_{(i,j)}-x_{i,j}|<\varepsilon'$ for every player $i$ and every $j\in S_i$.
--
--   Nash's function maps $D_\Gamma$ into itself and its fixed points are exactly the Nash equilibria of $\Gamma$; the weak approximation asks only that $x$ be almost fixed, not that it be close to a fixed point. These are the objects of Proposition 3 of the paper.
--
--   **Formalization Note** Players, strategy families, mixed profiles and expected payoffs are those of the published `agt_games` bundle; $u_i((i{:}j);x_{-i})$ is the published `DGPNash.NashMap.purePayoff`. Payoffs are real-valued (the paper takes rationals for computational reasons). The page writes the sum in the denominator as $\sum_{l=1}^{m_i}$ with an undefined $m_i$; §2 numbers the strategies of player $i$ as $1,\dots,n_i$ with $n_i=|S_i|$, so the sum is over all of $S_i$. `nashFunction` is defined by the printed formula on all real vectors; its denominator is at least $1$ everywhere, so no division by zero occurs. The published `DGPNash.NashMap.gain`/`nashMap` (Daskalakis–Goldberg–Papadimitriou) use the same formula but only for games with players `Fin r` and strategies `Fin n`, so they are not reused here.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), §2.3, p. 12 (Nash's function, the gain g_{i,j}) and p. 16 (Weak Approximation)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap

namespace FixpNash.WeakApprox

open Finset

/-- The **gain** `g_{i,j}(x) = u_i((i:j); x_{-i}) - u_i(x)` of player `i` switching to its pure
strategy `j` against the profile `x` (Etessami–Yannakakis, §2.3, p. 12). -/
noncomputable def gain {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) (j : S i) : ℝ :=
  DGPNash.NashMap.purePayoff u x i j - AGT.expectedPayoff u x i

/-- **Nash's function** `F_Γ` (p. 12):
`F_Γ(x)_{(i,j)} = (x_{i,j} + max{0, g_{i,j}(x)}) / (1 + Σ_{l ∈ S_i} max{0, g_{i,l}(x)})`. -/
noncomputable def nashFunction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) (j : S i) : ℝ :=
  (x i j + max 0 (gain u x i j)) / (1 + ∑ l : S i, max 0 (gain u x i l))

/-- A **weak `ε'`-approximate fixed point** of Nash's function (p. 16): a mixed profile `x`
(a point of the domain `D_Γ`) with `|F_Γ(x) - x|_∞ < ε'`, i.e. every coordinate of
`F_Γ(x) - x` has absolute value less than `ε'`. -/
def IsWeakApproxFixedPoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε' : ℝ) : Prop :=
  AGT.IsMixedProfile x ∧ ∀ (i : ι) (j : S i), |nashFunction u x i j - x i j| < ε'

end FixpNash.WeakApprox


