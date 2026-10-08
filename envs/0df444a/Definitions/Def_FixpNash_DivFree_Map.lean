-- Prove2me | Definitions.Def_FixpNash_DivFree_Map
-- name    : FixpNash_DivFree_Map
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:54.576249+00:00
-- url     : https://prove2.me/theorems/43ae760d-4515-44e2-a946-c26e9f64620b
-- title:
--   p. 47 — the vector h(x) = x + v(x), the functions f_{i,x}, the thresholds t_i and the map G_I
-- statement:
--   Let $I$ be a finite game: a finite set of players $i$, for each player a finite set $S_i$ of pure strategies, and payoff functions $u_i$ on pure strategy profiles. A real vector $x$ has entries $x_{ij}$ indexed by pairs $(i,j)$ with $j\in S_i$; the mixed strategy profiles are the vectors with $x_{ij}\ge 0$ and $\sum_{j\in S_i}x_{ij}=1$ for every $i$, and their set $\Delta$ (the product of the players' unit simplices) is the domain $D_I$ of the map defined here.
--
--   For a vector $x$, let $v(x)_{ij}=u_i((i{:}j);x_{-i})$ be the expected payoff to player $i$ of the pure strategy $j$ when the other players play according to $x$, and set
--   $$h(x)=x+v(x),\qquad h_{ij}(x)=x_{ij}+u_i((i{:}j);x_{-i}).$$
--   For each player $i$ consider the function of a real variable $t$
--   $$f_{i,x}(t)=\sum_{j\in S_i}\max\bigl(h_{ij}(x)-t,\,0\bigr),$$
--   let $t_i$ be the value of $t$ at which $f_{i,x}(t_i)=1$, and define
--   $$G_I(x)_{ij}=\max\bigl(h_{ij}(x)-t_i,\,0\bigr)\qquad\text{for every player } i \text{ and } j\in S_i.$$
--
--   This is the map whose fixed points in $\Delta$ are the Nash equilibria of $I$ (Lemma 20 of the paper); unlike Nash's own map it uses no division.
--
--   **Formalization Note.** The game is the published `agt_games` vocabulary (players a finite type, strategy sets finite types, real payoffs; the paper's payoffs are rational) and $v(x)_{ij}$ is the published `DGPNash.NashMap.purePayoff`. The threshold is defined as $t_i=\inf\{t\in\mathbb R : f_{i,x}(t)\le 1\}$, which requires no existence proof. When $S_i$ is nonempty this infimum is the unique solution of $f_{i,x}(t)=1$, which is the paper's definition ("there is a unique value of $t$, call it $t_i$, where $f_{i,x}(t_i)=1$"); that is the milestone `threshold_spec`. All four objects are defined by the same formulas for every real vector $x$, not only on $\Delta$; on $\Delta$ they are the paper's.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Section 4, definition of G_I, p. 47

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap

namespace FixpNash.DivFree

open Finset

/-!
The division-free map `G_I` of Etessami–Yannakakis, §4, p. 47.

A finite game is given, as in `agt_games`, by a finite type `ι` of players, a finite
strategy type `S i` for each player and payoffs `u : ι → (∀ i, S i) → ℝ`. A real vector
`x : ∀ i, S i → ℝ` has entries `x i j` indexed by pairs `(i, j)`; the domain `Δ` of `G_I`
is the set of mixed profiles, `AGT.IsMixedProfile x`.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The vector `h(x) = x + v(x)` of p. 47, where `v(x)ᵢⱼ = uᵢ((i:j); x₋ᵢ)` is the
expected payoff to player `i` of the pure strategy `j` against the other players' part
of `x` (`DGPNash.NashMap.purePayoff`). -/
def hVal (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) (j : S i) : ℝ :=
  x i j + DGPNash.NashMap.purePayoff u x i j

/-- The function `f_{i,x}(t) = ∑_{j ∈ Sᵢ} max(hᵢⱼ(x) − t, 0)` of p. 47. -/
def fSum (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) (t : ℝ) : ℝ :=
  ∑ j : S i, max (hVal u x i j - t) 0

/-- The threshold `tᵢ` of p. 47: the paper's "unique value of `t` where `f_{i,x}(t) = 1`".
It is written as `inf {t | f_{i,x}(t) ≤ 1}`, which needs no existence proof; that this
infimum is the unique root of `f_{i,x}(t) = 1` when `Sᵢ` is nonempty is the theorem
`FixpNash.DivFree.threshold_spec`. -/
noncomputable def threshold (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) : ℝ :=
  sInf {t : ℝ | fSum u x i t ≤ 1}

/-- The map `G_I(x)ᵢⱼ = max(hᵢⱼ(x) − tᵢ, 0)` of p. 47, given by the same formula for
every real vector `x`. -/
noncomputable def G (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) : ∀ i, S i → ℝ :=
  fun i j => max (hVal u x i j - threshold u x i) 0

end FixpNash.DivFree


