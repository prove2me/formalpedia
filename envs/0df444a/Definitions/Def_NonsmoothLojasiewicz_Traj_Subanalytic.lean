-- Prove2me | Definitions.Def_NonsmoothLojasiewicz_Traj_Subanalytic
-- name    : NonsmoothLojasiewicz_Traj_Subanalytic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:10:11.749787+00:00
-- url     : https://prove2.me/theorems/147e69b5-0dec-4689-be4a-e05b7d915980
-- title:
--   Semianalytic and subanalytic sets, subanalytic functions (Definition 2.1)
-- statement:
--   Let $X$ be a finite-dimensional real normed space (in this mission $X=\mathbb R^n$, $\mathbb R^n\times\mathbb R$ or $X\times\mathbb R^m$).
--
--   1. A subset $A\subseteq X$ is **semianalytic** if every point of $X$ has an open neighbourhood $V$ such that
--   $$A\cap V=\bigcup_{i=1}^{p}\bigcap_{j=1}^{q}\{x\in V:\ f_{ij}(x)=0,\ g_{ij}(x)>0\}$$
--   for finitely many functions $f_{ij},g_{ij}:V\to\mathbb R$ that are real-analytic on $V$.
--   2. A subset $A\subseteq X$ is **subanalytic** if every point of $X$ has a neighbourhood $V$ such that $A\cap V$ is the projection $\{x:\ (x,y)\in B\}$ of a bounded semianalytic subset $B$ of $X\times\mathbb R^m$, for some $m\ge 1$.
--   3. A function $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is **subanalytic** if its graph $\operatorname{Gr} f=\{(x,\lambda)\in\mathbb R^n\times\mathbb R:\ f(x)=\lambda\}$ is a subanalytic subset of $\mathbb R^n\times\mathbb R$.
--
--   Subanalyticity of $f$ is the structural hypothesis $(\mathcal H3)$ of Section 4; it enters the trajectory results only through the Łojasiewicz inequality (20).
--
--   **Formalization Note** The definitions are stated once for any finite-dimensional real normed space. Products carry the sup norm; real-analyticity and boundedness do not depend on the choice of equivalent norm. The neighbourhood in (i) is taken open (every neighbourhood contains an open one, and the description restricts to it), and $p,q\in\mathbb N$ may be $0$ (the empty set is already $\{0=0,\,-1>0\}$). The paper's "$\{x\in\mathbb R^n:(x,y)\in B\}$" is read as the projection of $B$. Functions take values in `EReal` and the graph is taken over the real values only, exactly $\operatorname{Gr} f$.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1207, Definition 2.1 (i)–(iii)

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic

open Topology

namespace NonsmoothLojasiewicz.Traj

/-- Definition 2.1(iii) (p. 1207): a function `f : ℝⁿ → ℝ ∪ {+∞}` is *subanalytic* if its graph
`Gr f = {(x, λ) ∈ ℝⁿ × ℝ : f x = λ}` is a subanalytic subset of `ℝⁿ × ℝ`. -/
def IsSubanalyticFn {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  NonsmoothLojasiewicz.Continuous.IsSubanalytic {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 = ((p.2 : ℝ) : EReal)}

end NonsmoothLojasiewicz.Traj


