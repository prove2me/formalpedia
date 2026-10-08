-- Prove2me | Definitions.Def_TwinWidthI_MinorFree_Setting
-- name    : TwinWidthI_MinorFree_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:38.67898+00:00
-- url     : https://prove2.me/theorems/31c4f00b-cbe7-4266-855d-42a2297cbcc4
-- title:
--   pp. 3:9, 3:26 — the adjacency matrix A_σ(G) and the constants g(t), f(t) of Theorem 6.3
-- statement:
--   Let $G$ be a finite graph and let $\sigma$ be a total ordering $v_1,\dots,v_n$ of its vertices. The **adjacency matrix of $G$ in the order $\sigma$**, $A_\sigma(G)$, is the $n\times n$ $0/1$ matrix whose entry in the $i$-th row and $j$-th column is $1$ if $v_iv_j\in E(G)$ and $0$ otherwise (p. 3:9); its diagonal is $0$.
--
--   With the Marcus–Tardos constant $c_k=\frac{8}{3}(k+1)^2 2^{4k}$ (Theorem 5.4), the constants of the minor-free bound are
--
--   $$
--   g(t)=2\bigl(2^{4t+1}+2\bigr)^2,\qquad f(t)=4c_{g(t)}\,2^{4c_{g(t)}+2}.
--   $$
--
--   Graph twin-width (partition form), mixed and grid minors and $c_k$ come from the series' shared definitions `TwinWidthI.BoolWidth.Setting` and `TwinWidthI.GridThm.Setting`; this file adds only $A_\sigma(G)$ and the two constants used by Theorem 6.3.
--
--   **Formalization Note** The order $\sigma$ is an equivalence $V\simeq\mathrm{Fin}\,n$ with $v_{i+1}=\sigma^{-1}(i)$; entries are `Bool`, `true` for $1$. The proof on p. 3:26 defines $g(t):=2h(t)^2$ with $h(t)=2^{4t+1}+2$, which is what `gMF` encodes; the printed statement of Theorem 6.3 has $+1$ instead of $+2$. $f$ is real-valued (real exponent); the goal compares the natural-number twin-width with $\lfloor f(t)\rfloor$.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), pp. 3:9, 3:12, 3:16–3:19, 3:26–3:29, §§2.1, 3, 5, 6.3

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting
import Definitions.Def_TwinWidthI_GridThm_Setting

namespace TwinWidthI.MinorFree

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency matrix of `G` in the vertex order `σ`. -/
noncomputable def adjMat {n : ℕ} (G : SimpleGraph V) (σ : V ≃ Fin n) :
    Matrix (Fin n) (Fin n) Bool := by
  classical
  exact fun i j => decide (G.Adj (σ.symm i) (σ.symm j))

/-- The proof's `g(t)=2h(t)^2`, with `h(t)=2^(4t+1)+2`; the printed statement has `+1`. -/
def gMF (t : ℕ) : ℕ := 2 * (2 ^ (4 * t + 1) + 2) ^ 2

/-- The explicit graph twin-width bound applied at the end of Theorem 6.3. -/
noncomputable def fMF (t : ℕ) : ℝ :=
  4 * TwinWidthI.GridThm.cMT (gMF t) * (2 : ℝ) ^ (4 * TwinWidthI.GridThm.cMT (gMF t) + 2)

end TwinWidthI.MinorFree


