-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Padding
-- name    : TarskiBootstrap_Dimensional_Padding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:17:01.653828+00:00
-- url     : https://prove2.me/theorems/951482f1-a677-4da7-9258-394ff7e0aef1
-- title:
--   Extremal padding from the antichain
-- statement:
--   For a subset $A\subset[n]^k$ with downward closure $D$, define
--
--   $$T(x)=\begin{cases}\bot&x\in D,\\\top&x\notin D,\end{cases}$$
--
--   where $\bot=(0,\ldots,0)$ and $\top=(n-1,\ldots,n-1)$. The same padding function is used at every hidden suffix block of the chain. Antichain and fixed-point assumptions are supplied by the theorems, rather than stored in this definition.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Equation (3.1), PDF/printed p. 11, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Grid
import Definitions.Def_TarskiBootstrap_Dimensional_DownwardClosure

open scoped Matrix

namespace TarskiBootstrap.Dimensional

/-- Equation (3.1), p. 11: bottom in the downward closure, top outside. -/
noncomputable def padding {n k : ℕ+} (A : Set (Grid n k)) (x : Grid n k) : Grid n k := by
  classical
  exact if x ∈ downwardClosure A then ⊥ else ⊤

end TarskiBootstrap.Dimensional


