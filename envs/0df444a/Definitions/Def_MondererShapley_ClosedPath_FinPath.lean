-- Prove2me | Definitions.Def_MondererShapley_ClosedPath_FinPath
-- name    : MondererShapley_ClosedPath_FinPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:35.975566+00:00
-- url     : https://prove2.me/theorems/9f6a1135-fce5-470c-a045-fbdd65eb97a5
-- title:
--   Finite path, payoff-change sum, and closed-path conditions
-- statement:
--   A **finite path** is a sequence $\gamma=(y_0,\ldots,y_N)$ in which every consecutive pair is a genuine unilateral step. Write $i_k$ for the deviator in step $k$. For a vector of functions $v=(v^i)_{i\in N}$, its path sum is
--
--   $$I(\gamma,v)=\sum_{k=1}^{N}\bigl(v^{i_k}(y_k)-v^{i_k}(y_{k-1})\bigr).$$
--
--   The path is **closed** when $y_0=y_N$ and **simple closed** when it is closed and $y_0,\ldots,y_{N-1}$ are pairwise distinct. Its length is $N$. These are the path objects in all four conditions of Theorem 2.8.
--
--   **Formalization Note** A finite path stores its deviator sequence explicitly, but each deviator is determined by its step. The printed upper limit $n$ in the definition of $I$ on p. 130 is read as $N$, the number of path steps. A length-zero path is one point and has path sum zero.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), pp. 128, 130–131 (PDF pp. 5, 7–8), path and I(γ,v) definitions; https://doi.org/10.1006/game.1996.0044

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsStep

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- A finite path `y₀, …, y_N` with its uniquely determined deviator at each step. -/
structure FinPath (Y : ι → Type*) where
  len : ℕ
  pt : Fin (len + 1) → ∀ i, Y i
  dev : Fin len → ι
  step : ∀ k : Fin len, IsStep (pt k.castSucc) (pt k.succ) (dev k)

/-- Sum of the deviators' payoff changes, Monderer--Shapley p. 130. -/
def FinPath.I (γ : FinPath Y) (v : ι → (∀ i, Y i) → ℝ) : ℝ :=
  ∑ k : Fin γ.len, (v (γ.dev k) (γ.pt k.succ) - v (γ.dev k) (γ.pt k.castSucc))

/-- The initial and terminal vertices coincide. -/
def FinPath.IsClosed (γ : FinPath Y) : Prop := γ.pt 0 = γ.pt (Fin.last γ.len)

/-- The vertices before the repeated terminal vertex are pairwise distinct. -/
def FinPath.IsSimpleClosed (γ : FinPath Y) : Prop :=
  γ.IsClosed ∧ ∀ l k : Fin (γ.len + 1), l.val < γ.len → k.val < γ.len → l ≠ k → γ.pt l ≠ γ.pt k

end MondererShapley.ClosedPath


