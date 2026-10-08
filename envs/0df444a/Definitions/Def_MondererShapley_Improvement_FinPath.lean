-- Prove2me | Definitions.Def_MondererShapley_Improvement_FinPath
-- name    : MondererShapley_Improvement_FinPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:15.478554+00:00
-- url     : https://prove2.me/theorems/7c81702b-18f5-4204-86df-7dfb08d8b18b
-- title:
--   Finite paths and their closed-path data
-- statement:
--   A **finite path** $\gamma=(y_0,\ldots,y_L)$ is a sequence of strategy profiles with a unique deviator $i_k$ at each of its $L$ genuine unilateral steps. For any vector of payoff functions $v$, the path sum is
--
--   $$
--   I(\gamma,v)=\sum_{k=1}^{L}\bigl(v^{i_k}(y_k)-v^{i_k}(y_{k-1})\bigr).
--   $$
--
--   The bundle also defines a closed path ($y_0=y_L$) and a simple closed path (no repetition among $y_0,\ldots,y_{L-1}$). The finite path type supports the reachability relation in Lemma 2.5.
--
--   **Formalization Note** The deviator sequence is stored explicitly; `IsStep` determines it uniquely. A path of length zero is one profile. The sum and closed-path predicates are included for identical definitions across this paper's missions and are unused in this mission.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), pp. 128, 130–131 (PDF pp. 5, 7–8), path, I(γ,v), and closed-path definitions

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsStep

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- A finite path with a distinct unilateral deviator at each step. -/
structure FinPath (Y : ι → Type*) where
  len : ℕ
  pt : Fin (len + 1) → ∀ i, Y i
  dev : Fin len → ι
  step : ∀ k : Fin len, MondererShapley.ClosedPath.IsStep (pt k.castSucc) (pt k.succ) (dev k)

/-- The sum of the deviators' payoff changes along a finite path (p. 130). -/
def FinPath.I (γ : FinPath Y) (v : ι → (∀ i, Y i) → ℝ) : ℝ :=
  ∑ k : Fin γ.len,
    (v (γ.dev k) (γ.pt k.succ) - v (γ.dev k) (γ.pt k.castSucc))

/-- A path whose initial and terminal profiles agree (p. 131). -/
def FinPath.IsClosed (γ : FinPath Y) : Prop :=
  γ.pt 0 = γ.pt (Fin.last γ.len)

/-- A closed path with no repeated vertex before its terminal vertex (p. 131). -/
def FinPath.IsSimpleClosed (γ : FinPath Y) : Prop :=
  γ.IsClosed ∧
    ∀ l k : Fin (γ.len + 1),
      l.val < γ.len → k.val < γ.len → l ≠ k → γ.pt l ≠ γ.pt k

end MondererShapley.Improvement


