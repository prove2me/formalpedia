-- Prove2me | Definitions.Def_ParallelHAC_HACRun_StartsLargeMerge
-- name    : ParallelHAC_HACRun_StartsLargeMerge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:57.458411+00:00
-- url     : https://prove2.me/theorems/e4f06339-2892-4cc6-8b28-8c97eabda516
-- title:
--   Why a phase starts: large merge, large size increase, large drift
-- statement:
--   For a phase $j>1$ (notation of Definition 9):
--
--   1. phase $j$ **starts because of a large merge** if $\delta_{s_j}>2\tilde\delta_{j-1}$;
--   2. otherwise it **starts because of a large size increase** if $|X_{s_j}|\ge\tfrac32|\tilde X_{j-1}|$;
--   3. otherwise it **starts because of a large drift**.
--
--   The three causes are exclusive and tried in this order, so every phase after the first has exactly one cause. (The paper notes that in the third case $X_{s_j}$ participates in a merge and $d(\tilde X_{j-1},\bar X_{s_j})>3c_\Delta\tilde\delta_{j-1}$; this follows from the maximality of $f_{j-1}$ and is not part of the definition.)
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.3, p.23 (PDF p.26)

import Mathlib
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_mergeValue
import Definitions.Def_ParallelHAC_HACRun_clusterOf
import Definitions.Def_ParallelHAC_HACRun_phaseEnd

namespace ParallelHAC

/-!
# Why a phase starts (§4.3, p.23)

Source: arXiv:2507.20047 (sha256 a21061c8…), §4.3, p.23.

For `j > 1`, phase `j` starts **because of a large merge** if `δ_{s_j} > 2 δ̃_{j−1}`, **otherwise
because of a large size increase** if `|X_{s_j}| ≥ (3/2)|X̃_{j−1}|`, and **otherwise because of a
large drift**. The three causes are exclusive and tried in this order. (The paper adds that in the
last case `X_{s_j}` participates in a merge and `d(X̃_{j−1}, X̄_{s_j}) > 3 cΔ δ̃_{j−1}`; this is a
consequence of the maximality of `f_{j−1}`, not part of the definition.)
-/

/-- Phase `j` starts because of a large merge: `δ_{s_j} > 2 δ̃_{j−1}` (§4.3, p.23). -/
def HACRun.StartsLargeMerge {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) (j : ℕ) : Prop :=
  2 * R.maxMergeValue (R.phaseStart x₀ cΔ (j - 1)) < R.mergeValue (R.phaseStart x₀ cΔ j)

/-- Phase `j` starts because of a large size increase: not a large merge, and
`|X_{s_j}| ≥ (3/2) |X̃_{j−1}|` (§4.3, p.23). -/
def HACRun.StartsLargeSizeIncrease {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) (j : ℕ) : Prop :=
  ¬ R.StartsLargeMerge x₀ cΔ j ∧
    3 / 2 * ((R.clusterOf x₀ (R.phaseStart x₀ cΔ (j - 1))).card : ℝ) ≤
      ((R.clusterOf x₀ (R.phaseStart x₀ cΔ j)).card : ℝ)

/-- Phase `j` starts because of a large drift: neither of the two causes above (§4.3, p.23). -/
def HACRun.StartsLargeDrift {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) (j : ℕ) : Prop :=
  ¬ R.StartsLargeMerge x₀ cΔ j ∧ ¬ R.StartsLargeSizeIncrease x₀ cΔ j

noncomputable instance {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) :
    DecidablePred (R.StartsLargeMerge x₀ cΔ) := Classical.decPred _

noncomputable instance {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) :
    DecidablePred (R.StartsLargeSizeIncrease x₀ cΔ) := Classical.decPred _

noncomputable instance {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) :
    DecidablePred (R.StartsLargeDrift x₀ cΔ) := Classical.decPred _

end ParallelHAC


