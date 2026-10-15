-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
-- name    : OAI_Combinatorics_BooleanFunctions_SmoothSelector
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:27:52.931687+00:00
-- url     : https://prove2.me/theorems/951d49b5-df4d-42c8-8678-a35ead7782af
-- title:
--   A piecewise-linear partition of unity on a uniform grid
-- statement:
--   Fix $N\in\mathbb{N}$ and $\delta\in\mathbb{R}$, and index the grid by $i\in\{0,1,\dots,2N\}$.
--
--   1. **Clip.** $\operatorname{clip}(x)=\max\{0,\min\{1,x\}\}$, the clamp of $x$ to $[0,1]$.
--   2. **Hat functions.**
--   $$\operatorname{hat}_i(t)=\operatorname{clip}\Big(\frac{t}{\delta}+N-i+1\Big)-\operatorname{clip}\Big(\frac{t}{\delta}+N-i\Big).$$
--   For $\delta>0$ this is the triangular bump of height $1$ and half-width $\delta$ centred at $\delta(i-N)$; the sum $\sum_i\operatorname{hat}_i(t)$ lies in $[0,1]$ and equals $1$ for $|t|\le N\delta$.
--   3. **Middle index.** The index $N$.
--   4. **Selector weights.**
--   $$\omega_i(t)=\operatorname{hat}_i(t)+[\,i=N\,]\Big(1-\sum_{j=0}^{2N}\operatorname{hat}_j(t)\Big),$$
--   i.e. the hats, with the mass missing outside $[-N\delta,N\delta]$ assigned to the middle index. The file proves $\sum_{i=0}^{2N}\omega_i(t)=1$ for every $t$.
--   5. **Centres.** $c_i=1+\delta\,(i-N)$; in particular $c_N=1$.
--
--   The file also records that $\operatorname{clip}$, every $\operatorname{hat}_i$ and every $\omega_i$ are continuous. The weights $\omega_i\ge0$ form a continuous partition of unity used as a smooth selector: a value $t$ selects the index $i$ with probability $\omega_i(t)$, and for $\delta>0$, whenever $\operatorname{hat}_i(t)\neq0$ the centre $c_i$ lies within $\delta$ of $1+t$.
--
--   **Formalization Note** Indices are `Fin (2*N+1)` and `middle N` is the index with value `N`. `hat`, `weight` and `center` are defined for every real `δ`; with Lean's convention `t/0 = 0` the case `δ = 0` is degenerate. `weight_sum` and `center_middle` are simp lemmas, and the continuity lemmas are registered for `fun_prop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/SmoothSelector.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/SmoothSelector.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SquareRootDegree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothSelector

def clip (x : ℝ) : ℝ := max 0 (min 1 x)

@[fun_prop] theorem clip_continuous : Continuous clip := by unfold clip; fun_prop

/-- The consecutive ramp differences form an exact finite partition on a grid. -/
def hat (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) : ℝ :=
  clip (t/δ + N - i + 1) - clip (t/δ + N - i)

@[fun_prop] theorem hat_continuous (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) :
    Continuous (hat N δ i) := by unfold hat; fun_prop

def middle (N : ℕ) : Fin (2*N+1) := ⟨N, by omega⟩

def weight (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) : ℝ :=
  hat N δ i t + if i = middle N then 1-∑ j, hat N δ j t else 0

@[fun_prop] theorem weight_continuous (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) :
    Continuous (weight N δ i) := by
  unfold weight
  split_ifs <;> fun_prop

@[simp] theorem weight_sum (N : ℕ) (δ t : ℝ) : ∑ i, weight N δ i t = 1 := by
  simp [weight, Finset.sum_add_distrib]

def center (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) : ℝ := 1+δ*(i-N)

@[simp] theorem center_middle (N : ℕ) (δ : ℝ) : center N δ (middle N) = 1 := by
  simp [center,middle]

end SmoothSelector
end SquareRootDegree

end

end OAI


