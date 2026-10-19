-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_Scales
-- name    : OAI_Probability_CriticalZ3_Scales
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:17:38.456197+00:00
-- url     : https://prove2.me/theorems/d76dc0c1-aa6a-4337-8c40-b8b9d098c4e3
-- title:
--   Scale data for the critical percolation argument
-- statement:
--   The numerical parameters of the finite-size criterion for bond or site percolation on $\mathbb Z^3$.
--
--   1. **Uniform notation.** The law, the events $\{|\mathcal C(x)|=\infty\}$ and the seed events are defined for both models. The contour error is $\varepsilon_0=\frac12\cdot10^{-14}$, which lies in $(0,\frac12)$.
--   2. **Scale data.** Scale data for a model consist of $0<p<1$ and $q\in(\frac p2,p)$, tolerances $\delta,\eta,\tau,\gamma\in(0,1)$, and integers $\mathrm{seed},K,R,r>0$, subject to:
--   - $\delta+52\eta/\delta<\varepsilon_0$, $\tau<\eta/4$, $\gamma<\delta$ and $2\gamma/\tau<\eta/4$;
--   - $\mathrm{seed}<R$ and $100(R+1)<r$;
--   - trial budgets: $4/(K(p/2)^{N+1})<\eta/4$, where $N$ is the number of bits in a seed cube, and a similar bound in terms of $(1-p)^{K(8\,\mathrm{seed}+5)^3}$ and $R-\mathrm{seed}$.
--   3. **Face crossing.** For $n\in\{2r,2r+1,10r\}$, every centre $c$ and every quarter-face $f$,
--   $$
--   \mathbb P_q\bigl(\Lambda_{\mathrm{seed}}(c)\leftrightarrow\text{quarter-face }f\text{ of }\Lambda_n(c)\ \text{inside }\Lambda_n(c)\bigr)>1-\gamma .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Scales.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Scales.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality

namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

open Filter Topology
namespace CriticalScales

noncomputable def contourError : ℝ := (1/100 : ℝ)^7/2

theorem contourError_pos : 0 < contourError := by norm_num [contourError]
theorem contourError_lt_half : contourError < 1/2 := by norm_num [contourError]

end CriticalScales

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace Model
noncomputable def law : (m : Model) → ℝ → Measure m.Config
  | .bond,p => bondLaw p
  | .site,p => siteLaw p

def InfiniteAt : (m : Model) → Vertex → Set m.Config
  | .bond,x => bondInfiniteAt x
  | .site,x => siteInfiniteAt x

def SeedInfinite : (m : Model) → Vertex → ℕ → Set m.Config
  | .bond,c,r => bondSeedInfinite c r
  | .site,c,r => siteSeedInfinite c r

instance law_probability (m : Model) (p : ℝ) : IsProbabilityMeasure (m.law p) := by
  cases m <;> dsimp [law] <;> infer_instance

end Model

structure ScaleData (model : Model) where
  p : ℝ
  p_pos : 0 < p
  p_lt_one : p < 1
  q : Set.Icc (0 : ℝ) 1
  q_half : p/2 < (q : ℝ)
  q_lt : (q : ℝ) < p
  δ : ℝ
  η : ℝ
  τ : ℝ
  γ : ℝ
  δ_range : δ ∈ Set.Ioo 0 1
  η_range : η ∈ Set.Ioo 0 1
  τ_range : τ ∈ Set.Ioo 0 1
  γ_range : γ ∈ Set.Ioo 0 1
  failure_budget : δ+52*η/δ < CriticalScales.contourError
  relay_budget : τ < η/4
  γδ : γ < δ
  trial_budget : 2*γ/τ < η/4
  seed : ℕ
  K : ℕ
  R : ℕ
  r : ℕ
  seed_pos : 0 < seed
  K_pos : 0 < K
  seed_R : seed < R
  large_r : 100*(R+1) < r
  K_budget : 4/((K:ℝ)*(p/2)^(Box.seedCard model seed+1)) < η/4
  R_budget : 1/((1-p)^(K*(8*seed+5)^3)*(R-seed:ℕ)) < η/4
  faces : ∀ n ∈ ({2*r,2*r+1,10*r} : Finset ℕ), ∀ c f,
    1-γ < (ProductCylinder.law (fun _ : model.Bit => q)).real
      (model.SeedReaches c seed n (QuarterFace c n f))

namespace ScaleData
variable {model : Model} (s : ScaleData model)

end ScaleData
end CriticalZ3

end OAI


