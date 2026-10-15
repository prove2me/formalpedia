-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_Amplification
-- name    : OAI_Combinatorics_BooleanFunctions_Amplification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:40:03.04792+00:00
-- url     : https://prove2.me/theorems/578257b5-294d-4335-b698-1bb45d81edb4
-- title:
--   Observations of bounded cell degree, their variance-to-cost ratio, and the one-coordinate base case
-- statement:
--   An *observation* in the sense of this file is a bundle consisting of a finite coordinate set $\Gamma$ (with decidable equality), a finite label set $B$, a map $F:\mathbb{B}^\Gamma\to B$ and a cost $D\in\mathbb{N}$ with $D>0$, such that every cell indicator has Fourier degree at most the cost and the score has positive variance:
--   $$\deg\big(\mathbf 1_{F=b}\big)\le D\ \text{ for all } b\in B,\qquad V(F)=\mathbb{E}\big[\mathbb{E}[S\mid F]^2\big]>0,$$
--   where $S(x)=\sum_i\operatorname{sgn}(x_i)$ is the cube sum and averages are uniform. The file then defines:
--
--   1. **Ratio.** $\operatorname{ratio}(F)=V(F)/D$.
--   2. **Cost factor.** $q=2N_\ast+2$ with $N_\ast=2^{1024}$; it is the number of leaves plus one.
--   3. **Amplification factor.** $\lambda=1+\eta/q$, where $\eta$ is the Gaussian improvement constant.
--   4. **Identity variance.** The lemma that the identity map of the one-coordinate cube $\mathbb{B}^{\{0\}}$ has variance $1$ (its score is the cube sum, which is $\pm1$).
--   5. **Base observation.** The identity observation on $\mathbb{B}^{\{0\}}$, with label set $\mathbb{B}^{\{0\}}$ and cost $1$ (its cells are point indicators depending on the single coordinate).
--
--   Every real function of an observation of cost $D$ has Fourier degree at most $D$, so the ratio compares the information that $F$ carries about the cube sum with the degree price of reading it out. The construction iterates a step that multiplies the ratio by more than $\lambda>1$, starting from the base observation of ratio $1$, so that ratios become arbitrarily large.
--
--   **Formalization Note** `Amplification.Observation` is a structure with fields `Coord`, `Label`, `map`, `cost`, `cost_pos`, `cell_le`, `variance_pos` and instance fields for `Fintype` and `DecidableEq`. The other names are `ratio`, `costFactor` (defined as `2*gridN+2`), `factor` (defined as `1+eta/costFactor`), the lemma `identity_variance`, and `base`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Amplification.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Amplification.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Rounding
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_CellDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Grouping

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Amplification
open Observations Switching GaussianGain MomentTransfer
attribute [local instance] Classical.propDecidable

structure Observation where
  Coord : Type
  [coordFintype : Fintype Coord]
  [coordDecidableEq : DecidableEq Coord]
  Label : Type
  [labelFintype : Fintype Label]
  map : Cube Coord → Label
  cost : ℕ
  cost_pos : 0 < cost
  cell_le : ∀ b, fourierDegree (cell map b) ≤ cost
  variance_pos : 0 < variance map

attribute [instance] Observation.coordFintype Observation.coordDecidableEq Observation.labelFintype

def ratio (F : Observation) : ℝ := variance F.map/F.cost

def costFactor : ℕ := 2*gridN+2

def factor : ℝ := 1+eta/costFactor

theorem identity_variance : variance (id : Cube (Fin 1) → Cube (Fin 1)) = 1 := by
  have hs : score (id : Cube (Fin 1) → Cube (Fin 1)) = cubeSum :=
    Projection.conditional_comp id cubeSum
  unfold Observations.variance
  rw [hs]
  simp only [cubeSum,Fin.sum_univ_one,sign_sq]
  exact average_const 1

def base : Observation where
  Coord := Fin 1
  Label := Cube (Fin 1)
  map := id
  cost := 1
  cost_pos := Nat.zero_lt_one
  cell_le := fun b => by
    have hd : fourierDegree (cell id b) ≤ (Finset.univ : Finset (Fin 1)).card := by
      apply fourierDegree_le_card_of_dependsOn
      intro x y h
      have he : x = y := funext fun i => h i (Finset.mem_univ i)
      rw [he]
    simpa using hd
  variance_pos := by rw [identity_variance]; exact zero_lt_one

end Amplification
end SquareRootDegree

end

end OAI


