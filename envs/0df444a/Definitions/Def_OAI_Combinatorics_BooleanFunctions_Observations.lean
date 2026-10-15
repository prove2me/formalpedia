-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
-- name    : OAI_Combinatorics_BooleanFunctions_Observations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:24:04.749714+00:00
-- url     : https://prove2.me/theorems/5fa51028-10c0-495f-80d6-2bf191dd6bdc
-- title:
--   Cube sum, score and variance of an observation; grouped and standardized observations
-- statement:
--   Let $\Gamma$ be a finite coordinate set, let $\mathbb{B}^\Gamma$ be the Boolean cube with the uniform average $\mathbb{E}$ and signs $\operatorname{sgn}(\mathrm{false})=1$, $\operatorname{sgn}(\mathrm{true})=-1$, and let $F:\mathbb{B}^\Gamma\to B$ be an observation with values in a finite label set $B$. Conditional averages $\mathbb{E}[\,\cdot\mid F]$ are the uniform fibre averages of the conditioning file.
--
--   1. **Cube sum.** $S(x)=\sum_{i\in\Gamma}\operatorname{sgn}(x_i)$.
--   2. **Score.** $\operatorname{sc}_F=\mathbb{E}[S\mid F]$, the average of $S$ over the fibre of $F$ through $x$.
--   3. **Variance.** $V(F)=\mathbb{E}_x\big[\operatorname{sc}_F(x)^2\big]$.
--   4. **Grouped observation.** For a finite set $K$, the observation $F^{(K)}:\mathbb{B}^{K\times\Gamma}\to B^K$ that applies $F$ to every block,
--   $$F^{(K)}(x)=\big(F(x_{j,\cdot})\big)_{j\in K},\qquad x_{j,\cdot}=\big(x(j,i)\big)_{i\in\Gamma}.$$
--   5. **Standardized value and standardized score.** $t_F(b)=V(F)^{-1/2}\,\mathbb{E}[S\mid F=b]$ for a label $b$, and $T_F(x)=t_F(F(x))=\operatorname{sc}_F(x)/\sqrt{V(F)}$.
--
--   Since $\mathbb{E}\,S=0$ and conditioning preserves averages, the score is centred, so $V(F)$ is its variance: it measures how much of the linear statistic $S$ can be predicted from the label $F(x)$. When $V(F)>0$ the standardized score $T_F$ has mean $0$ and second moment $1$, the normalization needed for the central limit theorem. For a real function $f$ on the cube one has $\sum_i\hat f(\{i\})=\mathbb{E}[f\,S]$, which is why the score governs first-order Fourier mass.
--
--   **Formalization Note** These are `Observations.cubeSum`, `score`, `variance`, `grouped`, `standardValue` and `standard`; `variance F` is literally the average of the squared score. If `variance F = 0`, Lean's conventions (`Real.sqrt 0 = 0`, and the inverse of $0$ is $0$) make `standardValue F` identically $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Observations.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Observations.lean by skeleton subtraction
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

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable

variable {γ β κ : Type*} [Fintype γ] [Fintype β] [Fintype κ]
  [DecidableEq γ] [DecidableEq κ]

def cubeSum (x : Cube γ) : ℝ := ∑ i, sign (x i)
def score (F : Cube γ → β) : Cube γ → ℝ := conditionalAverage F cubeSum
def variance (F : Cube γ → β) : ℝ := average (fun x => (score F x)^2)

def grouped (F : Cube γ → β) (x : Cube (κ × γ)) : κ → β :=
  fun j => F (fun i => x (j,i))

def standardValue (F : Cube γ → β) (b : β) : ℝ :=
  (Real.sqrt (variance F))⁻¹*conditionalValue F cubeSum b

def standard (F : Cube γ → β) (x : Cube γ) : ℝ := standardValue F (F x)

end Observations
end SquareRootDegree

end

end OAI


