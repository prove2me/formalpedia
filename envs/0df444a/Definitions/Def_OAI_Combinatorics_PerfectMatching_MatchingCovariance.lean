-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_MatchingCovariance
-- name    : OAI_Combinatorics_PerfectMatching_MatchingCovariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:56:55.867638+00:00
-- url     : https://prove2.me/theorems/1743f628-3d72-4484-bd64-5084a8b9eaf2
-- title:
--   Normalized centered matching indicators on the positive support of a marginal
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$, let $\mathcal M(G)$ be its set of perfect matchings with indicator vectors $\mathbf 1_M\in\{0,1\}^E$, and let $x\in\mathbb{R}^E$ with positive support $E_+(x)=\{e: x_e>0\}$.
--
--   1. *Normalized matching directions.* For $M\in\mathcal M(G)$, $z_M\in\mathbb{R}^{E_+(x)}$ is the vector
--   $$
--   z_M(e)=\frac{\mathbf 1_M(e)-x_e}{\sqrt{x_e}}\qquad(e\in E_+(x)).
--   $$
--   2. *Normalization map.* The linear map $\mathbb{R}^{E_+(x)}\to\mathbb{R}^{E_+(x)}$, $u\mapsto\big(u_e/\sqrt{x_e}\big)_{e\in E_+(x)}$.
--   3. *Score weights.* For $u\in\mathbb{R}^{E_+(x)}$, the edge weights $w(x,u)\in\mathbb{R}^E$ with $w_e=u_e/\sqrt{x_e}$ if $x_e>0$ and $w_e=0$ otherwise.
--
--   If $p$ is a law on $\mathcal M(G)$ with mean $x$, the matrix $\sum_M p_M z_M z_M^{\top}$ is the covariance matrix, restricted to the positive support, of the indicator vector of a $p$-random perfect matching after each coordinate is rescaled by $1/\sqrt{x_e}$. The score weights convert quadratic forms of this matrix into variances of linear scores of matchings. Indeed $\langle u, z_M\rangle=\sum_e w_e\mathbf 1_M(e)-\sum_e w_e x_e$, the linear score of $M$ with weights $w(x,u)$ centered at its $p$-mean. These are the objects whose rank, trace and second variation drive the entropy comparison for perfect matchings.
--
--   **Formalization Note** The names are `matchingNormalized G x`, `normalizeLinear x` and `matchingScoreWeights x u`. Vectors on the positive support are functions on the subtype `{e // 0 < x e}`, and score weights are extended by zero with `positiveExtension`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance

namespace OAI

/-!
Normalized matching covariance: face rank, exact trace, and second variation.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Normalized matching directions on exactly the positive edge support. -/
def matchingNormalized (G : LooplessGraph V E) (x : E → ℝ) :
    G.Matching → {e // 0 < x e} → ℝ :=
  normalizedCentered (fun M e => G.indicator M e.val) (fun e => x e.val)

def normalizeLinear (x : E → ℝ) :
    ({e // 0 < x e} → ℝ) →ₗ[ℝ] ({e // 0 < x e} → ℝ) where
  toFun := fun u e => u e/Real.sqrt (x e.val)
  map_add' := by intro u v; ext e; exact add_div _ _ _
  map_smul' := by intro a u; ext e; exact mul_div_assoc _ _ _

def matchingScoreWeights (x : E → ℝ) (u : {e // 0 < x e} → ℝ) : E → ℝ :=
  LooplessGraph.positiveExtension x (fun e => u e/Real.sqrt (x e.val))

end MatchingEntropy

end

end OAI


