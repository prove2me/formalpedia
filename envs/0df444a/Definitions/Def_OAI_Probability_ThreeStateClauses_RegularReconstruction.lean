-- Prove2me | Definitions.Def_OAI_Probability_ThreeStateClauses_RegularReconstruction
-- name    : OAI_Probability_ThreeStateClauses_RegularReconstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:53:20.830512+00:00
-- url     : https://prove2.me/theorems/9dbac305-d601-4001-88d8-1770f79ea2b8
-- title:
--   The Kesten–Stigum constant $4b\lambda^2/(b\lambda^2-1)$
-- statement:
--   For $b\in\mathbb{N}$ and $\lambda\in\mathbb{R}$, define
--   $$
--   \kappa(b,\lambda)=\frac{4\,b\lambda^2}{b\lambda^2-1}.
--   $$
--
--   When $b\lambda^2>1$ this is a positive constant. It bounds the second moment of the normalized boundary statistic of the $b$-ary broadcast tree uniformly in the depth, and this gives a positive lower bound on the reconstruction advantage above the Kesten–Stigum threshold.
--
--   **Formalization Note** The definition is `ksConstant b lam`. Lean's convention $x/0=0$ applies at $b\lambda^2=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/RegularReconstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/RegularReconstruction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateTreeClauses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_BranchMoments
import Definitions.Def_OAI_Probability_ThreeStateClauses_CompactLimits
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularStatistics
import Definitions.Def_OAI_Probability_ThreeStateClauses_InformationLoss

namespace OAI

/-! Regular Reconstruction. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

def ksConstant (b : ℕ) (lam : ℝ) : ℝ := 4*((b:ℝ)*lam^2)/((b:ℝ)*lam^2-1)

end ThreeState.TreeClauses.Tree

end

end OAI


