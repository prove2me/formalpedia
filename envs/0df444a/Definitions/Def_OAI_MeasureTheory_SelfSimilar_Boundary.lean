-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
-- name    : OAI_MeasureTheory_SelfSimilar_Boundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:44:42.774852+00:00
-- url     : https://prove2.me/theorems/9c5a02dd-9d26-42d5-92af-afe2abe8555d
-- title:
--   Integer increments of shifted floors
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Increment.** For reals $a$ and $u$,
--   $$
--   \mathrm{inc}(a,u)=\lfloor u+a\rfloor-\lfloor u\rfloor,
--   $$
--   the number of grid points crossed when moving from $u$ to $u+a$. Averaging over the shift $u$ relates the grid labels of $x$ and of $x+a$, which bounds how much translation changes grid entropies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Boundary.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Boundary.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace Boundary
open Set

noncomputable def increment (a u : ℝ) : ℝ := (⌊u+a⌋ : ℝ)-(⌊u⌋ : ℝ)

end Boundary

end EntropyRateDimension
end

end OAI


