-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_ExposureEntropy
-- name    : OAI_Probability_ThorpCompatibility_ExposureEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:33:57.76781+00:00
-- url     : https://prove2.me/theorems/fb6773a0-5c90-4bc4-8ad3-faa13621d053
-- title:
--   Total exposure error of the grid entropy estimate
-- statement:
--   For natural numbers $A,D$ and real parameters $H,K$, the total exposure error is
--   $$
--   E_{A,D}(H,K)=A\,(1+\log D)+2\,D\,K\,H\,(1+\log D)\,\mathcal H_A,
--   $$
--   where $\mathcal H_A=\sum_{j=1}^{A}\frac1j$ is the $A$-th harmonic number and $\mathcal H_0=0$.
--
--   For $D\ge 1$, this is the sum of the per-entry exposure errors $\frac{1+\log D}{D}+\frac{2KH}{A-i}(1+\log D)$ over all columns $k\in[D]$ and rows $i\in[A]$, since $\sum_{i=0}^{A-1}\frac{1}{A-i}=\mathcal H_A$. It is the total entropy lost to exposure effects in the lower bound for the entropy of a law on compatible grid configurations. With $H=K=m^{1/100}$ and $A,D\le 2m$, it is at most a constant multiple of $m^{1.04}$, which is negligible compared with the main term $AD=m^2$.
--
--   **Formalization Note** The definition is `totalExposureError A D H K`. It uses Mathlib's rational harmonic numbers `harmonic A`, cast to $\mathbb{R}$. $\log$ is the natural logarithm, with $\log 0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ExposureEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ExposureEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

noncomputable def totalExposureError (A D : ℕ) (H K : ℝ) : ℝ :=
  A * (1 + Real.log (D : ℝ)) +
    2 * D * K * H * (1 + Real.log (D : ℝ)) * (harmonic A : ℝ)

end ThorpCompatibility

end OAI


