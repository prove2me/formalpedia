-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
-- name    : OAI_MeasureTheory_SelfSimilar_TranslationGain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:46:25.41476+00:00
-- url     : https://prove2.me/theorems/94342658-db00-4e22-ae41-2f14d7460ff6
-- title:
--   Information gained by mixing a measure with a translate
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Information of a pair.** For measures $\mu,\nu$ and an observable $f$, the Jensen–Shannon type quantity
--   $$
--   I_f(\mu,\nu)=H_f\Bigl(\frac{\mu+\nu}2\Bigr)-\frac{H_f(\mu)+H_f(\nu)}2\ \ge0 .
--   $$
--   2. **Grid information.** For a translation $v$ and a grid of mesh $s$ shifted by $u$, $I_{\ell_{s,u}}\bigl(\mu,\mu(\cdot-v)\bigr)$, the entropy gained on the grid by averaging $\mu$ with its translate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/TranslationGain.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/TranslationGain.lean by skeleton subtraction
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

attribute [local instance] Classical.propDecidable

noncomputable def information {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    (μ ν : Measure α) (f : α → β) : ℝ :=
  entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) f-(entropy μ f+entropy ν f)/2

noncomputable def gridInformation (μ : Measure ℝ) (v s u : ℝ) : ℝ :=
  information μ (μ.map (fun x => x+v)) (label s u)

end MeasureEntropy

end EntropyRateDimension

end

end OAI


