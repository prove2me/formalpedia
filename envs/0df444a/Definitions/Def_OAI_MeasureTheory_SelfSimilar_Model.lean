-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_Model
-- name    : OAI_MeasureTheory_SelfSimilar_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:18:03.764375+00:00
-- url     : https://prove2.me/theorems/81151980-1173-4aad-b6cd-8221b0bfa338
-- title:
--   Composed maps, walk entropy, entropy rate and Lyapunov exponent
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For a self-similar system and $n\in\mathbb N$:
--
--   1. **Composed maps and word weights.** A word $w$ of length $n$ gives the composed affine map $f_{w_0}\circ\cdots\circ f_{w_{n-1}}$, recorded as its pair (slope, offset), and the weight $\prod_jw_{w_j}$.
--   2. **Map masses.** The finite set of distinct composed maps of length $n$, and for each such map $g$ the mass $m_n(g)$, the total weight of the words producing $g$.
--   3. **Walk entropy and entropy rate.** $H_n=-\sum_gm_n(g)\log_2m_n(g)$, and
--   $$
--   h=\inf_{n\ge1}\frac{H_n}{n},
--   $$
--   the entropy rate of the random walk on composed maps, which accounts for exact overlaps.
--   4. **Lyapunov exponent.** $\chi=-\sum_iw_i\log_2|r_i|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilarCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilarCorollaries

namespace OAI

universe uι

section

open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension

namespace System
variable {ι : Type uι} [Fintype ι]

def completeMap (S : System ι) {n : ℕ} (w : Fin n → ι) : ℝ × ℝ :=
  S.wordAffine (List.ofFn w)

noncomputable def wordWeight (S : System ι) {n : ℕ} (w : Fin n → ι) : ℝ :=
  ∏ j, S.weight (w j)

noncomputable def mapSupport (S : System ι) (n : ℕ) : Finset (ℝ × ℝ) := by
  classical
  exact Finset.univ.image (S.completeMap (n := n))

noncomputable def mapMass (S : System ι) (n : ℕ) (g : ℝ × ℝ) : ℝ := by
  classical
  exact ∑ w ∈ (Finset.univ : Finset (Fin n → ι)).filter (S.completeMap · = g),
    S.wordWeight w

noncomputable def walkEntropy (S : System ι) (n : ℕ) : ℝ :=
  (∑ g ∈ S.mapSupport n, Real.negMulLog (S.mapMass n g)) / Real.log 2

noncomputable def entropyRate (S : System ι) : ℝ :=
  sInf (Set.range fun n : ℕ => S.walkEntropy (n + 1) / (n + 1 : ℕ))

noncomputable def lyapunov (S : System ι) : ℝ :=
  -(∑ i, S.weight i * (Real.log |S.ratio i| / Real.log 2))

end System
end EntropyRateDimension
end

end OAI


