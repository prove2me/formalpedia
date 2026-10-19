-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
-- name    : OAI_MeasureTheory_SelfSimilar_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:39:37.093843+00:00
-- url     : https://prove2.me/theorems/eaa1c48b-3ea1-4b10-87e6-dcd6565f9af7
-- title:
--   Basic facts on word weights and walk masses
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Word weights.** For a word $w$ of length $n$, $w(w)=\prod_jw_{w_j}>0$, and these weights sum to $1$ over all words of length $n$.
--   2. **Map masses.** The masses of the distinct composed maps of length $n$ (the total weight of words producing each map) are positive on the support and sum to $1$:
--   $$
--   \sum_{g}m_n(g)=1 .
--   $$
--   3. **Uniform bounds.** There are $0<c<1$ and $T\ge0$ with $|r_i|\le c$ and $|b_i|\le T$ for all $i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilar

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem weight_nonneg (S : System ι) (i : ι) : 0 ≤ S.weight i :=
  (S.weight_pos i).le

theorem wordWeight_pos (S : System ι) {n : ℕ} (w : Fin n → ι) :
    0 < S.wordWeight w :=
  Finset.prod_pos (fun i _ => S.weight_pos (w i))

theorem wordWeight_sum (S : System ι) (n : ℕ) :
    ∑ w : Fin n → ι, S.wordWeight w = 1 := by
  classical
  simpa [wordWeight, S.weight_sum] using
    (Fintype.prod_sum (fun (_ : Fin n) i => S.weight i)).symm

theorem mapMass_sum (S : System ι) (n : ℕ) :
    ∑ g ∈ S.mapSupport n, S.mapMass n g = 1 := by
  classical
  simp only [mapSupport, mapMass]
  rw [Finset.sum_fiberwise_of_maps_to]
  · exact S.wordWeight_sum n
  · exact fun w hw => Finset.mem_image_of_mem _ hw

theorem mapMass_pos (S : System ι) {n : ℕ} {g : ℝ × ℝ}
    (hg : g ∈ S.mapSupport n) : 0 < S.mapMass n g := by
  classical
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hg
  apply lt_of_lt_of_le (S.wordWeight_pos w)
  apply Finset.single_le_sum (fun v _ => (S.wordWeight_pos v).le)
  simp

end System

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem exists_uniform_bounds (S : System ι) :
    ∃ c T : ℝ, 0 < c ∧ c < 1 ∧ 0 ≤ T ∧
      (∀ i, |S.ratio i| ≤ c) ∧ (∀ i, |S.offset i| ≤ T) := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i => |S.ratio i|)
    Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun i => |S.offset i|)
    Finset.univ_nonempty
  exact ⟨|S.ratio i|, |S.offset j|, S.ratio_pos i, S.ratio_lt_one i,
    abs_nonneg _, fun k => hi k (Finset.mem_univ k), fun k => hj k (Finset.mem_univ k)⟩

end System

end EntropyRateDimension
end

end OAI


