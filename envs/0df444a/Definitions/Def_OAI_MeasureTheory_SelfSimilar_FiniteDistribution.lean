-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
-- name    : OAI_MeasureTheory_SelfSimilar_FiniteDistribution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:41:19.668252+00:00
-- url     : https://prove2.me/theorems/053ba853-0b50-439d-80a0-097d589bccd6
-- title:
--   Finitely supported probability distributions
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Finite distribution.** Nonnegative weights on a type, vanishing off a finite support, with total mass $1$.
--   2. **Entropy, total variation, mixture and Jensen–Shannon divergence.** $H(p)=\sum_a-p(a)\log p(a)$, $\mathrm{TV}(p,q)=\frac12\sum_a|p(a)-q(a)|$, the even mixture $\frac{p+q}2$, and
--   $$
--   \mathrm{JS}(p,q)=H\Bigl(\frac{p+q}2\Bigr)-\frac{H(p)+H(q)}2 .
--   $$
--   3. **Pushforward and translation.** The image of $p$ under a map, and for distributions on $\mathbb Z$ the translate by $j$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteDistribution.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteDistribution.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension

structure FiniteDistribution (α : Type uα) where
  weight : α → ℝ
  support : Finset α
  nonneg : ∀ a, 0 ≤ weight a
  vanish : ∀ a ∉ support, weight a=0
  sum_one : ∑ a ∈ support, weight a=1

namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

noncomputable def entropy {α : Type uα} (p : FiniteDistribution α) : ℝ :=
  ∑' a, Real.negMulLog (p.weight a)

noncomputable def tv {α : Type uα} (p q : FiniteDistribution α) : ℝ :=
  (∑' a, |p.weight a-q.weight a|)/2

theorem sum_on {α : Type uα} (p : FiniteDistribution α) (s : Finset α)
    (hs : p.support ⊆ s) : ∑ a ∈ s, p.weight a=1 := by
  rw [← p.sum_one]
  exact (Finset.sum_subset hs (fun a _ ha => p.vanish a ha)).symm

noncomputable def mix {α : Type uα} (p q : FiniteDistribution α) : FiniteDistribution α := by
  classical
  refine ⟨fun a => (p.weight a+q.weight a)/2,p.support ∪ q.support,
    fun a => div_nonneg (add_nonneg (p.nonneg a) (q.nonneg a)) (by norm_num), ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_union, not_or] at ha
    rw [p.vanish a ha.1, q.vanish a ha.2]
    norm_num
  · rw [← Finset.sum_div, Finset.sum_add_distrib,
      p.sum_on _ Finset.subset_union_left, q.sum_on _ Finset.subset_union_right]
    norm_num

noncomputable def js {α : Type uα} (p q : FiniteDistribution α) : ℝ :=
  (p.mix q).entropy-(p.entropy+q.entropy)/2

noncomputable def map {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β) : FiniteDistribution β := by
  classical
  refine ⟨FiniteEntropy.mass p.support p.weight f,p.support.image f,
    FiniteEntropy.mass_nonneg _ _ _ (fun a _ => p.nonneg a), ?_, ?_⟩
  · exact fun b hb => FiniteEntropy.mass_eq_zero_of_not_mem p.support p.weight f hb
  · exact (FiniteEntropy.mass_sum ..).trans p.sum_one

noncomputable def translate (p : FiniteDistribution ℤ) (j : ℤ) : FiniteDistribution ℤ :=
  p.map (fun a => a+j)

end FiniteDistribution

end EntropyRateDimension
end

end OAI


