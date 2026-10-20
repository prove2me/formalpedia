-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_FairPairs__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:31:03.452431+00:00
-- url     : https://prove2.me/theorems/5e87ad30-027d-4c2d-a9f2-1a0665b22f27
-- title:
--   Fair pairings of a finite law at dyadic distance bands
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Finite laws.** A finite support of reals with positive probabilities summing to $1$.
--   2. **Edges in a band.** For $\ell\in\mathbb Z$, the pairs $x<y$ in the support with
--   $$
--   2^{-\ell}\le y-x<2^{1-\ell}.
--   $$
--   3. **Feasible weights and capacity.** Nonnegative edge weights whose half-weights incident to each point do not exceed its probability, and the capacity of a band, the largest total weight of a feasible family.
--   4. **Band index.** $-\lfloor\log_2u\rfloor$, the band of a distance $u$.
--   5. **Conditional coupling.** For an observable $g$, the coupling of $\nu$ with itself that pairs $x,y$ in the same cell of $g$ with weight $\nu(x)\nu(y)/\nu(g^{-1}(g(x)))$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FairPairs.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FairPairs.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilarCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Model
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain__SelfSimilarCorollaries

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FairPairs

structure Law where
  support : Finset ℝ
  prob : ℝ → ℝ
  prob_pos : ∀ x ∈ support, 0 < prob x
  prob_sum : ∑ x ∈ support, prob x = 1

noncomputable def Law.edges (ν : Law) (ℓ : ℤ) : Finset (ℝ × ℝ) := by
  classical
  exact (ν.support ×ˢ ν.support).filter fun e =>
    e.1 < e.2 ∧ (2 : ℝ) ^ (-ℓ) ≤ e.2 - e.1 ∧ e.2 - e.1 < (2 : ℝ) ^ (1 - ℓ)

noncomputable def incident {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact ∑ e, ((if e.val.1 = x then w e / 2 else 0) +
      (if e.val.2 = x then w e / 2 else 0))

def Feasible {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) : Prop :=
  (∀ e, 0 ≤ w e) ∧ ∀ x ∈ ν.support, incident w x ≤ ν.prob x

noncomputable def capacity (ν : Law) (ℓ : ℤ) : ℝ :=
  sSup {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t}

noncomputable def bandIndex (u : ℝ) : ℤ := -⌊Real.logb 2 u⌋

noncomputable def conditionalCoupling {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) (x y : ℝ) : ℝ :=
  if g x = g y then ν.prob x * ν.prob y / FiniteEntropy.mass ν.support ν.prob g (g x) else 0

end FairPairs

end EntropyRateDimension

end OAI


