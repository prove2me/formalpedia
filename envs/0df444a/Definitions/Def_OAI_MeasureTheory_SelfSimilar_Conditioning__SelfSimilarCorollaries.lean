-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_Conditioning__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:21:23.386376+00:00
-- url     : https://prove2.me/theorems/17116495-3420-4cb9-99d4-2623d141e474
-- title:
--   Conditioning on a tag and the induced finite laws
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Laws of observables.** For positive weights on a finite set summing to $1$ and a real observable $f$, the finite law of $f$; its grid entropy is the entropy of $\lfloor f/\rho\rfloor$.
--   2. **Fibres and posteriors.** For a tag map, the fibre of $a$ (elements with the same tag), its mass, and the posterior
--   $$
--   p(v\mid a)=\frac{p(v)}{p(\mathrm{fiber}(a))}\,[\mathrm{tag}(v)=\mathrm{tag}(a)],
--   $$
--   which is nonnegative and sums to $1$.
--   3. **Conditional law.** The finite law of $f$ under the posterior on the fibre of $a$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Conditioning.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Conditioning.lean by skeleton subtraction
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound__SelfSimilarCorollaries

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ

namespace EntropyRateDimension.FairPairs
open MeasureTheory FiniteEntropy
open scoped BigOperators ENNReal

noncomputable def Law.ofObservable {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) : Law := by
  classical
  exact ⟨s.image f, mass s p f, by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.sum_pos' (fun a ha => (hp a (Finset.mem_filter.mp ha).1).le)
      ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩,hp a ha⟩,
    (mass_sum s p f).trans hp1⟩

@[simp] theorem Law.ofObservable_support {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) :
    (Law.ofObservable s p hp hp1 f).support=s.image f := rfl

@[simp] theorem Law.ofObservable_prob {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) :
    (Law.ofObservable s p hp hp1 f).prob=mass s p f := rfl

@[simp] theorem Law.ofObservable_entropy {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) :
    (Law.ofObservable s p hp hp1 f).shannonEntropy=observableEntropy s p f/Real.log 2 := rfl

@[simp] theorem Law.ofObservable_gridEntropy {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ) (ρ : ℝ) :
    (Law.ofObservable s p hp hp1 f).gridEntropy ρ=
      observableEntropy s p (fun a => ⌊f a/ρ⌋)/Real.log 2 := by
  classical
  unfold Law.gridEntropy
  change observableEntropy (s.image f) (mass s p f) (fun x => ⌊x/ρ⌋)/_=_
  rw [← observableEntropy_comp]
  rfl

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.FiniteCondition
open FiniteEntropy FairPairs MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def fiber (tag : α → β) (a : α) : Finset α :=
  Finset.univ.filter (fun v => tag v=tag a)

noncomputable def mass (p : α → ℝ) (tag : α → β) (a : α) : ℝ :=
  ∑ v ∈ fiber tag a, p v

theorem mass_pos (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) :
    0 < mass p tag a := by
  classical
  exact Finset.sum_pos' (fun v _ => (hp v).le) ⟨a,by simp [fiber],hp a⟩

noncomputable def posterior (p : α → ℝ) (tag : α → β) (a v : α) : ℝ :=
  if tag v=tag a then p v/mass p tag a else 0

theorem posterior_nonneg (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a v : α) :
    0 ≤ posterior p tag a v := by
  unfold posterior
  split_ifs
  · exact (div_pos (hp v) (mass_pos p hp tag a)).le
  · rfl

theorem posterior_sum (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) :
    ∑ v, posterior p tag a v=1 := by
  classical
  simp only [posterior,← Finset.sum_filter,← Finset.sum_div]
  change mass p tag a / mass p tag a=1
  exact div_self (mass_pos p hp tag a).ne'

theorem fiber_normalized_sum (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) :
    ∑ v ∈ fiber tag a, p v/mass p tag a=1 := by
  rw [← Finset.sum_div]
  exact div_self (mass_pos p hp tag a).ne'

noncomputable def law (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α) (f : α → ℝ) : Law :=
  Law.ofObservable (fiber tag a) (fun v => p v/mass p tag a)
    (fun v _ => div_pos (hp v) (mass_pos p hp tag a)) (fiber_normalized_sum p hp tag a) f

end EntropyRateDimension.FiniteCondition

end OAI


