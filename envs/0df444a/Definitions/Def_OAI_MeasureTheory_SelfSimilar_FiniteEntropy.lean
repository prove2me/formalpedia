-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
-- name    : OAI_MeasureTheory_SelfSimilar_FiniteEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:40:28.946986+00:00
-- url     : https://prove2.me/theorems/46f65cc6-32fe-426b-9545-e06dd301456f
-- title:
--   Shannon entropy of finite weight functions
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For a finite set $s$ and weights $p$:
--
--   1. **Entropy.** $H(p)=\sum_{a\in s}-p(a)\log p(a)$ (natural logarithm).
--   2. **Image masses and observable entropy.** For a map $f$, $m_f(b)=\sum_{f(a)=b}p(a)$ and the entropy of the image distribution, $H_f(p)=H(m_f)$.
--   3. **Conditional entropy.** $H(f\mid g)=H_{(f,g)}(p)-H_g(p)$.
--   4. **Jensen–Shannon divergence and total variation.**
--   $$
--   \mathrm{JS}(p,q)=H\Bigl(\frac{p+q}2\Bigr)-\frac{H(p)+H(q)}2,\qquad\mathrm{TV}(p,q)=\frac12\sum_a|p(a)-q(a)|.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

noncomputable def entropy {α : Type uα} (s : Finset α) (p : α → ℝ) : ℝ :=
  ∑ i ∈ s, Real.negMulLog (p i)

noncomputable def mass {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (b : β) : ℝ := ∑ a ∈ s.filter (fun a => f a = b), p a

noncomputable def observableEntropy {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α)
    (p : α → ℝ) (f : α → β) : ℝ := entropy (s.image f) (mass s p f)

theorem mass_nonneg {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) (b : β) : 0 ≤ mass s p f b := by
  classical
  exact Finset.sum_nonneg (fun a ha => hp a (Finset.mem_filter.mp ha).1)

theorem mass_sum {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ) (f : α → β) :
    ∑ b ∈ s.image f, mass s p f b = ∑ a ∈ s, p a := by
  classical
  simpa only [mass] using
    (Finset.sum_fiberwise_of_maps_to (s := s)
      (fun a ha => Finset.mem_image_of_mem f ha) p)

theorem sum_mass_mul {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (t : Finset β)
    (p : α → ℝ) (f : α → β) (q : β → ℝ) (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ b ∈ t, mass s p f b * q b = ∑ a ∈ s, p a * q (f a) := by
  classical
  simp only [mass, Finset.sum_mul]
  calc
    _ = ∑ b ∈ t, ∑ a ∈ s.filter (fun a => f a = b), p a * q (f a) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hf _

theorem mass_eq_zero_of_not_mem {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α)
    (p : α → ℝ) (f : α → β) {b : β} (hb : b ∉ s.image f) : mass s p f b = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  exact (hb (Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1,
    (Finset.mem_filter.mp ha).2⟩)).elim

theorem mass_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ) (c : γ) :
    mass (s.image f) (mass s p f) g c = mass s p (g ∘ f) c := by
  classical
  have h := sum_mass_mul s (s.image f) p f (fun b => if g b = c then 1 else 0)
    (fun a ha => Finset.mem_image_of_mem f ha)
  simpa only [mass, Finset.sum_filter, mul_ite, mul_one, mul_zero, Function.comp_apply] using h

theorem observableEntropy_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ) :
    observableEntropy s p (g ∘ f) = observableEntropy (s.image f) (mass s p f) g := by
  classical
  simp only [observableEntropy, entropy, Finset.image_image, mass_comp]

noncomputable def conditionalEntropy {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) : ℝ :=
  observableEntropy s p (fun a => (f a, g a)) - observableEntropy s p g

noncomputable def js {α : Type uα} (s : Finset α) (p q : α → ℝ) : ℝ :=
  entropy s (fun a => (p a+q a)/2)-(entropy s p+entropy s q)/2

noncomputable def totalVariation {α : Type uα} (s : Finset α) (p q : α → ℝ) : ℝ :=
  (∑ a ∈ s, |p a-q a|)/2

end FiniteEntropy
end EntropyRateDimension
end

end OAI


