-- Prove2me | Definitions.Def_FriedgutCoalition_prodLaw
-- name    : FriedgutCoalition_prodLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:29.491174+00:00
-- url     : https://prove2.me/theorems/5468b0b3-e03a-49e5-b97c-db84788d20b2
-- title:
--   Product law $\mathbf X^i$ and pushforward law $f(\mathbf X)$ of a finite distribution
-- statement:
--   Let $\mathbf X$ be a distribution on a finite set $\Omega$, given by its weights. For $i\in\mathbb N$, the product law $\mathbf X^i$ on $\Omega^i$ is
--
--   $$\mathbf X^i(x_1,\dots,x_i)=\prod_{k=1}^i\mathbf X(x_k).$$
--
--   For $f:\Omega\to\Omega'$, the law of $f(\mathbf X)$ is
--
--   $$\Pr[f(\mathbf X)=w]=\sum_{\omega:\,f(\omega)=w}\Pr[\mathbf X=\omega].$$
--
--   These are the distributions compared in the data processing inequality (Fact 2.4) and in Lemma 4.5.
--
--   **Formalization Note** Distributions are weight functions into $\mathbb R$. The statistical distance $|\mathbf X-\mathbf Y|=\tfrac12\sum_\omega|\mathbf X(\omega)-\mathbf Y(\omega)|$ of §2.3 is the published `IsingLTL.BeliefProp.tvDist`, which has exactly this normalization.
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), §2.3, p.7 (f(X) in Fact 2.4); Lemma 4.5, p.14 (Aⁱ, Uʳᵢ)

import Mathlib

namespace FriedgutCoalition

/-!
# Product and pushforward laws of finite distributions

E. Chattopadhyay, M. Gurumukhani, *A Resolution of Friedgut's Conjecture on Influential Coalitions*,
arXiv:2609.16401 (held file sha256 51f298ff…), §2.3, p.7 (`f(X)` in Fact 2.4) and Lemma 4.5, p.14
(`A^i`, `U^i_r`).

**Formalization Note.** Distributions on a finite set are weight functions into `ℝ`. `prodLaw σ i` is
the `i`-fold product `σ^i` on `Fin i → α`, and `pushLaw f X` is the law of `f(X)`:
`Pr[f(X) = w] = ∑_{ω : f ω = w} Pr[X = ω]`. The statistical distance of §2.3 is the published
`IsingLTL.BeliefProp.tvDist` (`½ ∑ |X ω − Y ω|`).
-/

/-- The product law `σ^i` on `Fin i → α`. -/
noncomputable def prodLaw {α : Type*} (σ : α → ℝ) (i : ℕ) : (Fin i → α) → ℝ :=
  fun x => ∏ k, σ (x k)

/-- The law of `f(X)`: `w ↦ ∑_{ω : f ω = w} X ω`. -/
noncomputable def pushLaw {Ω Ω' : Type*} [Fintype Ω] (f : Ω → Ω') (X : Ω → ℝ) : Ω' → ℝ := by
  classical
  exact fun w => ∑ ω ∈ Finset.univ.filter (fun ω => f ω = w), X ω

end FriedgutCoalition


