-- Prove2me | Definitions.Def_LinearZeroSumMG_IsLinearMG
-- name    : LinearZeroSumMG_IsLinearMG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:18.290684+00:00
-- url     : https://prove2.me/theorems/8ff43c62-fa1e-4b7f-a134-ce33db2c566b
-- title:
--   Assumption 1 (Linearity and Boundedness)
-- statement:
--   A game satisfies **Assumption 1** with feature map $\phi:\mathcal S\times\mathcal A\times\mathcal A\to\mathbb R^d$, vectors $\theta_h\in\mathbb R^d$ and signed measures $\mu_h=(\mu_h^{(1)},\dots,\mu_h^{(d)})$ on $\mathcal S$ if $\phi$ is measurable with $\|\phi(x,a,b)\|\le1$ everywhere and, for every step $h\in[H]$:
--   1. $r_h(x,a,b)=\phi(x,a,b)^\top\theta_h$ for all $(x,a,b)$;
--   2. $\mathbb P_h(B\mid x,a,b)=\sum_{i=1}^d\phi_i(x,a,b)\,\mu_h^{(i)}(B)$ for every measurable $B\subseteq\mathcal S$;
--   3. $\|\theta_h\|\le\sqrt d$;
--   4. for every measurable $v:\mathcal S\to[-1,1]$,
--   $$
--   \Big\|\Big(\int v\,\mathrm d\mu_h^{(1)},\dots,\int v\,\mathrm d\mu_h^{(d)}\Big)\Big\|\le\sqrt d .
--   $$
--
--   The feature map is known to the learner; $\theta_h$ and $\mu_h$ are not. Under this assumption every action-value function is linear in $\phi$ (Lemma 1), which is what makes least-squares value iteration with $d$-dimensional features possible.
--
--   **Formalization Note** Condition 4 is the reading of the printed normalization $\|\mu_h(\mathcal S)\|\le\sqrt d$ under which the paper's proofs go through: it is exactly the bound $\|\int V\,\mathrm d\mu_h\|\le H\sqrt d$ for $|V|\le H$ used in the proofs of Lemmas 3 and 7. Taking $v\equiv1$ recovers the printed bound, and the total-variation normalization implies condition 4. Read literally (net masses), the printed assumption makes Lemma 7 false. Integrals against a signed measure are taken through its Jordan decomposition. The vectors $\theta_h$ and measures $\mu_h$ are arguments; theorems quantify over them.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §2.2.2, Assumption 1, p.7

import Mathlib
import Definitions.Def_LinearZeroSumMG_MarkovGame
import Definitions.Def_LinearZeroSumMG_clip

namespace LinearZeroSumMG

open MeasureTheory ProbabilityTheory Matrix

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The integral `∫ v dm = ∫ v dm⁺ − ∫ v dm⁻` of a real function against a finite signed measure
`m`, through its Jordan decomposition `m = m⁺ − m⁻`. -/
noncomputable def sIntegral (v : S → ℝ) (m : SignedMeasure S) : ℝ :=
  ∫ y, v y ∂m.toJordanDecomposition.posPart - ∫ y, v y ∂m.toJordanDecomposition.negPart

/-- **Assumption 1 (Linearity and Boundedness).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §2.2.2, p.7: "For each
`(x, a, b) ∈ 𝒮 × 𝒜 × 𝒜` and `h ∈ [H]`, we have `r_h(x, a, b) = φ(x, a, b)ᵀθ_h` and
`ℙ_h(·|x, a, b) = φ(x, a, b)ᵀμ_h(·)`, where `φ : 𝒮 × 𝒜 × 𝒜 → ℝ^d` is a known feature map,
`θ_h ∈ ℝ^d` is an unknown vector and `μ_h = (μ_h^{(i)})_{i∈[d]}` is a vector of `d` unknown (signed)
measures on `𝒮`. We assume that `‖φ(·, ·, ·)‖ ≤ 1`, `‖θ_h‖ ≤ √d` and `‖μ_h(𝒮)‖ ≤ √d` for all
`h ∈ [H]`, where `‖·‖` is the vector `ℓ₂` norm."

`IsLinearMG G φ θ μ` says, for every step `h ∈ [1, H]`:
1. `r_h(x, a, b) = φ(x, a, b)ᵀθ_h` for all `(x, a, b)`;
2. `ℙ_h(B | x, a, b) = ∑_{i} φ_i(x, a, b) μ_h^{(i)}(B)` for every measurable `B ⊆ S` and all `(x, a, b)`;
3. `‖θ_h‖ ≤ √d`;
4. `‖(∫ v dμ_h^{(1)}, …, ∫ v dμ_h^{(d)})‖ ≤ √d` for every measurable `v : S → [−1, 1]`;

and moreover `φ` is measurable with `‖φ(x, a, b)‖ ≤ 1` for all `(x, a, b)`.

**Formalization Note**
- Condition 4 is the reading R1 of the printed `‖μ_h(𝒮)‖ ≤ √d`. Taking `v ≡ 1` gives the printed
  bound, and the total-variation bound `‖(|μ_h^{(i)}|(𝒮))_i‖ ≤ √d` implies condition 4. Read literally
  (a bound on the vector of net masses), the printed assumption does not give
  `‖∫ V dμ_h‖ ≤ H√d` for `|V| ≤ H`, which the proofs of Lemmas 3 and 7 use; under it Lemma 7 fails
  (`d = 3`, two states, `‖μ_h(𝒮)‖ ≈ 1.43`, but `‖w_1‖ ≥ 7 > 2H√d`).
- The vectors `θ_h` and measures `μ_h` are arguments of the predicate; the theorems quantify over
  them universally, which is the same as assuming that some `θ`, `μ` exist. The algorithm never
  reads them.
- Integrals against a signed measure are taken through its Jordan decomposition (`sIntegral`).
- The feature map is measurable on `S × A × A`; this excludes only maps for which the expectations
  of the paper are undefined. -/
def IsLinearMG {d : ℕ} (G : MarkovGame S A) (φ : S → A → A → Fin d → ℝ)
    (θ : ℕ → Fin d → ℝ) (μ : ℕ → Fin d → SignedMeasure S) : Prop :=
  Measurable (fun z : S × A × A => φ z.1 z.2.1 z.2.2) ∧
  (∀ x a b, ApproxVI.euclNorm (φ x a b) ≤ 1) ∧
  ∀ h ∈ Finset.Icc 1 G.H,
    (∀ x a b, G.r h x a b = φ x a b ⬝ᵥ θ h) ∧
    (∀ x a b (B : Set S), MeasurableSet B →
      (G.P h (x, a, b) B).toReal = ∑ i, φ x a b i * μ h i B) ∧
    ApproxVI.euclNorm (θ h) ≤ Real.sqrt d ∧
    (∀ v : S → ℝ, Measurable v → (∀ y, |v y| ≤ 1) →
      ApproxVI.euclNorm (fun i => sIntegral v (μ h i)) ≤ Real.sqrt d)

end LinearZeroSumMG


