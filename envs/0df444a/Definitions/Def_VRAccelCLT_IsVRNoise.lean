-- Prove2me | Definitions.Def_VRAccelCLT_IsVRNoise
-- name    : VRAccelCLT_IsVRNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:07.965906+00:00
-- url     : https://prove2.me/theorems/a15082dc-6739-4c17-a92b-0c7e0b2b6be2
-- title:
--   Gradient noise satisfying (5): $\mathbb E[w_k\mid\mathcal F_k]=0$, $\mathbb E[\|w_k\|^2\mid\mathcal F_k]\le\nu^2/N_k$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_k)_{k\ge0}$ and let $(N_k)_{k\ge0}$ be batch sizes. A sequence of random vectors $w_k=w_{k,N_k}$ in $\mathbb R^m$ is **gradient noise with the moment bounds (5)**, with constant $\nu>0$, if for every $k\ge 0$:
--
--   1. $w_k$ is $\mathcal F_{k+1}$-measurable and square integrable;
--   2. almost surely,
--   $$
--   \mathbb E[w_{k}\mid\mathcal F_k]=0,\qquad \mathbb E\big[\|w_{k}\|^2\mid\mathcal F_k\big]\le \frac{\nu^2}{N_k}. \tag{5}
--   $$
--
--   In the paper the noise is the sampled average $w_{k,N_k}=\frac1{N_k}\sum_{j=1}^{N_k}\nabla F(x_k,\xi_{j,k})-\nabla f(x_k)$ of (3), with $\mathcal F_k=\sigma\{x_0,\xi_{j,t},1\le j\le N_t,0\le t\le k-1\}$, and (5) is derived from (3) and Assumption 1 (iii). Every result of the paper uses the noise only through (5) and the measurability of $w_k$, so the definition keeps exactly these properties; the sampled noise is one instance.
--
--   **Formalization Note** Square integrability makes the conditional expectations in (5) meaningful in Lean (a conditional expectation of a non-integrable function is $0$ in Mathlib); in the paper it follows from (5).
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, eq. (3) and (5), p.6; Assumption 1 (iii), p.6

import Mathlib

open MeasureTheory

namespace VRAccelCLT

/-- **Gradient noise with the moment bounds (5).** Lei, Shanbhag, arXiv:2006.07769v3, p.6:
"for any k ≥ 0, E[wk,Nk | Fk] = 0, and E[∥wk,Nk∥2 | Fk] ≤ ν2/Nk. (5) hold almost surely",
where `F_k ≜ σ{x₀, ξ_{j,t}, 1 ≤ j ≤ N_t, 0 ≤ t ≤ k − 1}` and `ν > 0` is the constant of
Assumption 1 (iii).

`IsVRNoise μ ℱ w ν N` says: `ν > 0`, and for every `k ≥ 0` the noise `w k` is
`ℱ (k+1)`-measurable, square integrable, has conditional mean `0` given `ℱ k`, and conditional
second moment at most `ν² / N k` given `ℱ k`, almost surely.

**Formalization Note.** The paper's noise is the sampled average (3),
`w_{k,N_k} = (Σ_{j=1}^{N_k} ∇F(x_k, ξ_{j,k}))/N_k − ∇f(x_k)`, and (5) is derived from (3) and
Assumption 1 (iii) (p.6). This definition keeps exactly the properties every proof of the paper
uses: (5) and the measurability `w_k ∈ ℱ_{k+1}` (`w_k` is built from `x_k` and the samples of
round `k`); the sampled noise is one instance. Square integrability is how the conditional
expectations of (5) are meaningful in Lean (a conditional expectation of a non-integrable function
is `0` in Mathlib); it follows from (5) in the paper. -/
def IsVRNoise {m : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (w : ℕ → Ω → EuclideanSpace ℝ (Fin m)) (ν : ℝ) (N : ℕ → ℕ) : Prop :=
  0 < ν ∧
    ∀ k : ℕ, StronglyMeasurable[ℱ (k + 1)] (w k) ∧ MemLp (w k) 2 μ ∧
      μ[w k | ℱ k] =ᵐ[μ] 0 ∧
      μ[fun ω => ‖w k ω‖ ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => ν ^ 2 / (N k : ℝ)

end VRAccelCLT


