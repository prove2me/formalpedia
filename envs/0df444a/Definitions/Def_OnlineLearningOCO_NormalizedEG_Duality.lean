-- Prove2me | Definitions.Def_OnlineLearningOCO_NormalizedEG_Duality
-- name    : OnlineLearningOCO_NormalizedEG_Duality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:14.86137+00:00
-- url     : https://prove2.me/theorems/0bce234c-f880-4db2-bba7-199369009f6b
-- title:
--   Online Mirror Descent, Fenchel conjugate, Bregman divergence, and the log-sum-exp conjugate (§2.6–§2.8, pp. 142–153)
-- statement:
--   This file fixes the objects of the duality analysis of Online Mirror Descent in §2.6–§2.8. Rounds are numbered from $0$ in Lean: Lean index $t$ is the paper's round $t+1$.
--
--   1. **Cumulative losses.** For a sequence $z_1, z_2, \dots$ in an additive group, $z_{1:t} = \sum_{s=1}^{t} z_s$ (p. 141), with $z_{1:0} = 0$.
--   2. **Fenchel conjugate.** For a set $S$ in a real inner product space $E$ and a function $R : E \to \mathbb R$, the conjugate of $R + I_S$ (the function equal to $R$ on $S$ and to $+\infty$ off $S$, §2.7.1, p. 147 and Table 2.1, p. 148) is
--   $$R^\star(\theta) = \sup_{w \in S} \big(\langle w, \theta\rangle - R(w)\big).$$
--   3. **Bregman divergence** (2.12), p. 148. For a differentiable $F : E \to \mathbb R$ with gradient $\nabla F$,
--   $$D_F(a \,\|\, b) = F(a) - \big(F(b) + \langle \nabla F(b), a - b\rangle\big).$$
--   4. **Online Mirror Descent** (box on p. 142). With a link function $g : E \to E$, OMD predicts $w_t = g(\theta_t)$, where $\theta_1 = 0$ and $\theta_{t+1} = \theta_t - z_t$; equivalently $w_t = g(-z_{1:t-1})$ (p. 149).
--   5. **The log-sum-exp conjugate.** For $\eta > 0$ and $\theta \in \mathbb R^d$, the conjugate of the normalized entropy $R(w) = \frac1\eta \sum_i w[i]\log w[i] + I_S(w)$ on the probability simplex $S$ (Table 2.1, p. 148; p. 153) is
--   $$R^\star(\theta) = \frac1\eta \log\Big(\sum_{i=1}^d e^{\eta\theta[i]}\Big),$$
--   whose gradient is the softmax map $\theta \mapsto \big(e^{\eta\theta[i]} / \sum_j e^{\eta\theta[j]}\big)_i$, the link function (2.10), p. 143, of normalized EG. The Bregman divergence $D_{R^\star}(a\,\|\,b)$ of this $R^\star$ is formed with the softmax as its gradient and the standard inner product of $\mathbb R^d$.
--
--   These objects are shared by Lemma 2.20 (the general OMD bound) and by the steps (2.16)–(2.18) of the proof of Theorem 2.22.
--
--   **Formalization Note** The conjugate is a real supremum (`⨆`) over the subtype $S$; it equals the paper's value whenever $S$ is nonempty and the supremum is bounded above, which is the case whenever a link function attaining it exists (the hypotheses of Lemma 2.20). The Bregman divergence takes the gradient as an explicit argument rather than computing it, so it is only meaningful when that argument is the gradient; the theorems that use it state that it is. The Bregman divergence on $\mathbb R^d$ is written with explicit coordinate sums because `Fin d → ℝ` carries the sup norm in Mathlib, not an inner product.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 141 (notation z_{1:t}), p. 142 (OMD box), p. 143 (2.10), p. 147 (Fenchel conjugate), p. 148 (Table 2.1, (2.12)), p. 149 (2.13), p. 153 (R⋆ of the normalized entropy)

import Mathlib
open scoped RealInnerProductSpace

namespace OnlineLearningOCO.NormalizedEG

/-! Shalev-Shwartz, *Online Learning and Online Convex Optimization*, Found. Trends Mach. Learn.
4(2) (2011) 107–194, §2.6–§2.8, pp. 141–154: Online Mirror Descent, the Fenchel conjugate,
Bregman divergences, and the log-sum-exp conjugate of the normalized entropy. Rounds are numbered
from `0`: index `t` in Lean is the paper's round `t + 1`. -/

/-- The cumulative sum `z_{1:t} = z_1 + ⋯ + z_t` of the first `t` loss vectors (notation of p. 141),
with 0-based rounds: `cumSum z t = ∑_{s<t} z s`, so `cumSum z 0 = 0`. -/
def cumSum {E : Type*} [AddCommMonoid E] (z : ℕ → E) (t : ℕ) : E :=
  ∑ s ∈ Finset.range t, z s

/-- The Fenchel conjugate (§2.7.1, p. 147) of the function equal to `R` on `S` and to `+∞` off `S`
(that is, of `R + I_S`, Table 2.1, p. 148): `R⋆(θ) = sup_{w ∈ S} (⟨w, θ⟩ − R(w))`.
This is a real supremum; it is the paper's value whenever `S` is nonempty and the supremum is
bounded above (both hold whenever a link function attaining it exists). -/
noncomputable def fenchelConj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (R : E → ℝ) (θ : E) : ℝ :=
  ⨆ w : S, (⟪(w : E), θ⟫ - R w)

/-- The Bregman divergence (2.12), p. 148, of a differentiable function `F` whose gradient is
`gradF`: `D_F(a ‖ b) = F(a) − (F(b) + ⟨∇F(b), a − b⟩)`. -/
def bregman {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (gradF : E → E) (a b : E) : ℝ :=
  F a - (F b + ⟪gradF b, a - b⟫)

/-- The prediction of Online Mirror Descent (box on p. 142) with link function `g`:
`w_t = g(θ_t)` with `θ_1 = 0`, `θ_{t+1} = θ_t − z_t`, i.e. `w_t = g(−z_{1:t−1})` (p. 149).
With 0-based rounds, `omdIterate g z t = g (−∑_{s<t} z s)`; `omdIterate g z 0 = g 0` is the
paper's `w_1`. -/
def omdIterate {E : Type*} [AddCommGroup E] (g : E → E) (z : ℕ → E) (t : ℕ) : E :=
  g (-(cumSum z t))

/-- The Fenchel conjugate of the normalized entropy `R(w) = (1/η) ∑_i w[i] log w[i] + I_S(w)`
on the probability simplex `S` of `ℝ^d` (Table 2.1, p. 148, and p. 153):
`R⋆(θ) = (1/η) log (∑_i e^{η θ[i]})`. -/
noncomputable def logSumExpConj {d : ℕ} (η : ℝ) (θ : Fin d → ℝ) : ℝ :=
  (1 / η) * Real.log (∑ i, Real.exp (η * θ i))

/-- The softmax map `θ ↦ (e^{η θ[i]} / ∑_j e^{η θ[j]})_i`, the gradient of `logSumExpConj η`
(the link function (2.10), p. 143, of normalized EG). -/
noncomputable def softmaxEG {d : ℕ} (η : ℝ) (θ : Fin d → ℝ) : Fin d → ℝ :=
  fun i ↦ Real.exp (η * θ i) / ∑ j, Real.exp (η * θ j)

/-- The Bregman divergence (2.12), p. 148, of the log-sum-exp conjugate `R⋆ = logSumExpConj η`,
with its gradient `softmaxEG η` and the standard inner product of `ℝ^d`:
`D_{R⋆}(a ‖ b) = R⋆(a) − (R⋆(b) + ∑_i ∇R⋆(b)[i] (a[i] − b[i]))`. -/
noncomputable def bregmanLSE {d : ℕ} (η : ℝ) (a b : Fin d → ℝ) : ℝ :=
  logSumExpConj η a - (logSumExpConj η b + ∑ i, softmaxEG η b i * (a i - b i))

end OnlineLearningOCO.NormalizedEG


