-- Prove2me | Definitions.Def_SellingData_AppendsRotation_RotationFamily
-- name    : SellingData_AppendsRotation_RotationFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:34:20.67608+00:00
-- url     : https://prove2.me/theorems/e9f1d596-c3cd-4914-b4c1-23cef1d8a0f9
-- title:
--   §4, pp. 15–16 — posterior-mean distributions H(v, α) on [v̲, v̄] with density h > 0, rotation order (9) around v⁺, common mean û
-- statement:
--   This definition fixes the **generalized information structure** of §4.
--
--   A marketer's targeting value $u$ has prior mean $\hat u$. A data-based service of informativeness $\alpha\in(0,1)$ produces a signal, and all relevant information in it is summarised by the posterior mean $v=E[u\mid w]$. For each $\alpha$ the posterior mean has cumulative distribution function $H(\cdot,\alpha)$ on a support $[\underline v,\bar v]$ with a strictly positive density $h(\cdot,\alpha)$:
--   $$
--   H(\underline v,\alpha)=0,\qquad H(\bar v,\alpha)=1,\qquad \frac{\partial H(v,\alpha)}{\partial v}=h(v,\alpha)>0\quad (\underline v<v<\bar v).
--   $$
--   $H(\cdot,\alpha)$ and $h(\cdot,\alpha)$ are continuous on $[\underline v,\bar v]$, and the partial derivative $\partial H(v,\alpha)/\partial\alpha$ exists for every $v\in[\underline v,\bar v]$ and $\alpha\in(0,1)$.
--
--   The family satisfies two model assumptions of the paper:
--
--   1. **Rotation order (9).** There is a rotation point $v^+\in(\underline v,\bar v)$ such that, for every $\alpha\in(0,1)$,
--   $$
--   \frac{\partial H(v,\alpha)}{\partial\alpha}>0 \text{ if } v<v^+,\qquad \frac{\partial H(v,\alpha)}{\partial\alpha}<0 \text{ if } v>v^+ .
--   $$
--   2. **Common mean.** Under Bayesian updating every $H(\cdot,\alpha)$ has mean $\hat u$:
--   $$
--   \int_{\underline v}^{\bar v} v\,h(v,\alpha)\,dv=\hat u\qquad(0<\alpha<1).
--   $$
--
--   A higher $\alpha$ is then a mean-preserving spread of the posterior mean. The structure includes the paper's "truth or noise" example with a prior on a bounded interval.
--
--   **Formalization Note.** The page allows a potentially unbounded support; here $\underline v<\bar v$ are real numbers (bounded support), because the paper's arguments integrate and differentiate over the support without any domination condition. The rotation condition is imposed on the open support, since $H$ is constant in $\alpha$ outside it. Condition (10) of the paper is a consequence of (9) and the common mean, and is not assumed.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), pp. 15–16, §4, (9), (10)

import Mathlib

namespace SellingData.AppendsRotation

open Set

/-- The generalized information structure of Guo, *Selling Data to Marketers*, §4, pp. 15–16:
a family, indexed by the informativeness `α ∈ (0, 1)`, of distributions of the posterior mean `v`
on a fixed bounded support `[vLo, vHi]`, with cumulative distribution function `H v α`, density
`h v α`, partial derivative `Hα v α = ∂H(v, α)/∂α`, rotation point `vPlus` (the rotation
order (9)) and common mean `uHat` (Bayesian updating preserves the prior mean `û`).

Bounded support, continuity of `H` and `h` in `v` on the closed support, and the existence of
`∂H/∂α` on the closed support are the regularity the paper states as "continuous and
differentiable"; the support is pinned to be bounded (the page allows a potentially unbounded
support). -/
structure RotationFamily where
  /-- lower end `v̲` of the support of the posterior mean -/
  vLo : ℝ
  /-- upper end `v̄` of the support of the posterior mean -/
  vHi : ℝ
  /-- rotation point `v⁺` -/
  vPlus : ℝ
  /-- prior mean `û`, the common mean of every `H(·, α)` -/
  uHat : ℝ
  /-- cumulative distribution function `H(v, α)` of the posterior mean -/
  H : ℝ → ℝ → ℝ
  /-- density `h(v, α)` of the posterior mean -/
  h : ℝ → ℝ → ℝ
  /-- partial derivative `∂H(v, α)/∂α` -/
  Hα : ℝ → ℝ → ℝ
  vLo_lt_vHi : vLo < vHi
  H_vLo : ∀ α ∈ Ioo (0 : ℝ) 1, H vLo α = 0
  H_vHi : ∀ α ∈ Ioo (0 : ℝ) 1, H vHi α = 1
  H_continuousOn : ∀ α ∈ Ioo (0 : ℝ) 1, ContinuousOn (fun v => H v α) (Icc vLo vHi)
  H_hasDerivAt_v : ∀ α ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo vLo vHi,
    HasDerivAt (fun x => H x α) (h v α) v
  h_pos : ∀ α ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo vLo vHi, 0 < h v α
  h_continuousOn : ∀ α ∈ Ioo (0 : ℝ) 1, ContinuousOn (fun v => h v α) (Icc vLo vHi)
  H_hasDerivAt_α : ∀ v ∈ Icc vLo vHi, ∀ α ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun a => H v a) (Hα v α) α
  /-- the rotation point lies inside the support, `v⁺ ∈ (v̲, v̄)` -/
  vPlus_mem : vPlus ∈ Ioo vLo vHi
  /-- the rotation order (9), read on the support -/
  rotation : ∀ α ∈ Ioo (0 : ℝ) 1,
    (∀ v ∈ Ioo vLo vPlus, 0 < Hα v α) ∧ (∀ v ∈ Ioo vPlus vHi, Hα v α < 0)
  /-- the mean of `H(·, α)` is `û` for every `α` -/
  mean_eq : ∀ α ∈ Ioo (0 : ℝ) 1, ∫ v in vLo..vHi, v * h v α = uHat

end SellingData.AppendsRotation


