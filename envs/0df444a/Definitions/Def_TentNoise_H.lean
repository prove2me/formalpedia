-- Prove2me | Definitions.Def_TentNoise_H
-- name    : TentNoise_H
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:29.454126+00:00
-- url     : https://prove2.me/theorems/a62eab86-1277-4b6e-b899-d85b84b58291
-- title:
--   The reflected Gaussian noising kernel $H_\sigma(x,\cdot)=\mathrm{Law}(\mathfrak r(x+\sigma Z))$
-- statement:
--   For $\sigma\ge0$ the **reflected Gaussian noising kernel** is
--
--   $$
--   H_\sigma(x,\cdot):=\mathrm{Law}\bigl(\mathfrak r(x+\sigma Z)\bigr),\qquad Z\sim\mathcal N(0,1),
--   $$
--
--   the reflected heat kernel on $[0,1]$ at variance $\sigma^2$, with $H_0(x,\cdot)=\delta_x$. For an observable $v$ one writes $(H_\sigma v)(x)=\int v(y)\,H_\sigma(x,dy)$.
--
--   $H_\sigma$ is the heat semigroup on $[0,1]$ with reflecting (Neumann) boundary: it is symmetric with respect to $\mu$ and preserves $\mu$. It is the noise added at each step of the noised rollouts.
--
--   **Formalization Note** $\sigma$ is a standard deviation: $H_\sigma(x,\cdot)$ is the push-forward by $\mathfrak r$ of Mathlib's `gaussianReal x (σ^2)`. At $\sigma=0$ Mathlib's Gaussian is the Dirac mass, so $H_0(x,\cdot)=\delta_{\mathfrak r(x)}=\delta_x$ for $x\in[0,1]$, as the paper requires. The kernel is defined on all of $\mathbb R$; only $x\in[0,1]$ is used.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Definition 2.8, p.5 (PDF p.5), eq. (7)

import Mathlib
import Definitions.Def_TentNoise_refl

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TentNoise

/-- The reflected Gaussian noising kernel `H_σ(x, ·) := Law(𝔯(x + σZ))`, `Z ∼ N(0, 1)`
(Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Definition 2.8, p.5, eq. (7)): the reflected heat kernel at variance `σ²`.

**Formalization Note** `σ` is a standard deviation: `H σ x` is the push-forward by `𝔯` of the
Gaussian `N(x, σ²)` (Mathlib's `gaussianReal x (σ²)`, with the variance written `(σ ^ 2).toNNReal = σ²`). At `σ = 0` Mathlib's Gaussian is the Dirac
mass, so `H 0 x = δ_{𝔯 x} = δ_x` for `x ∈ [0, 1]`, as the paper requires (`H₀(x, ·) = δ_x`).
The kernel is defined on all of `ℝ`; only `x ∈ [0, 1]` is used. -/
noncomputable def H (σ : ℝ) : Kernel ℝ ℝ where
  toFun x := (gaussianReal x (σ ^ 2).toNNReal).map refl
  measurable' := by
    have hG : Measurable (fun p : ℝ × ℝ => refl (p.1 + p.2)) :=
      measurable_refl.comp (measurable_fst.add measurable_snd)
    have hm : Measurable (fun x : ℝ =>
        ((gaussianReal 0 (σ ^ 2).toNNReal).map (Prod.mk x)).map
          (fun p : ℝ × ℝ => refl (p.1 + p.2))) :=
      (Measure.measurable_map _ hG).comp Measurable.map_prodMk_left
    convert hm using 2 with x
    rw [Measure.map_map hG measurable_prodMk_left]
    have : (fun p : ℝ × ℝ => refl (p.1 + p.2)) ∘ Prod.mk x = refl ∘ (fun z => x + z) := rfl
    rw [this, ← Measure.map_map measurable_refl (measurable_const_add x),
      gaussianReal_map_const_add, zero_add]

end TentNoise


