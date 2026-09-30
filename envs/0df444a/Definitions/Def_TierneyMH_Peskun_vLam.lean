-- Prove2me | Definitions.Def_TierneyMH_Peskun_vLam
-- name    : TierneyMH_Peskun_vLam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T12:22:55.175673+00:00
-- url     : https://prove2.me/theorems/681aed86-b2bd-4d50-a085-9160bc54a64d
-- title:
--   Regularized asymptotic variance $v_\lambda(f, H)$
-- statement:
--   Let $\pi$ be a probability measure and $H$ a transition kernel on $E$, $f : E \to \mathbb R$ and $\lambda \in \mathbb R$. Tierney defines, for $0 \le \lambda < 1$, $v_\lambda(f,H) = \langle f, (I - \lambda H)^{-1}(I + \lambda H) f\rangle$. Expanding $(I-\lambda H)^{-1} = \sum_{k \ge 0} \lambda^k H^k$ gives $(I-\lambda H)^{-1}(I+\lambda H) = I + 2\sum_{k\ge1}\lambda^k H^k$, and this definition takes that series form:
--
--   $$
--   v_\lambda(f, H) \;=\; \langle f, f\rangle \;+\; 2 \sum_{k=1}^{\infty} \lambda^{k} \,\langle f, H^{k} f\rangle ,
--   $$
--
--   with $\langle f, H^k f\rangle$ the lag-$k$ inner product in $L^2(\pi)$.
--
--   The family $v_\lambda$ interpolates to the asymptotic variance: as $\lambda \uparrow 1$ it converges to $v(f,H)$, which makes it the device by which Peskun's ordering of asymptotic variances is proved.
--
--   **Formalization Note** The series (Neumann-series) form replaces the operator form $\langle f,(I-\lambda H)^{-1}(I+\lambda H)f\rangle$; the two agree whenever $H$ is a contraction on $L^2_0(\pi)$ and $0 \le \lambda < 1$, which is the situation of the paper. Lean's `tsum` returns $0$ on a non-summable series; in that situation the series is absolutely summable because $|\langle f, H^k f\rangle| \le \langle f, f\rangle$. The parameter $\lambda$ is named `lam` in Lean.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 6, proof of Theorem 4 (definition of v_λ(f, H))

import Mathlib
import Definitions.Def_TierneyMH_Peskun_lagInner

open MeasureTheory ProbabilityTheory

namespace TierneyMH.Peskun

/-- The regularized asymptotic variance `v_λ(f, H) = ⟨f, (I − λH)⁻¹(I + λH) f⟩` of Tierney
(1998, p. 6), written through its Neumann series
`(I − λH)⁻¹(I + λH) = I + 2 ∑_{k ≥ 1} λᵏ Hᵏ` (valid on `L²₀(π)` for `0 ≤ λ < 1` when `H` is a
contraction there):
`v_λ(f, H) = ⟨f, f⟩ + 2 ∑_{k=1}^{∞} λᵏ ⟨f, Hᵏ f⟩`.
The parameter `λ` is named `lam` (`λ` is Lean syntax). Lean's `tsum` is `0` on a non-summable
series; for a reversible `H`, `f ∈ L²₀(π)` and `0 ≤ λ < 1` the series is absolutely summable
because `|⟨f, Hᵏ f⟩| ≤ ⟨f, f⟩`. -/
noncomputable def vLam {E : Type*} [MeasurableSpace E] (π : Measure E) (H : Kernel E E)
    (f : E → ℝ) (lam : ℝ) : ℝ :=
  ∫ x, f x ^ 2 ∂π + 2 * ∑' k : ℕ, lam ^ (k + 1) * lagInner π H f (k + 1)

end TierneyMH.Peskun


