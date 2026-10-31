-- Prove2me | Definitions.Def_DiffCtrlRobust_A123
-- name    : DiffCtrlRobust_A123
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:22.893458+00:00
-- url     : https://prove2.me/theorems/784e8b0a-ce90-4e43-b50b-7e526f58d6df
-- title:
--   Assumptions (A1)–(A3) with constants $C_R$, $C_0$
-- statement:
--   Let $b:\mathbb R^d\times\mathbb U\to\mathbb R^d$ and $\sigma:\mathbb R^d\to\mathbb R^{d\times d}$, let $\mathcal B_R$ be the open ball of radius $R$ at the origin, and let $a=\frac12\sigma\sigma^{\mathsf T}$. The pair $(b,\sigma)$ satisfies (A1)–(A3) with constants $C_R>0$ ($R>0$) and $C_0>0$ if:
--
--   1. (A1) $|b(x,\zeta)-b(y,\zeta)|^2+\|\sigma(x)-\sigma(y)\|^2\le C_R|x-y|^2$ for all $x,y\in\mathcal B_R$, $\zeta\in\mathbb U$, and $b$ is jointly continuous in $(x,\zeta)$;
--   2. (A2) $\sup_{\zeta\in\mathbb U}\langle b(x,\zeta),x\rangle^{+}+\|\sigma(x)\|^2\le C_0(1+|x|^2)$ for all $x\in\mathbb R^d$;
--   3. (A3) $\sum_{i,j=1}^d a^{ij}(x)z_iz_j\ge C_R^{-1}|z|^2$ for all $x\in\mathcal B_R$ and $z\in\mathbb R^d$.
--
--   These are local Lipschitz continuity, affine growth and local uniform ellipticity. Keeping the constants as parameters lets a theorem say that a family of models shares them.
--
--   **Formalization Note** The supremum in (A2) is written as a bound for every $\zeta$, which is equivalent for nonempty $\mathbb U$.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2, pp.5–6, (A1)–(A3); Notation, p.9, for the open ball

import Definitions.Def_DiffCtrlRobust_diffusionMatrix

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- Assumptions (A1)–(A3) on the drift `b` and the diffusion matrix `σ`, with explicit constants
`C R = C_R` and `C₀` (arXiv:2205.05894v2, §2, pp.5–6).

**Formalization Note.** `B_R` is the open ball (Notation, p.9). The same `C_R` serves (A1) and (A3),
as printed. The supremum over `ζ` of (A2) is written as a bound for every `ζ`, which is equivalent
since `U` is nonempty. Making the constants arguments lets the theorems of this mission say that
the approximating models share them. -/
structure A123 {d : ℕ} {U : Type*} [TopologicalSpace U] (C : ℝ → ℝ) (C₀ : ℝ)
    (b : SDEState d → U → SDEState d) (σ : SDEState d → SDEDiffusion d) : Prop where
  /-- `C_R > 0`. -/
  C_pos : ∀ R, 0 < R → 0 < C R
  /-- (A1): the local Lipschitz bound, uniform in the control. -/
  lipschitz : ∀ R, 0 < R → ∀ x ∈ Metric.ball (0 : SDEState d) R,
    ∀ y ∈ Metric.ball (0 : SDEState d) R, ∀ ζ : U,
      ‖b x ζ - b y ζ‖ ^ 2 + ‖σ x - σ y‖ ^ 2 ≤ C R * ‖x - y‖ ^ 2
  /-- (A1): `b` is jointly continuous. -/
  continuous_drift : Continuous (fun p : SDEState d × U => b p.1 p.2)
  /-- `C₀ > 0`. -/
  C₀_pos : 0 < C₀
  /-- (A2): the affine growth condition. -/
  growth : ∀ (x : SDEState d) (ζ : U),
    max (inner ℝ (b x ζ) x) 0 + ‖σ x‖ ^ 2 ≤ C₀ * (1 + ‖x‖ ^ 2)
  /-- (A3): nondegeneracy. -/
  nondegenerate : ∀ R, 0 < R → ∀ x ∈ Metric.ball (0 : SDEState d) R, ∀ z : SDEState d,
    (C R)⁻¹ * ‖z‖ ^ 2 ≤ ∑ i, ∑ j, diffusionMatrix σ x i j * z i * z j

end DiffCtrlRobust


