-- Prove2me | Definitions.Def_PADMPriv_renyiDiv
-- name    : PADMPriv_renyiDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:13.874028+00:00
-- url     : https://prove2.me/theorems/e18ca8d8-0530-4c6f-b60d-dd7c8ef09855
-- title:
--   Rényi divergence $D_\alpha(P\|Q)$ (Definition 2)
-- statement:
--   Let $P$, $Q$ be measures with densities $p$, $q$ with respect to a common reference measure $\nu$. For $\alpha>1$ the **Rényi divergence** is
--   $$
--   D_\alpha(P\|Q) = \frac{1}{\alpha-1}\ln\int \Big(\frac{p(z)}{q(z)}\Big)^{\alpha} q(z)\,d\nu(z).
--   $$
--   For random variables, $D_\alpha(X\|Y)$ is the divergence between their laws. It is the privacy loss measure of Rényi differential privacy.
--
--   **Formalization Note** Computed with $\nu=Q$: if $P\ll Q$ then $D_\alpha(P\|Q) = (\alpha-1)^{-1}\ln\int (dP/dQ)^\alpha\,dQ$, and $D_\alpha(P\|Q)=+\infty$ otherwise. The value is an extended real. For $\alpha>1$ this agrees with Definition 2 for every common reference measure.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Definition 2, p.4

import Mathlib

namespace PADMPriv

open MeasureTheory

open Classical in
/-- The Rényi divergence of order `α > 1`, Definition 2 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.4:
`D_α(P‖Q) = (α − 1)⁻¹ ln ∫ (p(z)/q(z))^α q(z) dν(z)` for densities `p, q` of `P, Q` with respect
to a common reference measure `ν`.

**Formalization Note** Computed with `ν = Q`: when `P ≪ Q` it is
`(α − 1)⁻¹ · ln ∫ (dP/dQ)^α dQ` (Radon–Nikodym derivative, `ℝ≥0∞` integral, `EReal` logarithm),
and it is `+∞` when `P` is not absolutely continuous with respect to `Q`. For `α > 1` this equals
Definition 2 for every common reference measure (with `ν = P + Q`, the integrand `p^α q^{1−α}` is
`+∞` on a set of positive `ν`-measure when `P` is not `≪ Q`). -/
noncomputable def renyiDiv {X : Type*} [MeasurableSpace X] (α : ℝ) (P Q : Measure X) : EReal :=
  if P ≪ Q then (((α - 1)⁻¹ : ℝ) : EReal) * ENNReal.log (∫⁻ z, (P.rnDeriv Q z) ^ α ∂Q) else ⊤

end PADMPriv


