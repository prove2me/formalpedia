-- Prove2me | Definitions.Def_NatureSLT_Consistency_uniformConvergence
-- name    : NatureSLT_Consistency_uniformConvergence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:50.347128+00:00
-- url     : https://prove2.me/theorems/92191357-b34e-4f37-a525-9a1bca943cf9
-- title:
--   Uniform one-sided (2.4) and two-sided (2.6) convergence of empirical risks
-- statement:
--   Let $F$ be a probability measure on $Z$ and $Q(z,\alpha)$, $\alpha\in\Lambda$, a set of real functions with risk $R(\alpha)=\int Q(z,\alpha)\,dF(z)$ and empirical risk $R_{\mathrm{emp}}(\alpha)=\frac1\ell\sum_{i=1}^\ell Q(z_i,\alpha)$ on an i.i.d. sample of size $\ell$ from $F$.
--
--   1. **Uniform one-sided convergence** holds if
--   $$\lim_{\ell\to\infty} P\Bigl\{\sup_{\alpha\in\Lambda}\bigl(R(\alpha)-R_{\mathrm{emp}}(\alpha)\bigr) > \varepsilon\Bigr\} = 0 \qquad \forall \varepsilon>0. \tag{2.4}$$
--   2. **Uniform two-sided convergence** holds if the random variables $\xi^\ell=\sup_{\alpha\in\Lambda}\bigl|\int Q(z,\alpha)\,dF(z)-\frac1\ell\sum_{i=1}^\ell Q(z_i,\alpha)\bigr|$ of (2.5) converge to $0$ in probability:
--   $$\lim_{\ell\to\infty} P\Bigl\{\sup_{\alpha\in\Lambda}\Bigl|\int Q(z,\alpha)\,dF(z)-\frac1\ell\sum_{i=1}^\ell Q(z_i,\alpha)\Bigr| > \varepsilon\Bigr\} = 0 \qquad \forall \varepsilon>0. \tag{2.6}$$
--
--   The probability is the product measure $F^\ell$. The key theorem identifies (2.4) with consistency of ERM; (2.6) is the law of large numbers in a functional space.
--
--   **Formalization Note** Both suprema are taken in the extended reals, so they are genuine (possibly $+\infty$); for an empty $\Lambda$ they equal $-\infty$. The one-sided form has no absolute value.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 38 and 40, Eqs. (2.4), (2.5), (2.6)

import Mathlib
import Definitions.Def_NatureSLT_Consistency_risk

open MeasureTheory Filter Topology

namespace NatureSLT.Consistency

/-- `sup_{α ∈ Λ} (R(α) − R_emp(α))` on the sample `z`, in `EReal` (so it is the genuine supremum,
possibly `+∞`; it is `⊥` only for empty `Λ`). -/
noncomputable def supOneSidedDeviation {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    (Q : Λ → Z → ℝ) {ℓ : ℕ} (z : Fin ℓ → Z) : EReal :=
  ⨆ α : Λ, ((risk F Q α - empiricalRisk Q z α : ℝ) : EReal)

/-- `ξ^ℓ = sup_{α ∈ Λ} |∫ Q(z, α) dF(z) − (1/ℓ) ∑_{i=1}^ℓ Q(zᵢ, α)|` (Vapnik 2000, Eq. (2.5),
p. 40) on the sample `z`, in `EReal` (genuine supremum, possibly `+∞`). -/
noncomputable def supTwoSidedDeviation {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    (Q : Λ → Z → ℝ) {ℓ : ℕ} (z : Fin ℓ → Z) : EReal :=
  ⨆ α : Λ, ((|risk F Q α - empiricalRisk Q z α| : ℝ) : EReal)

/-- **Uniform one-sided convergence** (Vapnik 2000, Eq. (2.4), p. 38):
`lim_{ℓ→∞} P{sup_{α ∈ Λ} (R(α) − R_emp(α)) > ε} = 0` for every `ε > 0`, the probability being the
product measure `F^ℓ` of an i.i.d. sample of size `ℓ`. -/
def UniformOneSidedConvergence {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    (Q : Λ → Z → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun ℓ : ℕ => Measure.pi (fun _ : Fin ℓ => F)
      {z : Fin ℓ → Z | ((ε : ℝ) : EReal) < supOneSidedDeviation F Q z}) atTop (𝓝 0)

/-- **Uniform two-sided convergence** (Vapnik 2000, Eq. (2.6), p. 40):
`lim_{ℓ→∞} P{sup_{α ∈ Λ} |∫ Q(z, α) dF(z) − (1/ℓ) ∑ Q(zᵢ, α)| > ε} = 0` for every `ε > 0`. -/
def UniformTwoSidedConvergence {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    (Q : Λ → Z → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun ℓ : ℕ => Measure.pi (fun _ : Fin ℓ => F)
      {z : Fin ℓ → Z | ((ε : ℝ) : EReal) < supTwoSidedDeviation F Q z}) atTop (𝓝 0)

end NatureSLT.Consistency


