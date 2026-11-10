-- Prove2me | Definitions.Def_OnlineDiscUniv_MomentClass
-- name    : OnlineDiscUniv_MomentClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:07.919431+00:00
-- url     : https://prove2.me/theorems/3632eb37-e8f3-469b-9229-5b425ce324c0
-- title:
--   Moment class $\mathcal M_q(K)$ and the tail modulus $t_\mu(H)$
-- statement:
--   For $q\ge4$ and $K<\infty$, $\mathcal M_q(K)$ is the class of probability laws $\mu$ on $\mathbb R$ with
--   $$
--   \mathbb E_\mu\xi=0,\qquad\mathbb E_\mu\xi^2=1,\qquad\mathbb E_\mu|\xi|^q\le K .
--   $$
--   The **fourth-moment tail modulus** is $t_\mu(H):=\mathbb E_\mu\big[|\xi|^4\mathbf 1_{\{|\xi|>H\}}\big]\in[0,\infty]$.
--
--   The class $\mathcal M_4(K)$ is the set of entry laws for which one algorithm works uniformly in Theorem 1.1(i) and Theorem 1.3, and $t_\mu(N^{1/3})$ is the tail term of the rate (1.1).
--
--   **Formalization Note** The absolute moment and the tail modulus are lower integrals in $[0,\infty]$. Integrability of $x$ and $x^2$ is stated so that the two moment conditions are about true moments; for $q\ge4$ it follows from $\mathbb E_\mu|\xi|^q\le K$.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), (2.2), p.5 (PDF p.6); tail modulus, p.2 (PDF p.3)

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace OnlineDiscUniv

/-- The moment class `M_q(K)` (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, (2.2),
printed p.5, PDF p.6): probability laws `μ` on `ℝ` with `E_μ ξ = 0`, `E_μ ξ² = 1` and
`E_μ |ξ|^q ≤ K`.

**Formalization Note** The `q`-th absolute moment is a lower integral in `ℝ≥0∞`, compared with
`ofReal K`. Integrability of `x` and `x²` is stated explicitly so that the Bochner integrals
`∫ x dμ` and `∫ x² dμ` are the true moments; for the paper's `q ≥ 4` it follows from
`E_μ|ξ|^q ≤ K < ∞`. -/
def MomentClass (q K : ℝ) : Set (Measure ℝ) :=
  {μ | IsProbabilityMeasure μ ∧ Integrable (fun x : ℝ => x) μ ∧
    Integrable (fun x : ℝ => x ^ 2) μ ∧ ∫ x, x ∂μ = 0 ∧ ∫ x, x ^ 2 ∂μ = 1 ∧
    ∫⁻ x, ‖x‖ₑ ^ q ∂μ ≤ ENNReal.ofReal K}

/-- The fourth-moment tail modulus `t_μ(H) := E_μ[|ξ|⁴ 1{|ξ| > H}]` (Jo–Lee, arXiv:2610.00103,
printed p.2, PDF p.3), as a lower integral in `ℝ≥0∞`. -/
noncomputable def tailMod (μ : Measure ℝ) (H : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x : ℝ | H < |x|}, ‖x‖ₑ ^ (4 : ℝ) ∂μ

end OnlineDiscUniv


