-- Prove2me | Definitions.Def_QuantumZipper_Welding_Wedge
-- name    : QuantumZipper_Welding_Wedge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:16:35.246517+00:00
-- url     : https://prove2.me/theorems/cf329335-d313-4080-895a-ac94036e5bf9
-- title:
--   $\alpha$-quantum wedge field (1.10): lateral kernel $G^\dagger$ and the two-sided drift process $A$
-- statement:
--   This file defines the field of an $\alpha$-quantum wedge in the representation (1.10), with $Q=2/\gamma+\gamma/2$.
--
--   1. **Lateral kernel.** The lateral part $h^\dagger$ of the free boundary GFF has mean zero on every semicircle centred at $0$ and covariance kernel
--   $$G^\dagger(u,v)=G(u,v)+2\log\max(|u|,|v|).$$
--   This is the GFF kernel with the radial projection removed from both arguments.
--   2. **The process $A$.** Let $w_1,w_2$ be independent standard Brownian motions and $B=\sqrt2\,w$ ("diffusive rate 2"). For $t\ge0$, $A_t=\sqrt2\,w_1(t)+(\alpha-Q)t$. With $\tilde B_s=\sqrt2\,w_2(s)-(\alpha-Q)s$ and $s_0=\sup\{s:\tilde B_s=0\}$, $A_{-t}=\tilde B_{t+s_0}$ for $t\ge0$. This is the Brownian motion with drift $-(\alpha-Q)$ conditioned not to revisit $0$, translated so that $\inf\{t:A_t=0\}=0$.
--   3. **Wedge field.** $h=h^\dagger+Q(-\log|\cdot|)+A_{-\log|\cdot|}$ with $h^\dagger$ independent of $A$. Equivalently, the pairings $(h,\mu)$ are, given $\sigma(w_1,w_2)$, Gaussian with mean $\int\big(Q(-\log|u|)+A_{-\log|u|}\big)\mu(du)$ and covariance $\iint G^\dagger\,d\mu\,d\nu$, with regular arc averages.
--
--   An $\alpha$-quantum wedge is the doubly marked quantum surface $(\mathbb H,h)$; its canonical description is obtained by the rescaling (1.8) with $\mu_h(B_1(0))=1$. Equality in law of wedges is equality in law of canonical descriptions.
--
--   **Formalization Note** The paper prints "for $\alpha<0$". The construction needs $\alpha<Q$ (so that $s_0<\infty$ almost surely), and the paper uses it with $\alpha=\gamma$ and $\alpha=\gamma-2/\gamma$; it is read as $\alpha<Q$. The kernel $G^\dagger$ is derived, not printed: the upper-semicircle average of $G(\cdot,v)$ around $0$ is $-2\log\max(r,|v|)$. $G^\dagger$ is scale invariant, which the sanity file checks.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §1.6, pp. 21–23, Definitions 1–3, (1.9), (1.10)

import Mathlib
import Definitions.Def_QuantumZipper_Welding_Setting
import Definitions.Def_QuantumZipper_Welding_QuantumLength

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper.Welding

/-! # Quantum wedges (arXiv:1012.4797v2, §1.6, pp. 21–23, (1.10)) -/

/-- The covariance kernel of the **lateral part** `h†` of the free boundary GFF on `ℍ`,
`G†(u, v) = G(u, v) + 2 log max(|u|, |v|)`.

`h† = h − h_{|·|}(0)` has mean zero on every semicircle centred at `0` (p. 21). For the free
boundary GFF, `∫ G(u, v) σ_{0,r}(du) = −2 log max(r, |v|)` (the average of `−log |u − v| − log |u − v̄|`
over the upper semicircle `|u| = r` is the average of `−log |u − v|` over the full circle), and
subtracting the radial projection from both arguments gives `G†`.

**Formalization Note** Derived, not printed in the paper; checked by hand: `G†` is invariant under
`(u, v) ↦ (au, av)`, as the scale invariance of `h†` (p. 22) requires, and the semicircle average of
`G†(·, v)` around `0` vanishes. -/
noncomputable def lateralGreen (u v : ℂ) : ℝ :=
  QuantumZipper.ReverseCoupling.greenFree u v + 2 * Real.log (max ‖u‖ ‖v‖)

/-- The two-sided process `A_t` of the `α`-quantum wedge (arXiv:1012.4797v2, (1.10), p. 22), built
from two independent standard Brownian paths `w₁`, `w₂` (with `B = √2 w` the Brownian motion "with
diffusive rate 2", p. 22):
* for `t ≥ 0`, `A_t = √2 w₁(t) + (α − Q) t`;
* for `t ≥ 0`, `A_{−t} = B̃_{t + s₀}`, where `B̃_s = √2 w₂(s) − (α − Q) s` and
  `s₀ = sup {s : B̃_s = 0}`.

**Formalization Note** The paper prints "for `α < 0`"; the construction needs `α < Q` (so that
`B̃` has positive drift and `s₀ < ∞` a.s.), and the paper uses it with `α = γ > 0` and
`α = γ − 2/γ`; this is read as `α < Q` (a printed slip, disclosed). If the zero set of `B̃` is
unbounded (a null event when `α < Q`), `sSup` is the junk `0`. The translation is the paper's
`inf {t : A_t = 0} = 0` (p. 23). -/
noncomputable def wedgeA (α Q : ℝ) (w₁ w₂ : ℝ≥0 → ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.sqrt 2 * w₁ (Real.toNNReal t) + (α - Q) * t
  else
    let Bt : ℝ≥0 → ℝ := fun s => Real.sqrt 2 * w₂ s - (α - Q) * s
    let s₀ : ℝ≥0 := sSup {s : ℝ≥0 | Bt s = 0}
    Bt (Real.toNNReal (-t) + s₀)

/-- The radial (non-lateral) part of the `α`-quantum wedge field (1.10):
`m_A(u) = Q(−log |u|) + A_{−log |u|}`. -/
noncomputable def wedgeMean (α Q : ℝ) (w₁ w₂ : ℝ≥0 → ℝ) (u : ℂ) : ℝ :=
  Q * (-Real.log ‖u‖) + wedgeA α Q w₁ w₂ (-Real.log ‖u‖)

/-- **`α`-quantum wedge field** (arXiv:1012.4797v2, §1.6, Definition 3, (1.10), p. 22), with
`Q = 2/γ + γ/2`. On `(Ω, P)`: `W₁`, `W₂` are independent standard Brownian motions (giving `A`), and
the field `h = h†(·) + Q(−log |·|) + A_{−log |·|}`, with `h†` independent of `A`, is given through
its pairings `Ψ ω μ = (h, μ)`: conditionally on `σ(W₁, W₂)`, the pairings are Gaussian with mean
`∫ m_A dμ` and covariance `∫∫ G† dμ dν`. The arc averages are regular.

**Formalization Note** This is the field in the representation (1.10), translated so that
`inf {t : A_t = 0} = 0` (p. 23), not yet in its canonical description; the canonical description is
obtained with `canonicalMeasure` / `canonicalArcAvg` (p. 21). Equality in law of quantum surfaces is
equality in law of canonical descriptions. -/
structure IsWedgeField {Ω : Type*} [MeasurableSpace Ω] (α γ : ℝ) (P : Measure Ω)
    (W₁ W₂ : ℝ≥0 → Ω → ℝ) (Ψ : Ω → Measure ℂ → ℝ) : Prop where
  bm₁ : IsBrownianReal W₁ P
  bm₂ : IsBrownianReal W₂ P
  indep : IndepFun (fun ω t => W₁ t ω) (fun ω t => W₂ t ω) P
  regular : ∀ᵐ ω ∂P, IsRegularArcField (Ψ ω)
  law : IsCondGaussianFieldOn P (pathSigma W₁ ⊔ pathSigma W₂) Set.univ IsAdmissible Ψ
    (fun ω μ => ∫ u, wedgeMean α (Qc γ) (fun t => W₁ t ω) (fun t => W₂ t ω) u ∂μ)
    (fun _ μ ν => kernelEnergy lateralGreen μ ν)

end QuantumZipper.Welding


