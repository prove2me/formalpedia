-- Prove2me | Definitions.Def_PercCubeCycles_Percolation
-- name    : PercCubeCycles_Percolation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:43.213708+00:00
-- url     : https://prove2.me/theorems/cb96f0fa-c3fb-40af-a23d-1d5261860102
-- title:
--   The hypercube $Q^d$, with high probability, and the parameters $\alpha,m,M$
-- statement:
--   The hypercube $Q^d$ has vertex set $\{0,1\}^d$, with two vertices adjacent if they differ in a single coordinate. $Q^d_p$ retains each edge independently with probability $p$. A sequence of events $(\mathcal E_d)$ holds **with high probability** (whp) if $\Pr(\mathcal E_d)\to1$ as $d\to\infty$.
--
--   The main regime is $p(d)=(1+\varepsilon)/d$, and the scale parameters of Theorem 6 are
--   $$\alpha=\varepsilon^{1/\varepsilon^{20}},\qquad m=\varepsilon^2 2^{\alpha d},\qquad M=\varepsilon^{-2}2^{\alpha d}.$$
--
--   **Formalization Note** $Q^d_p$ is the published bond percolation `RandomGames.BRD.percMeasure` with `openGraph`. For $d<1+\varepsilon$ the parameter exceeds $1$, which `Whp` does not see because it is a limit. Powers of $\varepsilon$ and $2$ with real exponents are `Real.rpow`.
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), p.2; footnote 1, p.3; Theorem 6, p.10

import Mathlib
import Definitions.Def_RandomGames_BRD_Percolation

set_option autoImplicit false

open Filter Topology

namespace PercCubeCycles

open RandomGames.BRD

/-!
# The hypercube, whp, and the parameters of Theorem 6

Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…): `Q^d` and `Q^d_p`, p.2; whp, footnote 1, p.3; `α, m, M`, Theorem 6, p.10.

**Formalization Note.** `Q^d_p` is the published bond percolation: `percMeasure p d` on `Edge d → Bool`
and `openGraph ω` on `Fin d → Bool`. For `d < 1 + ε` the parameter `(1 + ε)/d` is above `1`; `Whp` sees
only large `d`. `2^{αd}` and `ε^{1/ε²⁰}` are real powers.
-/

/-- p.2: the hypercube `Q^d`: every edge open. -/
def cube (d : ℕ) : SimpleGraph (Profile d) := openGraph fun _ => true

/-- Footnote 1, p.3: the events `E d` of `Q^d_{p(d)}` hold with high probability: `Pr(E_d) → 1`
as `d → ∞`. -/
def Whp (p : ℕ → ℝ) (E : (d : ℕ) → (Edge d → Bool) → Prop) : Prop :=
  Tendsto (fun d => percMeasure (p d) d {ω | E d ω}) atTop (𝓝 1)

/-- p.3: `p(d) = (1 + ε)/d`. -/
noncomputable def supercritical (ε : ℝ) (d : ℕ) : ℝ := (1 + ε) / d

/-- Theorem 6, p.10: `α(ε) = ε^{1/ε²⁰}`. -/
noncomputable def alphaOf (ε : ℝ) : ℝ := ε ^ (1 / ε ^ 20 : ℝ)

/-- Theorem 6, p.10: `2^{αd}`. -/
noncomputable def medScale (ε : ℝ) (d : ℕ) : ℝ := (2 : ℝ) ^ (alphaOf ε * d)

/-- Theorem 6, p.10: `m(ε, d) = ε² · 2^{αd}`. -/
noncomputable def mLow (ε : ℝ) (d : ℕ) : ℝ := ε ^ 2 * medScale ε d

/-- Theorem 6, p.10: `M(ε, d) = ε⁻² · 2^{αd}`. -/
noncomputable def mHigh (ε : ℝ) (d : ℕ) : ℝ := (ε ^ 2)⁻¹ * medScale ε d

end PercCubeCycles


