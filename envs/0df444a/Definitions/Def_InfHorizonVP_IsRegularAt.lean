-- Prove2me | Definitions.Def_InfHorizonVP_IsRegularAt
-- name    : InfHorizonVP_IsRegularAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:19.143624+00:00
-- url     : https://prove2.me/theorems/2c42f8bc-715d-45ab-9641-0855553de9bf
-- title:
--   Regularity (in the sense of Clarke) of a function at a point
-- statement:
--   A function $\varphi:E\to\mathbb R$ that is Lipschitz near $\bar x$ is **regular** at $\bar x$ if, for every $v\in E$, the classical directional derivative
--   $$
--   \varphi'(\bar x;v)=\lim_{\theta\downarrow0}\frac{\varphi(\bar x+\theta v)-\varphi(\bar x)}{\theta}
--   $$
--   exists and equals the Clarke directional derivative $\varphi^\circ(\bar x;v)$.
--
--   **Formalization Note** "Lipschitz near $\bar x$" (a standing condition of the page's definition) is part of the definition: Lipschitz on some neighbourhood of $\bar x$. $\varphi^\circ$ is the published `QuasiHemiVI.Existence.clarkeDeriv`.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.4

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Regularity of a function at a point (Clarke).**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.4: "Recall that the function ϕ that is Lipschitz
near x̄ is said to be regular at x̄ if the classical directional derivative
ϕ′(x̄; v) := lim_{θ↓0} (ϕ(x̄ + θv) − ϕ(x̄))/θ exists and ϕ′(x̄; v) = ϕ°(x̄; v) for every v ∈ E."

`IsRegularAt φ x̄` says `φ` is Lipschitz near `x̄` and, for every `v`, the one-sided difference
quotient converges as `θ ↓ 0` to the Clarke directional derivative `φ°(x̄; v)`.

**Formalization Note.** "Lipschitz near x̄" is Lipschitz on some neighbourhood of `x̄`; `φ°` is the
Clarke directional derivative `QuasiHemiVI.Existence.clarkeDeriv` (a genuine `limsup` for a function
Lipschitz near `x̄`). -/
def IsRegularAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → ℝ) (x : E) : Prop :=
  (∃ K : NNReal, ∃ U ∈ 𝓝 x, LipschitzOnWith K φ U) ∧
  ∀ v : E, Tendsto (fun θ : ℝ => (φ (x + θ • v) - φ x) / θ) (𝓝[>] 0)
    (𝓝 (QuasiHemiVI.Existence.clarkeDeriv φ x v))

end InfHorizonVP


