-- Prove2me | Definitions.Def_SelectiveDPT_advPm
-- name    : SelectiveDPT_advPm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:55.417535+00:00
-- url     : https://prove2.me/theorems/e0c708ee-4fab-4a7d-a9df-f6700f132455
-- title:
--   Negative-weights adversary bound $\mathrm{ADV}^\pm_{\varepsilon,\mathcal D}(f)$ and $\mathrm{ADV}^\pm_\varepsilon(f)$
-- statement:
--   Let $\tau^\pm(\varepsilon) = 2\sqrt{\varepsilon(1-\varepsilon)} + \varepsilon$. For a function $f : D \to Y$, a distribution $\mu$ on $D$ and an error $\varepsilon$,
--   $$\mathrm{ADV}^\pm_{\varepsilon,\mathcal D}(f) = \sup_{\Gamma^\pm} \frac{1 - \tau^\pm(\varepsilon)}{2\max_i \|\Gamma^\pm \circ D_i\|},$$
--   the supremum over witnesses $\Gamma^\pm$ to Proposition 2.5 for $f$ under $\mu$: the largest lower bound $T \ge (1-\tau^\pm(\varepsilon))/\delta^\pm(\Gamma^\pm)$ that Proposition 2.5 yields. Further $\mathrm{ADV}^\pm_\varepsilon(f) = \max_{\mathcal D} \mathrm{ADV}^\pm_{\varepsilon,\mathcal D}(f)$ over all distributions on $D$.
--
--   **Formalization Note** Values in $[0,\infty]$: a negative bound counts as $0$ and the supremum over no witness is $0$. The general $\tau^\pm(\varepsilon)$ is used for every output set; Proposition 2.5's tightening to $2\sqrt{\varepsilon(1-\varepsilon)}$ for Boolean outputs is not built in.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Proposition 2.5 and Definition 2.6, p.13

import Mathlib
import Definitions.Def_SelectiveDPT_IsNegAdvWitness
import Definitions.Def_SelectiveDPT_maskC

open scoped ENNReal

namespace SelectiveDPT

open QAlgorithms

/-- The terminal value `τ±(ε) = 2√(ε(1 − ε)) + ε` of the normalized negative-weights adversary
method (arXiv:2609.26678, Proposition 2.5, p.13). -/
noncomputable def tauPm (ε : ℝ) : ℝ :=
  2 * Real.sqrt (ε * (1 - ε)) + ε

/-- `ADV±_{ε,D}(f)`, the largest lower bound achievable with Proposition 2.5 under the
distribution `μ` and error `ε` (arXiv:2609.26678, Definition 2.6, p.13): the supremum over
witnesses `Γ±` (`IsNegAdvWitness`) of `(1 − τ±(ε)) / δ±(Γ±)` with
`δ±(Γ±) = 2 max_i ‖Γ± ∘ D_i‖`.

**Formalization Note.** Values in `[0, ∞]`: a negative bound counts as `0`, and the supremum over
no witness is `0`. The general `τ±(ε)` is used for every output set `Y` (the Boolean tightening of
Proposition 2.5 is not built in). The maximum over `i` is a real `⨆` over the finite index type. -/
noncomputable def advPmD {ι Y : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι] (μ : (ι → ZMod d) → ℝ)
    (D : Finset (ι → ZMod d)) (f : (ι → ZMod d) → Y) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ (Γ : Matrix D D ℂ) (_ : IsNegAdvWitness μ D f Γ),
    ENNReal.ofReal ((1 - tauPm ε) / (2 * ⨆ i : ι, specNorm (maskC Γ i)))

/-- `ADV±_ε(f) = max_D ADV±_{ε,D}(f)` (arXiv:2609.26678, Definition 2.6, p.13), the supremum over
all probability distributions `μ` on `D`. -/
noncomputable def advPm {ι Y : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι]
    (D : Finset (ι → ZMod d)) (f : (ι → ZMod d) → Y) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ (μ : (ι → ZMod d) → ℝ) (_ : IsDistOn μ D), advPmD μ D f ε

end SelectiveDPT


