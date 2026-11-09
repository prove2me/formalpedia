-- Prove2me | Definitions.Def_MWCSherali_FK
-- name    : MWCSherali_FK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:17.981198+00:00
-- url     : https://prove2.me/theorems/d4dcf5a4-21fb-4b01-b5e0-3fd628a64801
-- title:
--   The corner flows $F^{K_a}_{a,i}$
-- statement:
--   For $x$ with $x_a=\alpha$ let $\gamma_{a,x}(\tau)=\big(1-\frac{\tau}{1-\alpha}\big)e_a+\frac{\tau}{1-\alpha}x$, $0\le\tau\le1-\alpha$, the straight path from $e_a$ to $x$. For $i\neq a$ the **corner flow** $F^{K_a}_{a,i}$ is defined by
--
--   $$\int\varphi\,dF^{K_a}_{a,i}=\int x_i\Big(\frac1{1-\alpha}\int_0^{1-\alpha}\varphi(\gamma_{a,x}(\tau))\,d\tau\Big)\,d\mu_a(x).$$
--
--   It is also the corner capacity $B^{K_a}_i$; all other measures vanish in the corner.
--
--   **Formalization Note** It is the image of $(x_i\,\mu_a)\otimes\frac1{1-\alpha}\mathrm{Leb}|_{[0,1-\alpha]}$ under $(x,\tau)\mapsto\gamma_{a,x}(\tau)$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4.1, p.33

import Mathlib
import Definitions.Def_MWCSherali_muCorner

namespace MWCSherali

open MeasureTheory

/-- **The corner flows `F^{K_a}_{a,i}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4.1, p.33: with the straight paths
`γ_{a,x}(τ) = (1 − τ/(1 − α)) e_a + (τ/(1 − α)) x`, `0 ≤ τ ≤ 1 − α`, for `x_a = α`,
"`∫ φ dF^{K_a}_{a,i} = ∫ x_i (1/(1 − α) · ∫₀^{1−α} φ(γ_{a,x}(τ)) dτ) dμ_a(x)`" for `i ≠ a`.
Also "`B^{K_a}_i = F^{K_a}_{a,i}` for every `i ≠ a`, and all other measures are set to be `0` in
this corner".

`FK α β C a i` is the image of `(x_i · μ_a) ⊗ (1/(1 − α)) · Leb|_{[0, 1−α]}` under
`(x, τ) ↦ γ_{a,x}(τ)`, which is the displayed formula.

**Formalization Note.** The densities `x_i` and `1/(1 − α)` enter through `ENNReal.ofReal`; they
are nonnegative on the support (`x ∈ Δ₄`, `α < 1`). The same measure is the corner capacity
`B^{K_a}_i`. -/
noncomputable def FK (α β C : ℝ) (a i : Fin 4) : Measure (Fin 4 → ℝ) :=
  Measure.map
    (fun p : (Fin 4 → ℝ) × ℝ => (1 - p.2 / (1 - α)) • Pi.single a 1 + (p.2 / (1 - α)) • p.1)
    (((muCorner α β C a).withDensity fun x => ENNReal.ofReal (x i)).prod
      (ENNReal.ofReal (1 / (1 - α)) • volume.restrict (Set.Icc 0 (1 - α))))

end MWCSherali


