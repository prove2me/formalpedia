-- Prove2me | Definitions.Def_OmniMix_IsAlg2Run
-- name    : OmniMix_IsAlg2Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:52.232234+00:00
-- url     : https://prove2.me/theorems/249dccc2-f224-475a-925d-a9dfb303327e
-- title:
--   A run of Algorithm 2
-- statement:
--   Fix a finite class $F$, a horizon $T$, a learning rate $\eta$ and a context–outcome sequence $(x_t,y_t)$. A sequence of forecasts $D_1,\dots,D_T$ is a **run of Algorithm 2** if in every round $t$:
--   1. $D_t$ is supported in $I_\delta$, $\delta=1/(2(T+1))$;
--   2. $D_t$ solves the EVI for the test function $G_t$ of Eq. (25):
--   $$
--   \mathbb E_{P\sim D_t}\big[G_t(P)(y-P)\big]\le\epsilon_t=\frac1T\qquad\text{for both }y\in\{0,1\}.
--   $$
--
--   **Formalization Note** "An EVI solver" is any rule that meets the EVI condition, so a run is any forecast sequence meeting it in every round. The learning rate range $0<\eta\le1/2$ is a hypothesis of the theorems that use runs.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Algorithm 2, p.15

import Mathlib
import Definitions.Def_OmniMix_alg2G
import Definitions.Def_OmniMix_outVal

namespace OmniMix

/-- **A run of Algorithm 2.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, Algorithm 2, p.15: "Use the EVI solver to find a distribution
`D_t` over `I_δ`, satisfying `E_{P∼D_t}[G_t(P)(y − P)] ≤ ϵ_t`, for all `y ∈ {0, 1}`", with
`δ = 1/(2(T + 1))` and `ϵ_t = 1/T`.

`IsAlg2Run F T η x y D` says that on the context–outcome sequence `(x, y)`, for every round `t`, the
forecast `D_t` is supported in `I_δ` and satisfies the EVI condition for the test function `G_t`
computed from `D_0, …, D_{t−1}`, `x` and `y` (rounds `< t`) and the current context `x_t`.

**Formalization Note.** "An EVI solver" is any rule meeting the EVI condition; a run is any
sequence of forecasts that meets it in every round. The learning rate `η` (`0 < η ≤ 1/2` in the
paper) is a parameter; theorems state its range. Rounds are 0-based. -/
def IsAlg2Run {X : Type*} (F : Finset (X → unitInterval)) (T : ℕ) (η : ℝ) (x : Fin T → X)
    (y : Fin T → Bool) (D : Fin T → FinDist) : Prop :=
  ∀ t : Fin T, (∀ P ∈ (D t).wt.support, (P : ℝ) ∈ Idelta (deltaT T)) ∧
    ∀ y' : Bool, (D t).expectR (fun P => alg2G F T η x y D t P * (outVal y' - P)) ≤ 1 / (T : ℝ)

end OmniMix


