-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_phiAux
-- name    : KallMayerSLP_Multistage_phiAux
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:55.040993+00:00
-- url     : https://prove2.me/theorems/debbfbc6-874e-4c6f-b000-84bce659440f
-- title:
--   Backward recursion behind $\Phi_t$
-- statement:
--   This auxiliary function runs the recursion (3.15) by the number of stages from the end: $k=0$ gives $\Phi_{T+1}\equiv0$, and the step from $k$ to $k+1$ takes, at stage $t=T-k$, the expectation over $\xi_t$ of the stage problem built on the previous function. It is used through $\Phi_t$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.15), p.263 (PDF 272)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_stageMin
import Definitions.Def_KallMayerSLP_Multistage_toHist
import Definitions.Def_WassersteinDRO_Duality_erealExpectation

namespace KallMayerSLP.Multistage

open MeasureTheory WassersteinDRO.Duality

/-- The backward recursion behind `Phi`: `phiAux D μ k` is `Φ_{T+1-k}` (Kall & Mayer, *Stochastic
Linear Programming* (2005), Chapter 3, (3.15), p.263, PDF 272). `phiAux D μ 0` is `Φ_{T+1} ≡ 0`, and
for `t = T - k`, `phiAux D μ (k+1)` is `𝔼_{ξ_t}[r_t]` with `r_t` the stage problem built on
`phiAux D μ k`. `μ t` is the law `ℙ_{ξ_t}`. Use it through `Phi`. -/
noncomputable def phiAux (D : MSLP) (μ : ∀ t, Measure (Fin (D.r t) → ℝ)) :
    ℕ → (∀ τ, Fin (D.n τ) → ℝ) → (∀ s, Fin (D.r s) → ℝ) → EReal
  | 0, _, _ => 0
  | k + 1, z, w =>
    erealExpectation (μ (D.T - k)) fun v =>
      stageMin D (D.T - k) (D.b (D.T - k) (toHist (D.T - k) (Function.update w (D.T - k) v)))
        (fun z' => phiAux D μ k z' (Function.update w (D.T - k) v)) z

end KallMayerSLP.Multistage


