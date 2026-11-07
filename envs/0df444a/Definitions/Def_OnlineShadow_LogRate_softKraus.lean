-- Prove2me | Definitions.Def_OnlineShadow_LogRate_softKraus
-- name    : OnlineShadow_LogRate_softKraus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:08:39.117545+00:00
-- url     : https://prove2.me/theorems/abd5e88b-cab8-4499-9bf2-fdcab2c9afd0
-- title:
--   Kraus operators of the soft binary measurement of $(B,\theta)$
-- statement:
--   For a single-copy observable $B$, threshold $\theta$, accuracy $\varepsilon$ and sharpness $\lambda$, the **soft binary measurement corresponding to $(B,\theta)$** on $n$ copies has the two outcomes flag and pass, with Kraus operators
--   $$\Big(\sqrt{f_{\theta,\lambda}(\overline B)},\ \sqrt{1-f_{\theta,\lambda}(\overline B)}\Big),\qquad f_{\theta,\lambda}(x)=\frac1{1+e^{\lambda(\theta-\varepsilon/8-x)}},$$
--   where $\overline B$ is the lifted observable. It flags with high probability when the empirical average of $B$ is above $\theta$ and passes with high probability when it is below $\theta-\varepsilon/4$.
--
--
--   **Formalization Note** The outcome flag is `true`, pass is `false`. The function $\sqrt{f}$ or $\sqrt{1-f}$ is applied to the Hermitian matrix $\overline B$ by the functional calculus.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 4.2, p. 11

import Mathlib
import Definitions.Def_OnlineShadow_LogRate_liftObs
import Definitions.Def_OnlineShadow_LogRate_logistic

namespace OnlineShadow.LogRate

/-- The Kraus operators of the **soft binary measurement** corresponding to `(B, θ)` on `n` copies
(Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 4.2, p.11): `(√f_{θ,λ}(B̄), √(1 − f_{θ,λ}(B̄)))` for the outcomes flag (`true`) and
pass (`false`), with `f_{θ,λ}(x) = 1/(1 + e^{λ(θ − ε/8 − x)})` and `B̄` the lifted observable.

**Formalization Note** The function is applied by the continuous functional calculus to the Hermitian
matrix `liftObs n B`; `√f(B̄)` is the calculus of `√ ∘ f`. -/
noncomputable def softKraus {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (ε lam θ : ℝ)
    (B : Matrix ι ι ℂ) (flag : Bool) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  cfc (fun x : ℝ => Real.sqrt (if flag then logistic (θ - ε / 8) lam x
    else 1 - logistic (θ - ε / 8) lam x)) (liftObs n B)

end OnlineShadow.LogRate


