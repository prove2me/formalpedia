-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_markovWealth
-- name    : BauerleRiederMDP_LQ_Supplement_CIRandom_markovWealth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:05:22.903807+00:00
-- url     : https://prove2.me/theorems/be2f4743-7752-540d-a934-244cc32867f9
-- title:
--   The wealth under a stationary decision rule
-- statement:
--   **The wealth under a stationary decision rule** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.1, pp.268–269, PDF 278–279): for a decision rule $f = (f_c, f_a) : E \to  \mathbb R _+ \times  \mathbb R ^d$ of the model of §9.1, the stationary strategy $(f, f, \dots )$ consumes $c_n = f_c(X_n)$ and invests $\varphi _n = f_a(X_n)$, so that $X_{n+1} = X_n - f_c(X_n) + f_a(X_n) \cdot  R_{n+1}$.
--
--   **Formalization Note.** The rule is evaluated at $X_n^+$ ($E = [0, \infty )$), which is $X_n$ almost surely along an admissible strategy. The path is 0-indexed ($r j = R_{j+1}$).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.1, pp.268–269, PDF 278–279

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom

open scoped NNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **The wealth under a stationary decision rule** (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), §9.1, pp.268–269, PDF 278–279): for a decision rule
`f = (f_c, f_a) : E → ℝ_+ × ℝ^d` of the model of §9.1, the stationary strategy `(f, f, …)` consumes
`c_n = f_c(X_n)` and invests `φ_n = f_a(X_n)`, so that `X_{n+1} = X_n − f_c(X_n) + f_a(X_n) · R_{n+1}`.

**Formalization Note.** The rule is evaluated at `X_n⁺` (`E = [0, ∞)`), which is `X_n` almost
surely along an admissible strategy. The path is 0-indexed (`r j = R_{j+1}`). -/
noncomputable def CIRandom.markovWealth {d : ℕ} (f : ℝ≥0 → ℝ × (Fin d → ℝ)) (x : ℝ) :
    (n : ℕ) → (Fin n → Fin d → ℝ) → ℝ
  | 0, _ => x
  | n + 1, r =>
      CIRandom.markovWealth f x n (Fin.init r) - (f (CIRandom.markovWealth f x n (Fin.init r)).toNNReal).1 +
        ∑ k, (f (CIRandom.markovWealth f x n (Fin.init r)).toNNReal).2 k * r (Fin.last n) k

end BauerleRiederMDP.LQ.Supplement


