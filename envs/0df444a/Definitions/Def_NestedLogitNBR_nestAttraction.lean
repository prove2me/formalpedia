-- Prove2me | Definitions.Def_NestedLogitNBR_nestAttraction
-- name    : NestedLogitNBR_nestAttraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:35:52.656315+00:00
-- url     : https://prove2.me/theorems/55e5601d-099a-4d29-b400-d7f5cdcf7db0
-- title:
--   Nest attraction $V_i(S)^{\gamma_i}$
-- statement:
--   For nest $i$ with dissimilarity parameter $\gamma_i\ge0$, the attraction of an assortment $S$ is
--
--   $$
--   V_i(S)^{\gamma_i},\qquad V_i(S)=\sum_{j\in S}v_{ij}.
--   $$
--
--   A customer chooses nest $i$ with probability $V_i(S_i)^{\gamma_i}/(v_0+\sum_{l}V_l(S_l)^{\gamma_l})$ (eq. (1), p. 7), and $V_i(S)^{\gamma_i}$ multiplies $R_i(S)-x$ in the constraints of problems (3) and (4).
--
--   **Formalization Note** The power is the real power `Real.rpow`. When $V_i(S)=0$ the attraction is taken to be $0$, also when $\gamma_i=0$ (where `Real.rpow` gives $0^0=1$): the paper uses $V_i(\emptyset)^{\gamma_i}(R_i(\emptyset)-\hat x)=0$ to conclude $\hat y_i\ge0$ (App. A.1, p. 41), and an assortment of total weight $0$ is never chosen (p. 7).
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), §1, eq. (1), p. 7; constraints of problems (3)-(4), pp. 11-12; App. A.1, p. 41 (V_i(∅) term)

import Mathlib
import Definitions.Def_NestedLogitNBR_prefWeight

namespace NestedLogitNBR

/-- **Nest attraction `V_i(S)^{γ_i}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), eq. (1), p. 7: a customer chooses nest `i` with probability
`V_i(S_i)^{γ_i} / (v_0 + Σ_{l∈M} V_l(S_l)^{γ_l})`, where `γ_i ≥ 0` is the dissimilarity
parameter of nest `i`. `V_i(S)^{γ_i}` is the quantity multiplying `(R_i(S_i) − x)` in the
constraints of problems (3) and (4) (pp. 11–12).

**Formalization Note.** The power is `Real.rpow`. When `V_i(S) = 0` the value is `0`, also for
`γ_i = 0`, where `Real.rpow` would give `0 ^ 0 = 1`: the paper uses
`V_i(∅)^{γ_i}(R_i(∅) − x̂) = 0` (App. A.1, p. 41, "Noting that `V_i(∅) = 0`, it follows that
`ŷ_i ≥ 0`") and an assortment of total weight `0` is never chosen (p. 7). For `V_i(S) > 0` the
value is `V_i(S) ^ γ_i`. -/
noncomputable def nestAttraction {m n : ℕ} (v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m)
    (S : Finset (Fin n)) : ℝ :=
  if prefWeight v i S = 0 then 0 else prefWeight v i S ^ γ i

end NestedLogitNBR


