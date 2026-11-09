-- Prove2me | Definitions.Def_BosonicLearn_collectiveSuccess
-- name    : BosonicLearn_collectiveSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:21:44.224696+00:00
-- url     : https://prove2.me/theorems/b6c7e9e3-b79e-4cdb-b56b-e912631dd10a
-- title:
--   Success probability of a collective (entangled) learning scheme
-- statement:
--   A collective scheme on $N$ copies is a single POVM $E$ on the $N$-copy space whose outcome is the estimate $\widehat\rho$, a density operator. Its success probability on $\rho$ at precision $\varepsilon$ is
--
--   $$\operatorname{Tr}\Big(E\big(\{\sigma:\tfrac12\|\sigma-\rho\|_1\le\varepsilon\}\big)\,\rho^{\otimes N}\Big).$$
--
--   Here $\rho^{\otimes N}$ has entries $\prod_t\rho_{u_tv_t}$ (the published tensor power of Wilde's Schumacher mission). Any measurement on $\rho^{\otimes N}$ followed by any classical post-processing has this form, so this covers every learning scheme, entangled or not.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 9, pp. 65–67

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_BosonicLearn_traceDist

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open scoped ENNReal

namespace BosonicLearn

/-- **Success probability of a collective (entangled) learning scheme.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 9, p. 65 ("any scheme that can learn any passive Gaussian state … to ε trace distance with 2/3
probability"), proved "even for arbitrary collective measurements" (p. 67).

A collective scheme on `N` copies is a single POVM `E` on `ℓ²(ℕⁿ)^{⊗N}` whose outcome is the estimate itself, a
density operator. `collectiveSuccess E ρ ε` is the Born probability, on `ρ^{⊗N}`, that `½‖ρ̂ − ρ‖₁ ≤ ε`.

**Formalization Note.** `ρ^{⊗N}` is the published `WildeQIT.Schumacher.tensorPow` (entries `∏ₜ ρ_{u_t v_t}` on
the index type `Fin N → ℕⁿ`). Any measurement followed by any classical (randomized) post-processing is again a
POVM with outcomes in the state space, so this covers every scheme. -/
noncomputable def collectiveSuccess {n N : ℕ}
    (E : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n))))
    (ρ : State (Occupation (Fin n))) (ε : ℝ) : ℝ≥0∞ :=
  E.law (WildeQIT.Schumacher.tensorPow N ρ.coefficients)
    {σ | traceDist σ.coefficients ρ.coefficients ≤ ENNReal.ofReal ε}

end BosonicLearn


