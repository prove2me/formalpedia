-- Prove2me | Definitions.Def_DSICCompComp_Supplement_dualFunction
-- name    : DSICCompComp_Supplement_dualFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:31:08.376198+00:00
-- url     : https://prove2.me/theorems/88a7e106-e095-43cc-ac66-439721f617ff
-- title:
--   Dual function $g(\lambda) = \max_{(x,p)\in P(D)} L(\lambda,x,p)$
-- statement:
--   The partial Lagrangian dual function is
--
--   $$
--   g(\lambda) \;=\; \max_{(x, p) \in P(D)} L(\lambda, x, p),
--   $$
--
--   which is finite exactly when $\lambda$ satisfies flow conservation (Lemma C.2) and $+\infty$ otherwise.
--
--   **Formalization Note** Taken as a supremum in the extended reals, so the value $+\infty$ is represented.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, p.35, and Lemma C.2, p.36 (pdf pp.36–37)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_InP
import Definitions.Def_DSICCompComp_Supplement_lagrangian

namespace DSICCompComp

namespace Supplement

/-- The partial Lagrangian dual function `g(λ) = max_{(x,p) ∈ P(D)} L(λ, x, p)`
(Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, p.35 and Lemma C.2, p.36 (pdf pp.36–37)).

**Formalization Note** Taken as a supremum in `EReal`: by Lemma C.2 it is `+∞` unless `λ` conserves
flow. -/
noncomputable def dualFunction {n m : ℕ} (E : FiniteSetting n m)
    (lam : (i : Fin n) → ((k : Fin n) → E.S k) → Option (E.S i) → ℝ) : EReal :=
  ⨆ (sol : LPSolution E) (_ : InP E sol), ((lagrangian E lam sol : ℝ) : EReal)

end Supplement

end DSICCompComp


