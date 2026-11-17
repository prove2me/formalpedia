-- Prove2me | Definitions.Def_DSICCompComp_Supplement_IsOptimalDual
-- name    : DSICCompComp_Supplement_IsOptimalDual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:32:01.342464+00:00
-- url     : https://prove2.me/theorems/55a55e92-56da-4eca-a988-7639be66dcb8
-- title:
--   Optimal dual solution $\lambda^*$
-- statement:
--   $\lambda^*$ is an **optimal dual solution** of the DSIC revenue LP if $\lambda^* \ge 0$ (the multipliers belong to inequality constraints) and it minimizes the dual function over all nonnegative dual solutions:
--
--   $$
--   g(\lambda^*) \;\le\; g(\lambda) \qquad \text{for all } \lambda \ge 0 .
--   $$
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, pp.35–37 (pdf pp.36–38)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_dualFunction

namespace DSICCompComp

namespace Supplement

/-- `λ*` is an optimal dual solution of the DSIC revenue LP (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, pp.35–37 (pdf pp.36–38)): `λ* ≥ 0` (Lagrange multipliers of inequality constraints) and
`λ*` minimizes the dual function `g(λ) = sup_{(x,p) ∈ P(D)} L(λ, x, p)` over all `λ ≥ 0`. -/
def IsOptimalDual {n m : ℕ} (E : FiniteSetting n m)
    (lam : (i : Fin n) → ((k : Fin n) → E.S k) → Option (E.S i) → ℝ) : Prop :=
  (∀ i v w, 0 ≤ lam i v w) ∧
    ∀ lam' : (i : Fin n) → ((k : Fin n) → E.S k) → Option (E.S i) → ℝ,
      (∀ i v w, 0 ≤ lam' i v w) → dualFunction E lam ≤ dualFunction E lam'

end Supplement

end DSICCompComp


