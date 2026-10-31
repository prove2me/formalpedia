-- Prove2me | Definitions.Def_SupplierLearning_Params_SecondOrder
-- name    : SupplierLearning_Params_SecondOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:01.464457+00:00
-- url     : https://prove2.me/theorems/3af6b152-7140-4af7-b092-6379b00d2511
-- title:
--   Second-order conditions (hypotheses E1, E3)
-- statement:
--   The second-order conditions:
--
--   1. (E1) $\delta\rho(r^\ell)^2<4$;
--   2. (E3) if $r^h>\nu r^\ell$ then Condition (A3) holds, and if $r^h\le\nu r^\ell$ then $\delta\rho^2B^2<4$, where $B=(r^h-\nu r^\ell)/(1-\nu)$.
--
--   **Formalization Note** The printed proposition states neither. Without them an optimum may not exist or may fail to be unique: at $a_1=a_2=100$, $c^\ell=10$, $c^h=11$, $r^\ell=r^h=3$, $\delta=\rho=9/10$, $\nu=1/2$ the supremum of $\tilde V$ on $\Phi$ is $+\infty$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, correction of Proposition 1, p.13; (A3), App. p.7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_B
import Definitions.Def_SupplierLearning_Params_ConditionA3

namespace SupplierLearning

/-- **Second-order conditions (hypotheses E1, E3).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, correction of Proposition 1, p.13; (A3), App. p.7 (PDF p.13, 39).

**Formalization Note.** Not in the printed proposition; corrections C2 and C6. (A3) is required only when `r^h > ν r^ℓ`; when `r^h ≤ ν r^ℓ` the type-h objective is the pooled quadratic everywhere, and `δρ²B² < 4` is the matching condition. No condition `δρ(r^h)² < 4` is assumed. -/
structure Params.SecondOrder (P : Params) : Prop where
  learning : P.δ * P.ρ * P.rl ^ 2 < 4
  separating : P.ν * P.rl < P.rh → P.ConditionA3
  pooling : P.rh ≤ P.ν * P.rl → P.δ * P.ρ ^ 2 * P.B ^ 2 < 4

end SupplierLearning


