-- Prove2me | Definitions.Def_PermBlockchain_Transfers_demand
-- name    : PermBlockchain_Transfers_demand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:00:34.610836+00:00
-- url     : https://prove2.me/theorems/15a09ca5-6ddf-4d81-ba75-e25cdf4362b4
-- title:
--   Consumer demand $s_i$, display (7)
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   Consumers have type $t\in\{A,B\}$ with probability $1/2$ each and an outside option $\phi\sim G$. The demand of manufacturer $i$ at history $x$ under the true assignment $\theta$ is
--   $$s_i=\frac12\sum_{t\in\{A,B\}}\int w\bigl(t,\phi,x,b,r\bigr)(i)\,dG(\phi),\qquad b=\text{fee}(t,\phi,x),\ r=\text{revelation of }b\text{ under }\theta,$$
--   the measure of the consumers who buy from $i$, as in $s_i=\mu(\{k:m(k)=i\})$ (7).
--
--   **Formalization Note** The continuum of consumers $k\in[0,1]$ is represented by the population distribution of $(t_k,\phi_k)$; decisions depend only on $\mathcal G_k$, so the masses agree.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, pp. 9 and 12 (PDF pp. 10 and 13), display (7)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_revealed
import Definitions.Def_PermBlockchain_Transfers_FeeRule
import Definitions.Def_PermBlockchain_Transfers_PurchaseRule

namespace PermBlockchain.Transfers

/-- **Consumer demand `s_i = μ({k : m(k) = i})`, display (7).**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 12 (PDF p. 13), (7). Consumers are a unit mass; type `t_k ∈ {A, B}` "with
equal probability" (p. 9) and outside option `φ_k` "a random draw from a continuous distribution
G" (p. 9).

`demand ν fee w θ x i` is the mass of consumers who buy from `i` at history `x` when the true type
assignment is `θ`: consumers of type `t` (mass `1/2` each) with outside option `φ ~ ν` choose
`b = fee t φ x`, observe `revealed b θ x` and buy from `i` with weight `w t φ x b (revealed b θ x) (some i)`.

**Formalization Note.** The continuum `k ∈ [0, 1]` is replaced by the population measure
(uniform on `{A, B}`) ⊗ `ν` on `(t_k, φ_k)`: decisions depend on `G_k` only, so the two give the
same masses. -/
noncomputable def demand {m : ℕ} (ν : MeasureTheory.Measure ℝ) (fee : FeeRule m)
    (w : PurchaseRule m) (θ : Mfr m → MType) (x : Hist m) (i : Mfr m) : ℝ :=
  (1 / 2 : ℝ) * ∑ t : Horiz, ∫ φ, w t φ x (fee t φ x) (revealed (fee t φ x) θ x) (some i) ∂ν

end PermBlockchain.Transfers


