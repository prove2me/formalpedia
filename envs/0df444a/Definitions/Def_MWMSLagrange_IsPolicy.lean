-- Prove2me | Definitions.Def_MWMSLagrange_IsPolicy
-- name    : MWMSLagrange_IsPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:45.774995+00:00
-- url     : https://prove2.me/theorems/abf4bd6e-6588-4334-8c8f-ef48825a9eb1
-- title:
--   Non-anticipating shipment policy
-- statement:
--   A **shipment policy** prescribes, for every period $t$, warehouse $j$ and store $i$, a shipment $z_{i,j,t}(\omega)$ such that
--
--   1. $z_{i,j,t}$ is a measurable function of the demand path;
--   2. $z_{i,j,t}$ depends only on the demands $D_{\cdot,s}$ of periods $s<t$ (it is decided before $D_{\cdot,t}$ is realized);
--   3. $z_{i,j,t}\ge0$;
--   4. $z_{i,j,t}=0$ when $j\notin\mathcal M_i$.
--
--   This is the class of non-anticipating policies of (2.1) without the warehouse constraint.
--
--   **Formalization Note** The paper writes a policy as order-up-to levels $y^\pi_{i,t}\ge I^\pi_{i,t}$ and fractions $\rho^\pi_{i,j,t}$; $z=\rho^\pi(y^\pi-I^\pi)$ and $\rho^\pi=z/\sum_j z$ translate between the two forms.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, pp.7–8, (2.1)

import Mathlib
import Definitions.Def_MWMSLagrange_Instance

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, pp.7–8: a
non-anticipating shipment policy. The shipment `z_{i,j,t}(ω)` from warehouse `j` to store `i`
in period `t`

1. is a measurable function of the demand path,
2. depends only on the demands `D_{i',s}` of the periods `s < t` (non-anticipation: it is
   decided at the beginning of period `t`, before `D_{·,t}` is realized),
3. is nonnegative (`z_{i,j,t} ∈ ℝ_+`, p.7; equivalently `y^π ≥ I^π` and `ρ^π ∈ [0, 1]`), and
4. is zero unless `j ∈ 𝓜_i`.

No warehouse constraint is imposed here; see `FeasiblePolicy` and `RelaxedPolicy`.

**Formalization Note.** Policies are deterministic shipment rules; the paper's `(y^π, ρ^π)`
form of (2.1) is the same class (`z = ρ(y − I)`). -/
def IsPolicy {M N T : ℕ} (I : Instance M N)
    (z : Fin T → (Fin N × Fin T → ℝ) → Fin N → Fin M → ℝ) : Prop :=
  (∀ t i j, Measurable fun ω => z t ω i j) ∧
    (∀ t ω ω', (∀ (i : Fin N) (s : Fin T), s < t → ω (i, s) = ω' (i, s)) → z t ω = z t ω') ∧
    (∀ t ω i j, 0 ≤ z t ω i j) ∧
    (∀ t ω i j, I.adj i j = false → z t ω i j = 0)

end MWMSLagrange


