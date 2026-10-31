-- Prove2me | Definitions.Def_SupplierLearning_Params_Feasible
-- name    : SupplierLearning_Params_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:50:54.426355+00:00
-- url     : https://prove2.me/theorems/243ab1a1-4ad8-427b-ae42-d204e6b00c05
-- title:
--   The feasible set $\Phi$ of regime $\mathcal P^{\mathrm{AL}}$
-- statement:
--   A contract $\phi$ is **feasible**, $\phi\in\Phi$, when, for all types and outcomes:
--
--   1. all quantities are nonnegative;
--   2. every first-period quantity satisfies Condition (C), $q_1\le Q$, where $Q=\frac{c^h-c^\ell}{r^h-r^\ell}$ if $r^\ell<r^h$ and $Q=\infty$ otherwise;
--   3. (IR$^\theta$) $U(\theta)\ge0$;
--   4. (IC$^\theta$) $\tilde U(\theta;\check\theta)\le U(\theta)$ for every $\check\theta$;
--   5. (IC$^{\theta\Lambda}$) reporting the true outcome is optimal in period 2, after a truthful report of the type.
--
--   **Formalization Note** Nonnegativity of quantities is a reading. (C) is encoded as $(r^h-r^\ell)q_1\le c^h-c^\ell$, equivalent for $q_1\ge0$ and free of $\infty$. (C) restricts the menu, so it lies in $\Phi$ and is not a parameter assumption.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8, (IR^θ), (IC^θ), (IC^θΛ), and (C), p.7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_stagePayoff
import Definitions.Def_SupplierLearning_Params_supplierPayoff
import Definitions.Def_SupplierLearning_Params_U

namespace SupplierLearning

/-- **The feasible set \Phi of regime P^{AL}.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8, (IR^θ), (IC^θ), (IC^θΛ), and (C), p.7 (PDF p.7, 8).

**Formalization Note.** All three constraint families are kept, for both types and both outcomes; in particular (IC^h), which the paper's proof does not check. Nonnegative quantities are a reading (they are production quantities; the paper never says so). (C) `q₁ ≤ Q` is written `(r^h − r^ℓ) q₁ ≤ c^h − c^ℓ`, which for `q₁ ≥ 0` is the same set and needs no `∞`; it applies to every first-period quantity of the menu. -/
structure Params.Feasible (P : Params) (φ : Contract) : Prop where
  q₁_nonneg : ∀ θ, 0 ≤ (φ θ).q₁
  q₂_nonneg : ∀ θ Λ, 0 ≤ (φ θ).q₂ Λ
  capacity : ∀ θ, (P.rh - P.rl) * (φ θ).q₁ ≤ P.ch - P.cl
  ir : ∀ θ, 0 ≤ P.U φ θ
  ic_type : ∀ θ θ', P.supplierPayoff φ θ θ' ≤ P.U φ θ
  ic_outcome : ∀ θ Λ Λ', P.stagePayoff θ Λ (φ θ) Λ' ≤ P.stagePayoff θ Λ (φ θ) Λ

end SupplierLearning


