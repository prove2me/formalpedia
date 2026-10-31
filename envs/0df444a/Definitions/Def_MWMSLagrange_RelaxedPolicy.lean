-- Prove2me | Definitions.Def_MWMSLagrange_RelaxedPolicy
-- name    : MWMSLagrange_RelaxedPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:42.974368+00:00
-- url     : https://prove2.me/theorems/2e678f38-fd99-4a5a-a7d6-260d4636b4b6
-- title:
--   Relaxed policy of the Lagrangian problem (3.3)
-- statement:
--   A **relaxed policy** is a shipment policy with the warehouse constraint dropped, as in the Lagrangian relaxation problem (3.3), whose shipments $z_{i,j,t}$ are integrable under the demand law.
--
--   **Formalization Note** Integrability is required because the objective (3.3) contains $\mathbb E[z_{i,j,t}]$; without it Lean's integral would silently return $0$.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), (3.3), p.10

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_IsPolicy
import Definitions.Def_MWMSLagrange_demandMeasure

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), (3.3), p.10: a policy of
the Lagrangian relaxation problem: a non-anticipating shipment policy (`IsPolicy`) with the
warehouse constraint `∑_{i∈𝓝_j} ∑_t z_{i,j,t} ≤ C_j` dropped.

**Formalization Note.** Each shipment `z_{i,j,t}` is required to be integrable under the
demand law: the expectations `E[ρ^π_{i,j,t}(y^π_{i,t} − I^π_{i,t})] = E[z_{i,j,t}]` of (3.3)
presuppose it, and Lean's Bochner integral would otherwise return `0`. -/
structure RelaxedPolicy {M N T : ℕ} (I : Instance M N) (μ : Fin N → Fin T → Measure ℝ) where
  /-- the shipments `z t ω i j` from warehouse `j` to store `i` in period `t` -/
  z : Fin T → (Fin N × Fin T → ℝ) → Fin N → Fin M → ℝ
  isPolicy : IsPolicy I z
  integrable : ∀ t i j, Integrable (fun ω => z t ω i j) (demandMeasure μ)

end MWMSLagrange


