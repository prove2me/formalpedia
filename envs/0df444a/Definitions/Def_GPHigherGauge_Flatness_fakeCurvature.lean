-- Prove2me | Definitions.Def_GPHigherGauge_Flatness_fakeCurvature
-- name    : GPHigherGauge_Flatness_fakeCurvature
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:27.084165+00:00
-- url     : https://prove2.me/theorems/93b17a60-6d15-44d3-bace-b644bc5e7c27
-- title:
--   The fake curvature $\widetilde F_{\mu\nu}=F_{\mu\nu}+\tau(B_{\mu\nu})$ of the 2-connection $(A,B)$
-- statement:
--   Let $t:H\to G$ be a map of real Lie groups with $\tau=dt_1$, let $A_\mu$ be the connection 1-form of a family of edge labels with curvature $F_{\mu\nu}$, and let $B_{\mu\nu}$ be the connection 2-form of a family of square labels. The **fake curvature** of the 2-connection $(A,B)$ is
--   $$\widetilde F_{\mu\nu}(x)=F_{\mu\nu}(x)+\tau\big(B_{\mu\nu}(x)\big)=\partial_\mu A_\nu-\partial_\nu A_\mu+[A_\mu,A_\nu]+\tau(B_{\mu\nu}).$$
--
--   It is the curvature 2-form that the paper reads off the generalized holonomy of an infinitesimal square.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.3, Eq. (3.23), p. 16

import Mathlib
import Definitions.Def_GPHigherGauge_Flatness_connectionTwoForm
import Definitions.Def_GPHigherGauge_Flatness_tau
import Definitions.Def_GPHigherGauge_Flatness_curvature

open scoped Manifold ContDiff

namespace GPHigherGauge.Flatness

/-- The fake curvature `F̃_μν = F_μν + τ(B_μν)` of the 2-connection `(A, B)`.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.3, Eq. (3.23), p. 16:
"F̃_µν = ∂_µA_ν − ∂_νA_µ + [A_µ, A_ν] + τ(B_µν) = F_µν + τ(B_µν)".

**Formalization Note** `F_μν` is `curvature`, `B_μν` is `connectionTwoForm`, `τ` is `tau`. -/
noncomputable def fakeCurvature {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] [ChartedSpace F H] [Group H] {n : ℕ} (t : H → G)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ → G)
    (h : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ → H) (μ ν : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : GroupLieAlgebra 𝓘(ℝ, E) G :=
  curvature (E := E) g μ ν x + tau (E := E) (F := F) t (connectionTwoForm (F := F) h μ ν x)

end GPHigherGauge.Flatness


