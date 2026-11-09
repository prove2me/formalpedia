-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_RandomizedOnline
-- name    : OnlinePerceptronIsolation_Binary_RandomizedOnline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:18.835367+00:00
-- url     : https://prove2.me/theorems/e494641c-0df6-4d1f-89f6-00f0ea940791
-- title:
--   Measurable online algorithms with arbitrary independent seeds
-- statement:
--   Let $(\Xi,\nu)$ be any seed probability space. A randomized online algorithm is a family $A(\xi)$ of deterministic online signing maps whose coordinate outputs are jointly measurable in the seed $\xi$ and matrix $G$. Every seed section satisfies the referenced nonanticipation condition: sign $i$ depends only on columns through $i$. Its success probability is
--   $$\mathbb P_{(\xi,G)\sim\nu\otimes\mathcal G^{m,n}}\bigl(A(\xi,G)\in S^h(G,\kappa)\bigr).$$
--   The product law enforces independence of the seed and instance. Seeds can have arbitrary laws, and the maps have unrestricted memory and running time. Past signs can be reconstructed from the observed columns and seed. Fixing a margin outside the map's binders restricts no algorithm at that margin. This representation supports dimension-dependent families and exact averaging over all randomness.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 2.3, Eq. (2.4), printed p.6, PDF p.8; footnote 4, printed p.3, PDF p.5; Eqs. (A.60)-(A.61), printed p.24, PDF p.26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Isolation
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Definition 2.3 and footnote 4: arbitrary jointly measurable seed-indexed online maps.
The independent seed law is supplied separately; no seed support or computational restriction. -/
def IsRandomizedOnline {Ξ : Type*} [MeasurableSpace Ξ] {m n : ℕ}
    (A : Ξ → Fin n → (Fin m × Fin n → ℝ) → ℝ) : Prop :=
  (∀ i, Measurable (fun p : Ξ × (Fin m × Fin n → ℝ) => A p.1 i p.2)) ∧
    ∀ ξ, ABPOnline.IsOnlineAlg m n (A ξ)

/-- Success averaged over the independent seed and Gaussian matrix, not a selected seed. -/
noncomputable def randomSuccess {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ)
    {m n : ℕ} (A : Ξ → Fin n → (Fin m × Fin n → ℝ) → ℝ) (κ h : ℝ) : ℝ :=
  (ν.prod (ABPOnline.gaussMat m n)).real
    {p | IsIsolated p.2 κ h (fun i => A p.1 i p.2)}

end OnlinePerceptronIsolation.Binary


