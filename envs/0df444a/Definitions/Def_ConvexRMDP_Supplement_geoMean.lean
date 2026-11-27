-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_geoMean
-- name    : ConvexRMDP_Supplement_geoMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:51:41.964796+00:00
-- url     : https://prove2.me/theorems/f0d920e4-2218-5fbb-9eaa-2f5c9a6e2e51
-- title:
--   The map $f(p)=\prod_{s'}x_{s'}^{\gamma p_{s'}}$ of (5.4)
-- statement:
--   Fix $\gamma \in (0,1)$ and $x \in [1,+\infty)^{\mathcal S}$. The map $f : \mathbb R^{\mathcal S} \to \mathbb R$ of (5.4) is
--
--   $$
--   f(p) = \prod_{s' \in \mathcal S} x_{s'}^{\gamma p_{s'}} .
--   $$
--
--   Minimizing $f$ over the uncertainty set $\mathcal U_{sa}$ is the inner problem (5.2) in the constraints of the convex program (4.7); its conjugate is computed in Proposition 5.2.
--
--   **Formalization Note** The paper writes $f : \Delta(\mathcal S) \to \mathbb R$, but its conjugate in Proposition 5.2 and in Appendix D ("$f(p) = 1$, $\forall p \in \mathbb R^{\mathcal S}$") is a supremum over all of $\mathbb R^{\mathcal S}$, so $f$ is defined on all of $\mathbb R^{\mathcal S}$. The power is the real power, used only with positive bases.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, §5.1, display (5.4), p.16; App. D, p.30

import Mathlib

namespace ConvexRMDP

namespace Supplement

/-- **The map `f` of (5.4)** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.16):
for a fixed `x ∈ [1,+∞)^S`, `f(p) = ∏_{s' ∈ S} x_{s'}^{γ p_{s'}}`.

**Formalization Note.** The paper writes `f : Δ(S) → ℝ`, but its conjugate (Proposition 5.2, proved in
App. D, p.30: "`f(p) = 1, ∀ p ∈ ℝ^S`") is the supremum over all `p ∈ ℝ^S`, so `f` is defined on all of
`S → ℝ`. `γ` is the discount factor. The power is `Real.rpow`, the paper's power for the positive
bases `x_{s'} ≥ 1` on which `f` is used. -/
noncomputable def geoMean {S : Type*} [Fintype S] (γ : ℝ) (x p : S → ℝ) : ℝ :=
  ∏ s', x s' ^ (γ * p s')

end Supplement

end ConvexRMDP


