-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_Supplement_Conditioning
-- name    : MultiSpinCounting_Positive_Supplement_Conditioning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:22:53.698068+00:00
-- url     : https://prove2.me/theorems/dd0bc1e5-bf15-4919-9cbd-9dd4fb5c35b9
-- title:
--   Conditional Gibbs marginals and distance to boundary discrepancies
-- statement:
--   Let $\Phi=(G,[q],A,\lambda)$ be a positive real spin instance on $n$ vertices, with all vertices active. Write $w_\Phi(x)$ for its published full-graph weight (1.1). For a boundary set $\Lambda$ and an assignment $\sigma$ on it, define
--   $$\mu_\Phi(v\leftarrow a\mid\Lambda\leftarrow\sigma)=\frac{\sum_{x:x|_\Lambda=\sigma,\ x_v=a}w_\Phi(x)}{\sum_{x:x|_\Lambda=\sigma}w_\Phi(x)}.$$
--   Every edge and every field stays in the weight, including edges incident to or inside the boundary. Positive data and a nonempty palette make every conditioning denominator positive.
--   For two boundary assignments define $\Delta=\{u\in\Lambda:\sigma_u\ne\tau_u\}$ and
--   $$r=\inf_{u\in\Delta}\operatorname{dist}_G(v,u)\in\mathbb N\cup\{\infty\}.$$
--   Distance is in the whole graph. Empty discrepancy and unreachable discrepancies give infinity. These definitions supply the exact conditional quantities in Theorem 1.2.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 3–4, Definition 1.1; Theorem 1.2

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Instance

noncomputable section

namespace MultiSpinCounting.Positive.Supplement

/-- The full-graph weight, using the published active-carrier weight.
Every theorem using conditioning has active = univ. -/
def fullWeight {n q : ℕ} (Φ : Instance n q ℝ) (x : Fin n → Fin q) : ℝ :=
  weight Φ (fun u => x u.val)

/-- Genuine conditioning: all original fields and edge interactions remain. -/
def condMarginal {n q : ℕ} (Φ : Instance n q ℝ) (Λ : Finset (Fin n))
    (σ : Fin n → Fin q) (v : Fin n) (a : Fin q) : ℝ := by
  classical
  exact (∑ x : Fin n → Fin q,
    if (∀ u ∈ Λ, x u = σ u) ∧ x v = a then fullWeight Φ x else 0) /
    (∑ x : Fin n → Fin q,
      if ∀ u ∈ Λ, x u = σ u then fullWeight Φ x else 0)

/-- Definition 1.1: distance in the whole graph, with ∞ for empty/unreachable discrepancy. -/
def discrepancyDist {n q : ℕ} (G : SimpleGraph (Fin n)) (Λ : Finset (Fin n))
    (σ τ : Fin n → Fin q) (v : Fin n) : ℕ∞ :=
  ⨅ u : {u // u ∈ Λ ∧ σ u ≠ τ u}, G.edist v u.val

end MultiSpinCounting.Positive.Supplement


