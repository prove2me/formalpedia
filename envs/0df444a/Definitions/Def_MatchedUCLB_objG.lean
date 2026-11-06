-- Prove2me | Definitions.Def_MatchedUCLB_objG
-- name    : MatchedUCLB_objG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:06.744965+00:00
-- url     : https://prove2.me/theorems/7f4646d4-8960-4d30-9245-ee83a157d24f
-- title:
--   The base increment norms $G_j=\mu R_j^{q-1}$
-- statement:
--   With $R_j=\|h_j\|$, the **base increment norms** are $G_j=\mu R_j^{q-1}$. By Definition E.1 (and Lemma 4.3(b)) they are the norms of the base gradient increments $b_j=\nabla B(c_{j+1})-\nabla B(c_j)=\mu R_j^{q-2}h_j$.
--
--   **Formalization Note** The complete objective depends on $q=p+\nu$, $\mu$, the chain length $m$, the number of phases $L$, the initial scale $\tau_0$ and a phase frame $(v,u)$; the constants $K$ and $\eta$ are fixed as in Lemma 4.5. Phase directions are sequences indexed by $j\in\mathbb N$, of which only $j<L$ enter. $G_j$ is defined by the closed formula.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Definition E.1, p.83

import Mathlib
import Definitions.Def_MatchedUCLB_objH

namespace MatchedUCLB

/-- **The base increment norms `G_j = μR_j^{q−1}`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Definition E.1, p.83:
"`b_j := ∇B(c_{j+1}) − ∇B(c_j) = μR_j^{q−2} h_j`, `G_j := ‖b_j‖ = μR_j^{q−1}`", `R_j = ‖h_j‖`.

**Formalization Note.** `G_j` is defined by the closed formula of Definition E.1 (the identity
`∇B(c_{j+1}) − ∇B(c_j) = μR_j^{q−2}h_j` is Lemma 4.3(b)).

**Formalization Note.** The parameters of the complete objective are `q = p + ν`, `μ`, the chain
length `m`, the number of phases `L`, the initial scale `τ₀` and a phase frame `(v, u)`; `K` and
`η` are fixed as in Lemma 4.5 (`KConst q`, `eta q`). -/
noncomputable def objG (q μ : ℝ) {d m : ℕ} (τ₀ : ℝ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)) (j : ℕ) : ℝ :=
  μ * ‖objH q τ₀ v u j‖ ^ (q - 1)

end MatchedUCLB


