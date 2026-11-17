-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_prodQMCVal
-- name    : HeilmanMax3Cut_Supplement_prodQMCVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:03:15.143189+00:00
-- url     : https://prove2.me/theorems/4b834fdf-282b-4d55-ab03-ec41d5126d37
-- title:
--   The product-state Quantum MAX-CUT value
-- statement:
--   For a weighted graph with weights $w$, the product-state Quantum MAX-CUT value is
--
--   $$\max_{\substack{u=u_1\otimes\cdots\otimes u_n\\ u_i\in\mathbb C^2,\ \|u_i\|\le1}} u^*\Big(\sum_{i,j=1}^n w_{ij}\big(I_2^{\otimes n}-X_iX_j-Y_iY_j-Z_iZ_j\big)\Big)u .$$
--
--   It restricts the Quantum MAX-CUT problem to product states; the Briët–Oliveira–Vallentin algorithm approximates it within $\alpha_{\mathrm{BOV}}$.
--
--   **Formalization Note** $u_i$ ranges over the closed unit ball of $\mathbb C^2$ with the Euclidean norm; $u_1\otimes\cdots\otimes u_n$ is $b\mapsto\prod_iu_i(b_i)$; the real part of $u^*Hu$ is taken ($H$ is Hermitian). The maximum is a supremum of a continuous function on a compact set.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 2.1, p.10

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_HeilmanMax3Cut_Supplement_qmcHam
open OptInapprox.MaxCut Matrix

namespace HeilmanMax3Cut.Supplement

/-- **The product-state Quantum MAX-CUT value.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 2.1, p.10: "The product state of
Quantum MAX-CUT is the more restricted optimization problem of computing
`max_{u = u₁ ⊗ ⋯ ⊗ u_n : uᵢ ∈ ℂ², ‖uᵢ‖ ≤ 1, ∀ 1 ≤ i ≤ n} u* (∑_{i,j=1}^n w_{ij} (I₂^{⊗n} − X_iX_j − Y_iY_j − Z_iZ_j)) u`."

**Formalization Note.** `uᵢ ∈ EuclideanSpace ℂ (Fin 2)` (so `‖uᵢ‖` is the Euclidean norm of `ℂ²`),
and `u₁ ⊗ ⋯ ⊗ u_n` is the vector `b ↦ ∏ᵢ uᵢ(bᵢ)` on bit strings `b : Fin n → Fin 2`. The operator
(`qmcHam`) is Hermitian, so `u* H u` is real; its real part is taken. The maximum is the real `sSup`
of the image of the compact set `{u : ∀ i, ‖uᵢ‖ ≤ 1}` under a continuous map, so it is attained and
the set is bounded and nonempty. -/
noncomputable def prodQMCVal (G : WMaxCut) : ℝ :=
  sSup ((fun u : Fin G.n → EuclideanSpace ℂ (Fin 2) =>
      (star (fun b : Fin G.n → Fin 2 => ∏ i, u i (b i)) ⬝ᵥ
        (qmcHam G *ᵥ fun b : Fin G.n → Fin 2 => ∏ i, u i (b i))).re) ''
    {u | ∀ i, ‖u i‖ ≤ 1})

end HeilmanMax3Cut.Supplement


