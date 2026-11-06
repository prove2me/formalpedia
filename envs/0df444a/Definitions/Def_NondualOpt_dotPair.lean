-- Prove2me | Definitions.Def_NondualOpt_dotPair
-- name    : NondualOpt_dotPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:40.147469+00:00
-- url     : https://prove2.me/theorems/c789d406-0909-451d-9d32-015ca86f4cb0
-- title:
--   The dot-product pairing on $\mathbb R^d$
-- statement:
--   The bilinear pairing $\langle g,u\rangle=\sum_{i=1}^d g_iu_i$ on $\mathbb R^d\times\mathbb R^d$. With $E=\mathbb R^d$ and $E^*$ identified with $\mathbb R^d$ it is the duality pairing of the paper, and it is the pairing of the $(p,q)$ case $(X,H)=(B_p^d,B_{q^*}^d)$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, §2, p.7

import Mathlib

namespace NondualOpt

/-- The dot product `⟨g, u⟩ = ∑ᵢ gᵢ uᵢ` on `ℝ^d`, as a bilinear pairing. With `E = ℝ^d` and `E∗`
identified with `ℝ^d`, this is the duality pairing of the paper.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, §2, p.7 ("one may take `E = ℝ^d`,
identify `E∗` with `ℝ^d`, and interpret `⟨g, u⟩` as the usual inner product"). -/
def dotPair (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun g u => dotProduct g u)
    (fun _ _ _ => add_dotProduct _ _ _) (fun _ _ _ => smul_dotProduct _ _ _)
    (fun _ _ _ => dotProduct_add _ _ _) (fun _ _ _ => dotProduct_smul _ _ _)

end NondualOpt


