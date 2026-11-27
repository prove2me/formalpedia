-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_supportApprox
-- name    : RockafellianRelax_Supplement_supportApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:14:22.732189+00:00
-- url     : https://prove2.me/theorems/073b520e-3ddd-516b-a60d-8c5d2c915d6e
-- title:
--   Approximating function (4.10) under support uncertainty
-- statement:
--   Let $f_0 : \mathbb R^n \to \overline{\mathbb R}$, $g : \mathbb R^m\times\mathbb R^n \to \overline{\mathbb R}$, $p^\nu \in \mathbb R^s$, $\xi^\nu_i \in \mathbb R^m$, $\theta^\nu,\lambda^\nu \in \mathbb R$, and let $\Delta$ be the probability simplex. The **approximating function** (4.10) is, for $p^\nu + u \in \Delta$,
--
--   $$
--   f^\nu((u,v),x) = f_0(x) + \sum_{i=1}^s (p^\nu_i+u_i)\, g(\xi^\nu_i+v_i,x) + \tfrac12\theta^\nu\|u\|_2^2 + \tfrac12\lambda^\nu\|v\|_2^2,
--   $$
--
--   and $+\infty$ otherwise.
--
--   Theorem 4.5 shows that these functions epi-converge to the Rockafellian (4.9).
--
--   **Formalization Note** $(u,v)$ is the split of one vector in $\mathbb R^{s+sm}$, and $\|v\|_2^2$ sums the squares of all $sm$ coordinates. The support perturbation $v$ is unconstrained.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, display (4.10), p.16

import Mathlib
import Definitions.Def_RockafellianRelax_Supplement_euclidNorm
import Definitions.Def_RockafellianRelax_Supplement_expObjective
import Definitions.Def_RockafellianRelax_Supplement_splitPerturbation

namespace RockafellianRelax.Supplement

open Classical in
/-- **Approximating function (4.10).** Royset, Chen & Eckstrand, arXiv:2204.04762v4, (4.10), p.16: "fν((u, v), x) = f₀(x) + ∑_{i=1}^s
(pν_i + u_i) g(ξν_i + v_i, x) + ½θν‖u‖₂² + ½λν‖v‖₂² + ι_∆(pν + u)".

**Formalization Note.** `q, ξ, θ, lam` stand for `pν, ξν, θν, λν`. `(u, v) = splitPerturbation w`,
and `‖v‖₂²` is the sum of squares of all `sm` coordinates. The function is the formula on
`q + u ∈ ∆ = stdSimplex ℝ (Fin s)` and `⊤` elsewhere; `v` is unconstrained. -/
noncomputable def supportApprox {m n s : ℕ} (f0 : (Fin n → ℝ) → EReal)
    (g : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (q : Fin s → ℝ) (ξ : Fin s → Fin m → ℝ) (θ lam : ℝ) :
    (Fin (s + s * m) → ℝ) × (Fin n → ℝ) → EReal :=
  fun z =>
    let u := (splitPerturbation z.1).1
    let v := (splitPerturbation z.1).2
    if q + u ∈ stdSimplex ℝ (Fin s) then
      expObjective f0 (fun i x => g (ξ i + v i, x)) (q + u) z.2 +
        ((1 / 2 * θ * euclidNorm u ^ 2 + 1 / 2 * lam * ∑ i, ∑ j, v i j ^ 2 : ℝ) : EReal)
    else ⊤

end RockafellianRelax.Supplement


