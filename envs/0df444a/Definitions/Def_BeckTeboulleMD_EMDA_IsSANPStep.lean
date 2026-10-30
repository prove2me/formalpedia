-- Prove2me | Definitions.Def_BeckTeboulleMD_EMDA_IsSANPStep
-- name    : BeckTeboulleMD_EMDA_IsSANPStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:59:39.439982+00:00
-- url     : https://prove2.me/theorems/e6eb442d-3bae-422a-a9ed-44b4ff1f9ad9
-- title:
--   One step of SANP, (3.11)
-- statement:
--   Let $X$ be a subset of a real normed space $E$, $\psi:E\to\mathbb R$, $g$ a continuous linear functional on $E$ (the subgradient $f'(x^k)$), $t\in\mathbb R$ (the step $t_k$) and $x\in E$ (the iterate $x^k$). A point $x^+$ is a **SANP step** from $x$ if $x^+\in X$ and
--   $$
--   g(x^+)+\frac1t\,B_\psi(x^+,x)\;\le\;g(y)+\frac1t\,B_\psi(y,x)\qquad\text{for all }y\in X,
--   $$
--   that is, $x^+$ minimizes $y\mapsto\langle y,f'(x^k)\rangle+t_k^{-1}B_\psi(y,x^k)$ over $X$. The subgradient algorithm with nonlinear projections (SANP) starts from $x^1\in\operatorname{int}X$ and sets $x^{k+1}$ to this minimizer, with $t_k>0$.
--
--   SANP is the paper's reformulation of mirror descent as a subgradient method with a Bregman "projection"; the convergence analysis of §4 is carried out for it.
--
--   **Formalization Note** The paper writes $x^{k+1}=\operatorname{argmin}$; the predicate says $x^+$ is a minimizer. When $\psi$ is strongly convex on a convex $X$ and differentiable at $x$, the objective is strongly convex and the minimizer is unique. The condition $t>0$ is stated in the theorems, not in the predicate.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003) 167–175, doi:10.1016/s0167-6377(02)00231-6, §3, eq. (3.11), printed p. 170 (PDF p. 4)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_bregman

namespace BeckTeboulleMD.EMDA

/-- **One step of the subgradient algorithm with nonlinear projections (SANP), (3.11).**
Beck & Teboulle, *Mirror descent and nonlinear projected subgradient methods for convex
optimization*, Oper. Res. Lett. 31 (2003), §3, eq. (3.11), printed p. 170 (PDF p. 4):
"Subgradient algorithm with nonlinear projections (SANP): Given B_ψ as defined in (3.10) with ψ as
above, start with x¹ ∈ int X, and generate the sequence {x^k} via the iteration
x^{k+1} = argmin_{x∈X} { ⟨x, f′(x^k)⟩ + (1/t_k) B_ψ(x, x^k) }, t_k > 0."

`IsSANPStep X ψ g t x xnext` says that `xnext ∈ X` minimizes `y ↦ g y + t⁻¹ B_ψ(y, x)` over `X`,
where `g` is the subgradient `f′(x^k)` (as a functional), `t = t_k` and `x = x^k`.

**Formalization Note.** The paper writes `x^{k+1} = argmin`; this predicate says that `xnext` is
*a* minimizer. When `ψ` is strongly convex on a convex `X` and differentiable at `x`, the objective
is strongly convex on `X` and the minimizer, if it exists, is unique, so the predicate determines
`xnext`. The condition `t_k > 0` is not part of the predicate; theorems state it. -/
def IsSANPStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) (g : E →L[ℝ] ℝ) (t : ℝ) (x xnext : E) : Prop :=
  xnext ∈ X ∧ ∀ y ∈ X, g xnext + t⁻¹ * bregman ψ xnext x ≤ g y + t⁻¹ * bregman ψ y x

end BeckTeboulleMD.EMDA


