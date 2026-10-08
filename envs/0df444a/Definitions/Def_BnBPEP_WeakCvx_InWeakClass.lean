-- Prove2me | Definitions.Def_BnBPEP_WeakCvx_InWeakClass
-- name    : BnBPEP_WeakCvx_InWeakClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:37.370038+00:00
-- url     : https://prove2.me/theorems/a93d32bc-37d2-476b-877a-f957db8e410c
-- title:
--   The class $\mathcal W_{\rho,L}$ of $\rho$-weakly convex functions with $L$-bounded subgradients
-- statement:
--   Let $\rho, L\in\mathbb R$. A function $f:\mathbb R^d\to\mathbb R$ belongs to the class $\mathcal W_{\rho,L}$ when
--
--   1. $f$ is **$\rho$-weakly convex**: the function $x\mapsto f(x)+\frac{\rho}{2}\|x\|^2$ is convex on $\mathbb R^d$; and
--   2. $f$ has **$L$-bounded subgradients**: $\|g\|\le L$ for every $x\in\mathbb R^d$ and every $g\in\partial f(x)$, where $\partial f(x)$ is the set of vectors $g$ with
--   $$f(y)\ \ge\ f(x)+\langle g,y-x\rangle-\frac{\rho}{2}\|y-x\|^2\quad\forall y\in\mathbb R^d.$$
--
--   This is the function class of Table 1 of Das Gupta, Van Parys and Ryu (with $\rho>0$, $L>0$), on which their subgradient-method analysis of §6.3 is carried out. Since $f\in\mathcal W_{\rho,L}$ if and only if $f/\rho\in\mathcal W_{1,L/\rho}$, the paper normalizes $\rho=1$ and writes the bound as $\widetilde L=L/\rho$; the theorems of this mission work in $\mathcal W_{1,L}$, so their $L$ is the paper's $\widetilde L$.
--
--   **Formalization Note** The parameter conditions $\rho>0$, $L>0$ of Table 1 are not part of the predicate; theorems state $0<L$ where they use the class (always with $\rho=1$). App. 8.1 prints the bound as $\|u\|^2\le L$, a typo for the definition $\|u\|\le L$ on p. 572, which is what is formalized. The class is nonempty: $f=0$ and $f(x)=L\|x\|$ belong to $\mathcal W_{1,L}$.
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), p. 572 (§2, ρ-weakly convex, L-bounded subgradients), p. 573 (Table 1, W_{ρ,L}), p. 613 (normalization ρ = 1, L̃ = L/ρ), p. 629 (App. 8.1)

import Mathlib
import Definitions.Def_BnBPEP_WeakCvx_IsWeakSubgrad

namespace BnBPEP.WeakCvx

/-- The class `W_{ρ,L}` of `ρ`-weakly convex functions with `L`-bounded subgradients
(Das Gupta–Van Parys–Ryu, Math. Program. 204 (2024), p. 572 and Table 1, p. 573):
`f + (ρ/2)‖·‖²` is convex on `ℝ^d`, and every subgradient `g ∈ ∂f(x)` (in the sense of
`IsWeakSubgrad ρ`) satisfies `‖g‖ ≤ L`. The paper takes `ρ > 0`, `L > 0`; theorems state
these where they use them. -/
def InWeakClass {d : ℕ} (ρ L : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ConvexOn ℝ Set.univ (fun x => f x + ρ / 2 * ‖x‖ ^ 2) ∧
    ∀ x g : EuclideanSpace ℝ (Fin d), IsWeakSubgrad ρ f x g → ‖g‖ ≤ L

end BnBPEP.WeakCvx


