-- Prove2me | Definitions.Def_SphereSOS_Rate_Level
-- name    : SphereSOS_Rate_Level
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:55.573981+00:00
-- url     : https://prove2.me/theorems/123e7bc6-d546-47e9-a2ce-bbd44746c53b
-- title:
--   §1.1, (1) — $p_{\max}$, $p_{\min}$ on $S^{d-1}$ and the sum-of-squares bound $p_\ell$
-- statement:
--   For a real polynomial $p$ in $d$ variables,
--   $$p_{\max}=\max_{x\in S^{d-1}}p(x),\qquad p_{\min}=\min_{x\in S^{d-1}}p(x),$$
--   and the **level-$\ell$ sum-of-squares bound** is
--   $$p_\ell=\min\big\{\gamma\in\mathbb R:\ \gamma-p\ \text{is sum-of-squares of degree }\ell\text{ on }S^{d-1}\big\},$$
--   where "sum-of-squares of degree $\ell$ on $S^{d-1}$" means $\ell$-sos on $S^{d-1}$ for the $1\times1$ matrix polynomial $\gamma-p$: on the sphere $\gamma-p=\sum_ju_j^2$ with $\deg u_j\le\ell$. Each $p_\ell$ is an upper bound on $p_{\max}$, computable by a semidefinite program.
--
--   **Formalization Note** $p_{\max}$ and $p_{\min}$ are real `sSup`/`sInf`. For $d\ge1$ the sphere is nonempty and compact, so both are attained. The level value uses `WithTop ℝ`: an infeasible SOS constraint has value $+\infty$, rather than Lean's real `sInf ∅ = 0`. At the levels covered by Theorem 1, the theorem asserts a finite, attained value. For $d=0$ all three quantities use the harmless value $0$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 2, (1) and the definition of p_ℓ in §1.1; p_min in Theorem 1

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting

namespace SphereSOS.Rate

/-- `p_max`, the maximum of `p` on `S^{d-1}` (1). -/
noncomputable def pmax (d : ℕ) (p : MvPolynomial (Fin d) ℝ) : ℝ :=
  sSup ((fun x => MvPolynomial.eval x p) '' sphere d)

/-- `p_min`, the minimum of `p` on `S^{d-1}`. -/
noncomputable def pmin (d : ℕ) (p : MvPolynomial (Fin d) ℝ) : ℝ :=
  sInf ((fun x => MvPolynomial.eval x p) '' sphere d)

/-- The level-`ℓ` sum-of-squares bound `p_ℓ` of §1.1, with `γ - p` read as a `1 × 1`
matrix polynomial. An infeasible level has value `⊤`, rather than the real `sInf ∅ = 0`.
For the empty zero-dimensional sphere we use the value zero, as in `pmax` and `pmin`. -/
noncomputable def pLevel (d ℓ : ℕ) (p : MvPolynomial (Fin d) ℝ) : WithTop ℝ :=
  if d = 0 then 0 else
    sInf ((fun γ : ℝ => (γ : WithTop ℝ)) ''
      {γ : ℝ | IsSosOnSphere ℓ (Matrix.of fun _ _ : Fin 1 => MvPolynomial.C γ - p)})

end SphereSOS.Rate


