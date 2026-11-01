-- Prove2me | Definitions.Def_GibbsCongestion_dirichletForm
-- name    : GibbsCongestion_dirichletForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:23.642988+00:00
-- url     : https://prove2.me/theorems/718c596d-202c-43dd-9798-46b49c8314b5
-- title:
--   Dirichlet form $\mathcal E_P(f,g)$
-- statement:
--   For a Markov chain with transition matrix $P$ on a finite set $\Omega$ and a distribution $\pi$, the **Dirichlet form** of $f,g:\Omega\to\mathbb R$ is
--   $$\mathcal E_P(f,g)=\frac12\sum_{x\in\Omega}\sum_{y\in\Omega}\pi(x)P(x,y)\,[f(x)-f(y)]\,[g(x)-g(y)].$$
--   It is the numerator of the modified log-Sobolev ratio $\mathcal E_P(f,\log f)/\mathrm{Ent}_\pi(f)$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, App. A, p.25

import Mathlib

namespace GibbsCongestion

/-- The **Dirichlet form**
`E_P(f, g) = (1/2) ∑_x ∑_y π(x) P(x,y) [f(x) − f(y)] [g(x) − g(y)]` of a chain `P` with
distribution `π` (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, App. A, p.25). -/
noncomputable def dirichletForm {Ω : Type*} [Fintype Ω] (P : Matrix Ω Ω ℝ) (π : Ω → ℝ) (f g : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, π x * P x y * (f x - f y) * (g x - g y)

end GibbsCongestion


