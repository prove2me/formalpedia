-- Prove2me | Definitions.Def_SteurerHDX_innerMu
-- name    : SteurerHDX_innerMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:54.877514+00:00
-- url     : https://prove2.me/theorems/6cee9109-41aa-4e64-80b3-a927aa908b2a
-- title:
--   The inner product $\langle f,g\rangle_\mu$
-- statement:
--   For $f,g:\iota\to\mathbb R$,
--   $$\langle f,g\rangle_\mu=\mathbb E_{x\sim\mu} f(x)g(x)=\sum_x \mu(x)f(x)g(x),$$
--   where $\mu$ is the stationary distribution of the walk. $P$ is self-adjoint for this inner product.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.1, p.3

import Mathlib
import Definitions.Def_SteurerHDX_statDist

namespace SteurerHDX

/-- **The inner product ⟨f, g⟩_μ.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.1, p.3:
"⟨f, g⟩_μ = E_{x∼μ} f(x)g(x)". -/
noncomputable def innerMu {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) (f g : ι → ℝ) : ℝ :=
  ∑ x, statDist W x * f x * g x

end SteurerHDX


