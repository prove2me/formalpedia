-- Prove2me | Definitions.Def_RockafellianRelax_conj
-- name    : RockafellianRelax_conj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:08.083892+00:00
-- url     : https://prove2.me/theorems/c7b771cf-8544-4436-90a6-43222b605fa8
-- title:
--   Conjugate $\psi^*$ of $\psi : \mathbb R^k \to \overline{\mathbb R}$
-- statement:
--   For $\psi : \mathbb R^k \to \overline{\mathbb R}$, the **conjugate** $\psi^* : \mathbb R^k \to \overline{\mathbb R}$ is
--
--   $$
--   \psi^*(y) = \sup_{x \in \mathbb R^k} \bigl\{\langle x, y\rangle - \psi(x)\bigr\}.
--   $$
--
--   Since $\langle x, y\rangle$ is finite, the term is $-\infty$ where $\psi(x) = +\infty$ and $+\infty$ where $\psi(x) = -\infty$; no $\infty - \infty$ occurs. The paper applies it to the min-value function, $\mathcal V^*$, to characterize exactness.
--
--   **Formalization Note** $\mathbb R^k$ is `Fin k → ℝ`, $\langle x, y\rangle$ is `x ⬝ᵥ y`, and the supremum is taken in `EReal`.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §3, p.7 ("The conjugate ψ∗ … is given by ψ∗(y) = sup_x⟨x, y⟩ − ψ(x)")

import Mathlib

namespace RockafellianRelax

/-- **Conjugate** `ψ*(y) = sup_x ⟨x, y⟩ − ψ(x)` of `ψ : ℝᵏ → R̄`.
Royset, Chen & Eckstrand, arXiv:2204.04762v4, §3, p.7: "The conjugate ψ* : ℝⁿ → R̄ of ψ is given by
ψ*(y) = sup_x⟨x, y⟩ − ψ(x)".

**Formalization Note.** `ℝᵏ` is `Fin k → ℝ` and `⟨x, y⟩` is `x ⬝ᵥ y`. The supremum is taken in the
complete lattice `EReal`. The minuend `⟨x, y⟩` is a real number, so `⟨x, y⟩ − ψ(x)` is `−∞` when
`ψ(x) = +∞` and `+∞` when `ψ(x) = −∞`, as in the paper's extended arithmetic (footnote 1, p.4);
no `∞ − ∞` occurs. -/
noncomputable def conj {k : ℕ} (ψ : (Fin k → ℝ) → EReal) (y : Fin k → ℝ) : EReal :=
  ⨆ x : Fin k → ℝ, ((x ⬝ᵥ y : ℝ) : EReal) - ψ x

end RockafellianRelax


