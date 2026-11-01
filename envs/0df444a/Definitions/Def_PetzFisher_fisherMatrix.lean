-- Prove2me | Definitions.Def_PetzFisher_fisherMatrix
-- name    : PetzFisher_fisherMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:06.407978+00:00
-- url     : https://prove2.me/theorems/6b2789f3-f75f-4a1b-80da-fe19e2b9ebad
-- title:
--   Quantum Fisher information matrix $J(\theta)$ of a parametrized family
-- statement:
--   Let $\mathcal M=\{\rho(\theta):\theta\in G\}$, $G\subseteq\mathbb R^k$, be a differentiable family of invertible density matrices and $f$ a standard operator monotone function. The quantum Fisher information matrix of $\mathcal M$ at $\theta$ is the $k\times k$ matrix
--
--   $$
--   J(\theta)_{ij}:=\operatorname{Tr}L^f_i(\theta)\,\mathbb J^f_{\rho(\theta)}\big(L^f_j(\theta)\big)=\operatorname{Tr}\big(\mathbb J^f_{\rho(\theta)}\big)^{-1}\big(\partial_{\theta_i}\rho(\theta)\big)\,\partial_{\theta_j}\rho(\theta),\qquad 1\le i,j\le k. \tag{26}
--   $$
--
--   It depends on $f$: $f(x)=(x+1)/2$ gives the SLD Fisher information, $f(x)=(x-1)/\log x$ the Bogoliubov–Kubo–Mori one. Monotonicity of $J$ under quantum channels is the subject of Theorem 2.3.
--
--   **Formalization Note** The matrix is the right-hand form of (26), computed with the published monotone metric `metric f D A B`$=\operatorname{Re}\operatorname{Tr}\,(\mathbb J^f_D)^{-1}(A)\,B$. The real part loses nothing in the paper's setting: for symmetric $f$ ($xf(x^{-1})=f(x)$) and self-adjoint $A,B$ the trace is real (p.7, condition (11)), and the derivatives of a Hermitian family are self-adjoint. $J(\theta)$ is a real matrix indexed by $\{0,\dots,k-1\}$; it is meaningful when $\rho(\theta)$ is positive definite and $\rho$ is differentiable at $\theta$, which every statement assumes.
-- source:
--   Petz–Ghinea, Introduction to quantum Fisher information, arXiv:1008.2417v1, §2, eq. (26), pp.14–15

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P31
import Definitions.Def_PetzFisher_partialDeriv

namespace PetzFisher

/-- The quantum Fisher information matrix of a parametrized family `θ ↦ ρ(θ)` with respect to `f`
(Petz–Ghinea, *Introduction to quantum Fisher information*, arXiv:1008.2417v1, §2, eq. (26),
pp.14–15): "`J(θ)_{ij} := Tr L^f_i(θ) 𝕁^f_{ρ(θ)}(L_j(θ)) = Tr (𝕁^f_{ρ(θ)})^{-1}(∂_{θ_i}ρ(θ))(∂_{θ_j}ρ(θ))`
(1 ≤ i, j ≤ k) is the quantum Fisher information matrix (depending on the function `f`)."

**Formalization Note.** This is the right-hand form of (26):
`J(θ)_{ij} = Re Tr (𝕁^f_{ρ(θ)})^{-1}(∂_{θ_i} ρ(θ)) ∂_{θ_j} ρ(θ)`, computed with the published
`Bridge50.P31.metric f D A B = Re Tr (inverseMetric f D A * B)`. The real part loses nothing in the
setting of the paper: for a standard (symmetric, `x f(x^{-1}) = f(x)`) function `f` and self-adjoint
`A`, `B` the trace is real (p.7, condition (11)), and the derivatives of a Hermitian family are
self-adjoint. `J(θ)` is a real `k × k` matrix indexed by `Fin k`. The value is meaningful when
`ρ(θ)` is positive definite and `ρ` is differentiable at `θ`; every statement using it assumes both. -/
noncomputable def fisherMatrix {I : Type} [Fintype I] [DecidableEq I] {k : ℕ} (f : ℝ → ℝ)
    (ρ : (Fin k → ℝ) → Matrix I I ℂ) (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => QAlgorithms.Papers.Independent.Bridge50.P31.metric f (ρ θ) (partialDeriv ρ θ i)
    (partialDeriv ρ θ j)

end PetzFisher


