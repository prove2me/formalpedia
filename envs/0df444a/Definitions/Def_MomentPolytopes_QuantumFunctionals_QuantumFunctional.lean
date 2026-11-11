-- Prove2me | Definitions.Def_MomentPolytopes_QuantumFunctionals_QuantumFunctional
-- name    : MomentPolytopes_QuantumFunctionals_QuantumFunctional
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:04:31.891399+00:00
-- url     : https://prove2.me/theorems/5e92286d-d348-4548-98ee-b4e97f326653
-- title:
--   The objective ϕ_θ and the logarithmic quantum functional E_θ
-- statement:
--   Let $\theta$ be a probability distribution on $[d]$ (zero weights allowed). The convex objective $\phi_\theta:\mathbb R^{n_1}\times\dots\times\mathbb R^{n_d}\to\mathbb R\cup\{\infty\}$ is
--   $$\phi_\theta(p_1,\dots,p_d)=\begin{cases}-\sum_{\ell\in[d]}\theta_\ell H(p_\ell)&\text{if all }p_\ell\ge0,\\ \infty&\text{otherwise,}\end{cases}$$
--   with $H$ the Shannon entropy (natural log, $0\log0=0$).
--
--   For a tensor tuple $T\ne0$, the **logarithmic quantum functional** is
--   $$E_\theta(T)=\max_{p\in\Delta(T)}\sum_{\ell=1}^d\theta_\ell H(p_\ell)=-\min_{p\in\Delta(T)}\phi_\theta(p).$$
--
--   **Formalization Note** $\phi_\theta$ is valued in `EReal` with $+\infty=\top$. $E_\theta(T)$ is the real `sSup` of $\sum_\ell\theta_\ell H(p_\ell)$ over $\Delta(T)$; for $T\ne0$ this set is nonempty and compact and the function is continuous, so the supremum is the maximum. It is never defined through an algorithm.
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 54, eq. (7.4) and Definition 7.3

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope

set_option autoImplicit false

namespace MomentPolytopes.QuantumFunctionals

variable {d n0 : ℕ} {n : Fin d → ℕ}

/-- `θ` is a probability distribution on `[d]` (zero weights allowed). -/
def IsProbVec (θ : Fin d → ℝ) : Prop :=
  (∀ ℓ, 0 ≤ θ ℓ) ∧ ∑ ℓ, θ ℓ = 1

/-- The convex objective of eq. (7.4), p. 54, valued in `ℝ ∪ {∞}` (encoded in `EReal`):
`ϕ_θ(p_1, …, p_d) = -∑_ℓ θ_ℓ H(p_ℓ)` if all `p_ℓ ≥ 0`, and `+∞` otherwise. -/
noncomputable def phiTheta (θ : Fin d → ℝ) (p : SpecTuple n) : EReal :=
  if ∀ ℓ i, 0 ≤ p ℓ i then (((-∑ ℓ, θ ℓ * shannonEntropy (p ℓ)) : ℝ) : EReal) else ⊤

/-- The logarithmic quantum functional (Definition 7.3, p. 54):
`E_θ(T) = max_{p ∈ Δ(T)} ∑_ℓ θ_ℓ H(p_ℓ)` for `T ≠ 0`. The maximum is the supremum of the
image of the compact, nonempty set `Δ(T)` (for `T ≠ 0`) under a continuous function, so the
real `sSup` is attained. -/
noncomputable def logQuantumFunctional (θ : Fin d → ℝ) (T : Ten d n0 n) : ℝ :=
  sSup ((fun p : SpecTuple n => ∑ ℓ, θ ℓ * shannonEntropy (p ℓ)) '' entanglementPolytope T)

end MomentPolytopes.QuantumFunctionals


