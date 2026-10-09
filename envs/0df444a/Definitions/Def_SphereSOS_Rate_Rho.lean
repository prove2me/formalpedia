-- Prove2me | Definitions.Def_SphereSOS_Rate_Rho
-- name    : SphereSOS_Rate_Rho
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:19.223052+00:00
-- url     : https://prove2.me/theorems/2028b965-d1c9-4e36-983c-660b80b96ba7
-- title:
--   (10), (13), (16) — the kernel error $\rho_{2n}(d,\ell)$ and its linear proxy $\tilde\rho_{2n}(d,\ell)$
-- statement:
--   Fix $d\ge2$, $n\ge0$, $\ell\ge0$. For a univariate polynomial $q$ write $\lambda_i=\lambda_i(q^2)$ for the Gegenbauer coefficients of $\phi=q^2$.
--
--   1. The **kernel error** is
--   $$\rho_{2n}(d,\ell)=\min_{\substack{q\in\mathbb R[t],\ \deg q\le\ell\\ \lambda_0=1}}\ \sum_{k=1}^n\big|\lambda_{2k}^{-1}-1\big|\ \in[0,\infty],$$
--   where a term with $\lambda_{2k}=0$ counts as $+\infty$.
--   2. The **linear proxy** of (16) is
--   $$\tilde\rho_{2n}(d,\ell)=\min_{\substack{e\in\mathbb R^{\ell+1}\\ \sum_ie_i^2=1}}\ \sum_{k=1}^n\Big(1-e^{\mathsf T}\,\mathcal T\big[C_{2k}/C_{2k}(1)\big]\,e\Big).$$
--
--   $\rho_{2n}(d,\ell)$ measures how close the Gegenbauer coefficients of the best square kernel $q(\langle x,y\rangle)^2$ of degree $2\ell$ can be brought to those of the identity; Theorem 6 turns it into the additive error of the level-$\ell$ certificate.
--
--   **Formalization Note** Three conventions. (i) The sum runs over $k=1,\dots,n$, as in (12), (13) and (16); display (10) prints the upper limit $2n$, a slip. (ii) The minimum is over $\deg q\le\ell$, the range of the paper's own reformulation (13) ($q=\sum_{i\le\ell}e_iC_i/\sqrt{C_i(1)}$); (10) says $\deg q=\ell$, which gives the same infimum. (iii) $\rho_{2n}$ is an infimum in $[0,\infty]$: $|\lambda^{-1}-1|$ is $+\infty$ at $\lambda=0$ (not Lean's $0^{-1}=0$), and an empty feasible set gives $+\infty$. $\tilde\rho_{2n}$ is a real infimum over a nonempty set that is bounded below (each term is nonnegative since $|C_{2k}(t)|\le C_{2k}(1)$ on $[-1,1]$).
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, pp. 6, 8, 9, (10), (13), (16)

import Mathlib
import Definitions.Def_SphereSOS_Rate_Toeplitz

namespace SphereSOS.Rate

/-- `|λ⁻¹ - 1|` in `[0, ∞]`, with the value `∞` at `λ = 0`. -/
noncomputable def invDist (lam : ℝ) : ENNReal :=
  if lam = 0 then ⊤ else ENNReal.ofReal |lam⁻¹ - 1|

/-- The quantity `ρ_{2n}(d, ℓ)` of (10)/(13): the infimum, over univariate `q` of degree at most
`ℓ` with `λ_0(q^2) = 1`, of `∑_{k=1}^n |λ_{2k}(q^2)⁻¹ - 1|`, valued in `[0, ∞]`. -/
noncomputable def rho (d n ℓ : ℕ) : ENNReal :=
  ⨅ (q : Polynomial ℝ) (_ : q.natDegree ≤ ℓ) (_ : gegCoeff d (q ^ 2) 0 = 1),
    ∑ k ∈ Finset.Icc 1 n, invDist (gegCoeff d (q ^ 2) (2 * k))

/-- The proxy `ρ̃_{2n}(d, ℓ)` of (16): the minimum over unit vectors `e ∈ ℝ^{ℓ+1}` of
`∑_{k=1}^n (1 - eᵀ T[C_{2k}/C_{2k}(1)] e)`. -/
noncomputable def rhoTilde (d n ℓ : ℕ) : ℝ :=
  sInf {s : ℝ | ∃ e : Fin (ℓ + 1) → ℝ, (∑ i, e i ^ 2) = 1 ∧
    s = ∑ k ∈ Finset.Icc 1 n,
      (1 - dotProduct e (Matrix.mulVec (toep d ℓ (fun t => (geg d (2 * k)).eval t)) e))}

end SphereSOS.Rate


