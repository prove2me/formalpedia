-- Prove2me | Definitions.Def_SphereSOS_Rate_Toeplitz
-- name    : SphereSOS_Rate_Toeplitz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:38.474124+00:00
-- url     : https://prove2.me/theorems/1e598238-7798-4a44-98ef-17a3946d84bb
-- title:
--   p. 8, p. 9 — the generalized Toeplitz matrices $\mathcal T[h]$, the largest eigenvalue, and $h=\frac1n\sum_k C_{2k}/C_{2k}(1)$
-- statement:
--   Fix $d\ge2$ and $\ell\ge0$, and use the notation of the Gegenbauer definitions ($C_i$, $P_i=C_i/C_i(1)$, normalized weight $\bar w$).
--
--   1. The polynomials $\sqrt{\omega_{d-1}/\omega_d}\;C_i/\sqrt{C_i(1)}$ have unit norm for $(1-t^2)^{(d-3)/2}dt$; equivalently $\pi_i=P_i/\big(\int_{-1}^1P_i^2\bar w\big)^{1/2}$ has unit norm for $\bar w$.
--   2. For $h:[-1,1]\to\mathbb R$, the **generalized Toeplitz matrix** $\mathcal T[h]$ is the $(\ell+1)\times(\ell+1)$ symmetric matrix
--   $$\mathcal T[h]_{ij}=\frac{\omega_{d-1}}{\omega_d}\int_{-1}^1\frac{C_i(t)}{\sqrt{C_i(1)}}\frac{C_j(t)}{\sqrt{C_j(1)}}h(t)(1-t^2)^{\frac{d-3}{2}}dt=\int_{-1}^1\pi_i(t)\pi_j(t)h(t)\bar w(t)\,dt,\qquad 0\le i,j\le\ell.$$
--   3. For a real symmetric $m\times m$ matrix $A$, $\lambda_{\max}(A)=\sup\{e^{\mathsf T}Ae:\ e\in\mathbb R^m,\ \sum_ie_i^2=1\}$ is its largest eigenvalue.
--   4. For $n\ge1$, $h=\dfrac1n\displaystyle\sum_{k=1}^n\frac{C_{2k}}{C_{2k}(1)}$.
--
--   The matrices $\mathcal T[\cdot]$ turn the optimization over the polynomial $q$ in $\rho_{2n}$ into an eigenvalue problem: $\tilde\rho_{2n}(d,\ell)=n-n\lambda_{\max}(\mathcal T[h])$.
--
--   **Formalization Note** $\lambda_{\max}$ is the Rayleigh supremum; its set is nonempty and bounded for $m\ge1$, and here $m=\ell+1\ge1$. Matrix indices are $0,\dots,\ell$ as on the page. The polynomial $h$ is used with $n\ge1$ only.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, pp. 8–9, the definition of 𝒯[h] (p. 8), λ_max and h = (1/n) Σ_{k=1}^n C_{2k}/C_{2k}(1) (p. 9, before (16) and in Proposition 7)

import Mathlib
import Definitions.Def_SphereSOS_Rate_Gegenbauer

namespace SphereSOS.Rate

/-- The orthonormal Gegenbauer polynomials `√(ω_{d-1}/ω_d) C_i / √(C_i(1))`: the normalized
`P_i` rescaled to unit norm for the normalized weight. -/
noncomputable def onb (d i : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / Real.sqrt (∫ t in (-1)..1, ((geg d i).eval t) ^ 2 * wbar d t)) * geg d i

/-- The generalized Toeplitz matrix `T[h]` of size `(ℓ + 1) × (ℓ + 1)`, p. 8. -/
noncomputable def toep (d ℓ : ℕ) (h : ℝ → ℝ) : Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ :=
  fun i j => ∫ t in (-1)..1, (onb d i).eval t * (onb d j).eval t * h t * wbar d t

/-- The largest eigenvalue of a real symmetric matrix, as the supremum of its Rayleigh quotient
over unit vectors. -/
noncomputable def lamMax {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  sSup {s : ℝ | ∃ e : Fin m → ℝ, (∑ i, e i ^ 2) = 1 ∧ s = dotProduct e (Matrix.mulVec A e)}

/-- The polynomial `h = (1/n) ∑_{k=1}^n C_{2k} / C_{2k}(1)` of (16) and Proposition 7. -/
noncomputable def hpoly (d n : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, geg d (2 * k)

end SphereSOS.Rate


