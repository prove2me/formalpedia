-- Prove2me | Definitions.Def_SphereSOS_Rate_Gegenbauer
-- name    : SphereSOS_Rate_Gegenbauer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:44.011727+00:00
-- url     : https://prove2.me/theorems/6f6e7b5f-0503-41ff-9062-b4506556d880
-- title:
--   §2, (9) — normalized Gegenbauer polynomials $C_i/C_i(1)$, the weight $(1-t^2)^{(d-3)/2}$, and the Gegenbauer coefficients $\lambda_i$
-- statement:
--   Fix $d\ge2$. Let $C_i$ be the Gegenbauer polynomial of degree $i$ attached to $S^{d-1}$, orthogonal on $[-1,1]$ for the weight $w(t)=(1-t^2)^{(d-3)/2}$, and let $P_i=C_i/C_i(1)$. The $P_i$ are determined by $P_0=1$, $P_1(t)=t$ and the three-term recurrence
--   $$(k+d-1)\,P_{k+2}(t)=(2k+d)\,t\,P_{k+1}(t)-(k+1)\,P_k(t)\qquad(k\ge0).$$
--   With the normalized weight $\bar w(t)=\dfrac{\omega_{d-1}}{\omega_d}(1-t^2)^{(d-3)/2}=\dfrac{w(t)}{\int_{-1}^1w(s)\,ds}$ (where $\omega_d$ is the surface area of $S^{d-1}$), the **Gegenbauer coefficients** of a univariate polynomial $\phi$ are, as in (9),
--   $$\lambda_i(\phi)=\frac{\omega_{d-1}}{\omega_d}\int_{-1}^1\phi(t)\frac{C_i(t)}{C_i(1)}(1-t^2)^{\frac{d-3}{2}}\,dt=\int_{-1}^1\phi(t)P_i(t)\,\bar w(t)\,dt.$$
--   They are the coefficients of $\phi=\sum_i\lambda_iC_i$, and by the Funk–Hecke formula they are the eigenvalues of the kernel $\phi(\langle x,y\rangle)$ on the spherical harmonics of each degree.
--
--   **Formalization Note** The recurrence is written with real casts, so there is no natural-number subtraction; for $d\ge2$ every denominator $k+d-1$ is at least $1$. The weight uses the real power function. The objects are meaningful for $d\ge2$, the standing assumption of §2–3, and every theorem that uses them assumes $d\ge2$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, pp. 5–6, §2 (Gegenbauer polynomials, weight (1 − t²)^{(d−3)/2}), (9)

import Mathlib

namespace SphereSOS.Rate

/-- The normalized Gegenbauer polynomial `P_i = C_i / C_i(1)` attached to the sphere `S^{d-1}`,
defined by `P_0 = 1`, `P_1 = t` and the three-term recurrence
`(k + d - 1) P_{k+2} = (2k + d) t P_{k+1} - (k + 1) P_k`. Intended for `d ≥ 2`. -/
noncomputable def geg (d : ℕ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | k + 2 =>
      Polynomial.C (1 / ((k : ℝ) + (d : ℝ) - 1)) *
        (Polynomial.C (2 * (k : ℝ) + (d : ℝ)) * Polynomial.X * geg d (k + 1) -
          Polynomial.C ((k : ℝ) + 1) * geg d k)

/-- The Gegenbauer weight `(1 - t^2)^{(d-3)/2}` on `[-1, 1]`. -/
noncomputable def w (d : ℕ) (t : ℝ) : ℝ :=
  (1 - t ^ 2) ^ (((d : ℝ) - 3) / 2)

/-- The normalized weight `(ω_{d-1}/ω_d) (1 - t^2)^{(d-3)/2}`, of total mass one on `[-1, 1]`. -/
noncomputable def wbar (d : ℕ) (t : ℝ) : ℝ :=
  w d t / ∫ s in (-1)..1, w d s

/-- The `i`-th Gegenbauer coefficient `λ_i` of a univariate polynomial `φ`, equation (9). -/
noncomputable def gegCoeff (d : ℕ) (φ : Polynomial ℝ) (i : ℕ) : ℝ :=
  ∫ t in (-1)..1, φ.eval t * (geg d i).eval t * wbar d t

end SphereSOS.Rate


