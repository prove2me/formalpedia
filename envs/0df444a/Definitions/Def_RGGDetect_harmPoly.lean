-- Prove2me | Definitions.Def_RGGDetect_harmPoly
-- name    : RGGDetect_harmPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:42.42516+00:00
-- url     : https://prove2.me/theorems/eabf827b-0994-4a1d-b7f0-080ad3afe697
-- title:
--   Spherical harmonics $\mathcal H_{\ell,d}$, their dimension $N_{\ell,d}$, the zonal polynomials $P_{\ell,d}$, and the tensor spaces $\mathcal H_{\boldsymbol\ell}$
-- statement:
--   1. $\mathcal H_{\ell,d}$, the **degree-$\ell$ spherical harmonics** on $S^{d-1}$, is the space of restrictions to the sphere of homogeneous polynomials $P$ of degree $\ell$ in $d$ variables with $\sum_i\partial_i^2P=0$.
--   2. $N_{\ell,d}=\dim\mathcal H_{\ell,d}$.
--   3. The **normalized zonal harmonic** $P_{\ell,d}=C_{\ell,\lambda}/C_{\ell,\lambda}(1)$, $\lambda=(d-2)/2$ (Gegenbauer), is the polynomial given by $P_0=1$, $P_1(t)=t$ and
--   $$
--   (k+d-1)\,P_{k+2}(t)=(2k+d)\,t\,P_{k+1}(t)-(k+1)\,P_k(t).
--   $$
--   4. For a finite set $V$ of points and a multidegree $\boldsymbol\ell=(\ell_v:v\in V)$ with $\ell_v\ge1$, the **tensor-product space** (14) is
--   $$
--   \mathcal H_{\boldsymbol\ell}=\bigotimes_{v\in V}\mathcal H_{\ell_v}=\operatorname{span}\Big\{\prod_{v\in V}f_v(x_v):f_v\in\mathcal H_{\ell_v}\Big\},
--   $$
--   a space of functions of the configuration. For nonzero $D\in\mathcal H_{\boldsymbol\ell}$, $\boldsymbol\ell$ is its multidegree and $\|\boldsymbol\ell\|_1$ its total degree.
--
--   These are the spaces in which the paper's cavity recurrence is closed.
--
--   **Formalization Note** Polynomials are `MvPolynomial (Fin d) ℝ`. The recurrence for $P_{\ell,d}$ is the normalized Gegenbauer recurrence (Chebyshev for $d=2$) and is the same as the published `SphereSOS.Rate.geg`; it is meaningful for $d\ge2$. A multidegree is a function on the index type of which only the values on $V$ matter; a factor of degree $0$ is a constant, which covers the paper's $D\equiv1$.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), §2.3, eq. (14), p.7 (PDF p.9); (50)–(53), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere

namespace RGGDetect

/-- The restriction to `S^{d-1}` of a real polynomial in `d` variables. -/
noncomputable def polyOnSphere {d : ℕ} (P : MvPolynomial (Fin d) ℝ) : Sph d → ℝ :=
  fun x => MvPolynomial.eval (fun i => (x : EuclideanSpace ℝ (Fin d)) i) P

/-- `H_{ℓ,d}`, the space of degree-`ℓ` spherical harmonics on `S^{d-1}`: restrictions to the sphere
of homogeneous polynomials of degree `ℓ` in `d` variables with vanishing Laplacian
`∑_i ∂_i² P = 0` (arXiv:2610.08517, held version, §2.3, p.7). -/
noncomputable def harmPoly (d ℓ : ℕ) : Submodule ℝ (Sph d → ℝ) :=
  Submodule.span ℝ {f | ∃ P : MvPolynomial (Fin d) ℝ, P.IsHomogeneous ℓ ∧
    (∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 ∧ f = polyOnSphere P}

/-- `N_{ℓ,d} = dim H_{ℓ,d}` (arXiv:2610.08517, held version, §2.3, p.7). -/
noncomputable def harmDim (d ℓ : ℕ) : ℕ := Module.finrank ℝ (harmPoly d ℓ)

/-- The normalized zonal harmonic `P_{ℓ,d} = C_{ℓ,λ}/C_{ℓ,λ}(1)`, `λ = (d-2)/2`
(arXiv:2610.08517, held version, (51), (53), p.18), as a polynomial in one variable, by the
three-term recurrence `P₀ = 1`, `P₁ = t`,
`(k + d - 1) P_{k+2}(t) = (2k + d) t P_{k+1}(t) - (k + 1) P_k(t)`.

**Formalization Note** The recurrence is the normalized Gegenbauer recurrence (for `d = 2` the
Chebyshev one); it is the same recurrence as the published `SphereSOS.Rate.geg` (6f6e7b5f). It is
meaningful for `d ≥ 2` (for `d = 1` the first step divides by `0`), and every statement using it
assumes `d ≥ 2`. -/
noncomputable def zonal (d : ℕ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | (k + 2) => Polynomial.C (1 / ((k : ℝ) + d - 1)) *
      (Polynomial.C (2 * (k : ℝ) + d) * Polynomial.X * zonal d (k + 1) -
        Polynomial.C ((k : ℝ) + 1) * zonal d k)

/-- The tensor-product space (14) `H_ℓ = ⊗_{v ∈ V} H_{ℓ_v}`: the span of the functions
`x ↦ ∏_{v ∈ V} f_v(x_v)` of a configuration, with `f_v ∈ H_{ℓ_v}` (arXiv:2610.08517, held version,
§2.3, p.7, eq. (14)).

**Formalization Note** Points are indexed by a finite type `ι` and a multidegree is a function
`ℓ : ι → ℕ` of which only the values on `V` matter; the paper requires `ℓ_v ≥ 1` on `V`, which the
statements assume. The elements are functions of the whole configuration that depend only on the
coordinates in `V`. With `ℓ_v = 0` the factor is a constant (degree-0 harmonics), which is how the
paper's `D ≡ 1` is covered. -/
noncomputable def tensorHarm {ι : Type*} {d : ℕ} (V : Finset ι) (ℓ : ι → ℕ) :
    Submodule ℝ ((ι → Sph d) → ℝ) :=
  Submodule.span ℝ {D | ∃ f : ι → Sph d → ℝ, (∀ v ∈ V, f v ∈ harmPoly d (ℓ v)) ∧
    D = fun x => ∏ v ∈ V, f v (x v)}

end RGGDetect


