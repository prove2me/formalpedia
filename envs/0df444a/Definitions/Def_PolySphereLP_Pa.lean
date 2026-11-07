-- Prove2me | Definitions.Def_PolySphereLP_Pa
-- name    : PolySphereLP_Pa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:22.063917+00:00
-- url     : https://prove2.me/theorems/306ecf70-ca59-41a8-adc8-aab82ace3065
-- title:
--   The random harmonic polynomial $P_{\mathbf a}=\langle\mathbf a,\Psi_d\rangle$
-- statement:
--   Given an orthonormal basis $Y_1,\dots,Y_h$ of $\mathcal H_{n,d}$ and a coefficient vector $\mathbf a\in\mathbb R^h$,
--   $$P_{\mathbf a}(x)=\langle\mathbf a,\Psi_d(x)\rangle=\sum_{i=1}^h a_iY_i(x).$$
--   In the paper's random model $\mathbf a\sim\nu=\mathrm{Unif}(S^{h-1})$.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (14), p.10

import Mathlib

namespace PolySphereLP

/-- **The random harmonic polynomial `P_a`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (14), p.10: `P_a(x) = ⟨a, Ψ_d(x)⟩ =
∑ᵢ aᵢ Yᵢ(x)`.

`Pa Y a = ∑ᵢ aᵢ Yᵢ` for a coefficient vector `a ∈ ℝ^h`. -/
noncomputable def Pa {n h : ℕ} (Y : Fin h → MvPolynomial (Fin n) ℝ) (a : Fin h → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.C (a i) * Y i

end PolySphereLP


