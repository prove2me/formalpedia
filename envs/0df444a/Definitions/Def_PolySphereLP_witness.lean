-- Prove2me | Definitions.Def_PolySphereLP_witness
-- name    : PolySphereLP_witness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:00:48.154106+00:00
-- url     : https://prove2.me/theorems/8016897c-ae4d-441b-8d0d-ddc41d0faed1
-- title:
--   The witness functional $\mathcal L_{\mathbf a,\alpha}$
-- statement:
--   For $\mathbf a\in S^{h-1}$ and $\alpha\ge0$,
--   $$\mathcal L_{\mathbf a,\alpha}(f)=\int f(x)\big(1+\alpha F_{\mathbf a}(x)\big)\,d\sigma(x).$$
--   It satisfies normalization and the sphere equalities for every $\alpha$, and $\mathcal L_{\mathbf a,\alpha}(P_{\mathbf a}^r)\ge\alpha\|F_{\mathbf a}\|^2_{L^2(\sigma)}$ for even $r$; the main lemma chooses $\alpha$ so that it also satisfies the test inequalities.
--
--   **Formalization Note** Defined by the same formula on all of $\mathbb R[x]$, a linear extension of the functional on $\mathbb R[x]_{\le q}$.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (39)–(41), p.16

import Mathlib
import Definitions.Def_PolySphereLP_Fa

namespace PolySphereLP

/-- **The witness functional `ℒ_{a,α}`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (39), p.16: for `a ∈ S^{h−1}` and `α ≥ 0`,
`ℒ_{a,α}(f) =def ∫ f(x)(1 + αF_a(x)) dσ(x)` (`f ∈ ℝ[x]_{≤q}`).

**Formalization Note.** Defined by the same formula on all of `ℝ[x]` (the region `momentRegion` lives
on all polynomials); this is a linear extension of the paper's functional. The integrand is a
polynomial, integrable against `σ`. -/
noncomputable def witness (n q r : ℕ) {h : ℕ} (Y : Fin h → MvPolynomial (Fin n) ℝ) (a : Fin h → ℝ)
    (α : ℝ) (f : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∫ x, MvPolynomial.eval x f * (1 + α * MvPolynomial.eval x (Fa n q r Y a)) ∂(SphereSOS.Rate.sigma n)

end PolySphereLP


