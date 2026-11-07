-- Prove2me | Definitions.Def_PolySphereLP_Zg
-- name    : PolySphereLP_Zg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:00:58.580694+00:00
-- url     : https://prove2.me/theorems/ea0cfb11-023e-4209-bdc3-41b731808ab4
-- title:
--   The data polynomial $Z_g(\mathbf a)=\int gF_{\mathbf a}\,d\sigma$
-- statement:
--   For a fixed polynomial $g$ in the solution variable $x$,
--   $$Z_g(\mathbf a)=\int g(x)F_{\mathbf a}(x)\,d\sigma(x).$$
--   The witness evaluates a test as $\mathcal L_{\mathbf a,\alpha}(g)=\int g\,d\sigma+\alpha Z_g(\mathbf a)$.
--
--   **Formalization Note** Defined for every $\mathbf a\in\mathbb R^h$ by the same formula.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Lemma 3.2, p.17

import Mathlib
import Definitions.Def_PolySphereLP_Fa

namespace PolySphereLP

/-- **The data polynomial `Z_g(a)`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Lemma 3.2, p.17: `Z_g(a) =def ∫ g(x)F_a(x) dσ(x)`.

**Formalization Note.** Defined for every `a ∈ ℝ^h` by the same formula; the paper uses it on
`S^{h−1}`. -/
noncomputable def Zg (n q r : ℕ) {h : ℕ} (Y : Fin h → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ) (a : Fin h → ℝ) : ℝ :=
  ∫ x, MvPolynomial.eval x g * MvPolynomial.eval x (Fa n q r Y a) ∂(SphereSOS.Rate.sigma n)

end PolySphereLP


