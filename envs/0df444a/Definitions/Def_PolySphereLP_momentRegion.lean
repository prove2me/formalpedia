-- Prove2me | Definitions.Def_PolySphereLP_momentRegion
-- name    : PolySphereLP_momentRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:44.133403+00:00
-- url     : https://prove2.me/theorems/842e1e03-0fed-46d0-8202-c4982fbe26ec
-- title:
--   The moment region $\mathcal F_{q,\mathcal G}$
-- statement:
--   Fix tests $\mathcal G=\{g_1,\dots,g_M\}\subseteq\mathbb R[x]_{\le q}$. The **moment region** $\mathcal F_{q,\mathcal G}$ is the set of linear functionals $\mathcal L$ with
--   $$\mathcal L(1)=1,\qquad \mathcal L\big((\|x\|^2-1)f\big)=0\ \ (\deg f\le q-2),\qquad \mathcal L(g_j)\ge0\ \ (j\in[M]).$$
--   Every evaluation functional at a point of the sphere lies in it when every $g_j$ is nonnegative on $S^{n-1}$.
--
--   **Formalization Note** Functionals are linear maps on all of $\mathbb R[x]$, constrained only through polynomials of degree at most $q$ (every test in the items has degree at most $q$). Restricting to $\mathbb R[x]_{\le q}$ and extending linearly from it give the same set of values $\mathcal L(P^r)$ when $\deg P^r\le q$, so the supremum in (12) is unchanged.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (11), p.10

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting

namespace PolySphereLP

/-- **The moment region `ℱ_{q,𝒢}`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (11), p.10: the linear functionals `ℒ : ℝ[x]_{≤q} → ℝ`
with `ℒ(1) = 1`, `ℒ((‖x‖² − 1) f) = 0` (`deg f ≤ q − 2`), `ℒ(g_j) ≥ 0` (`j ∈ [M]`).

`momentRegion n q g` is the set of `ℝ`-linear `L : ℝ[x₁,…,xₙ] → ℝ` with `L 1 = 1`,
`L((x₁²+⋯+xₙ² − 1) f) = 0` for every `f` of total degree `≤ q − 2`, and `L (g j) ≥ 0` for every `j`.

**Formalization Note.** Functionals are taken on all of `ℝ[x]`, constrained only through polynomials
of degree `≤ q` (the tests have degree `≤ q` in every item). Restriction to `ℝ[x]_{≤q}` and linear
extension from it give the same set of values `L(P^r)` for `deg P^r ≤ q`, so the supremum in (12) is
unchanged. `q − 2` is natural subtraction; every item has `q ≥ 4`. -/
def momentRegion (n q : ℕ) {M : ℕ} (g : Fin M → MvPolynomial (Fin n) ℝ) :
    Set (MvPolynomial (Fin n) ℝ → ℝ) :=
  {L | IsLinearMap ℝ L ∧ L 1 = 1 ∧
    (∀ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ q - 2 →
      L ((SphereSOS.Rate.normSqPoly n - 1) * f) = 0) ∧
    ∀ j, 0 ≤ L (g j)}

end PolySphereLP


