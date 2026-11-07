-- Prove2me | Definitions.Def_PolySphereLP_powLP
-- name    : PolySphereLP_powLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:30.631203+00:00
-- url     : https://prove2.me/theorems/1829b3aa-9299-4bfa-b3d5-cf7a02c78641
-- title:
--   The powered-objective LP value $\mathrm{PowLP}_{q,\mathcal G}(P)$
-- statement:
--   For a polynomial $P$ and an even integer $r$ (the paper takes $r=q/d$ for $P$ of degree $d$),
--   $$\mathrm{PowLP}_{q,\mathcal G}(P)=\Big(\sup_{\mathcal L\in\mathcal F_{q,\mathcal G}}\mathcal L(P^r)\Big)^{1/r}.$$
--   The inner problem is a linear program; its value is positive for nonzero $P$, possibly $+\infty$, and $\mathrm{PowLP}_{q,\mathcal G}(P)\ge\|P\|_\infty$.
--
--   **Formalization Note** The value is taken in $[0,+\infty]$, since it may be $+\infty$. Each $\mathcal L(P^r)$ enters through its nonnegative part; when the tests are nonnegative on the sphere the region contains evaluation functionals, the supremum is at least $\|P\|_\infty^r\ge0$, and this changes nothing. The exponent $r$ is a separate argument.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (12), p.10

import Mathlib
import Definitions.Def_PolySphereLP_momentRegion

namespace PolySphereLP

/-- **The powered-objective LP value `PowLP_{q,𝒢}(P)`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (12), p.10:
`PowLP_{q,𝒢}(P) =def (sup_{ℒ∈ℱ_{q,𝒢}} ℒ(P^r))^{1/r}`; "its supremum is positive for nonzero P,
possibly +∞".

`powLP n q r g P = (⨆_{L ∈ ℱ_{q,𝒢}} L(P^r))^{1/r}` in `[0, ∞]`.

**Formalization Note.** Computed in `ℝ≥0∞` because the value may be `+∞` (a real `sSup` would
return `0`). Each value `L(P^r)` enters through `ENNReal.ofReal`; this truncation does not change the
supremum when the region contains an evaluation functional at a sphere point (true when every test is
nonnegative on the sphere, as in every item), since then the supremum is `≥ ‖P‖_∞^r ≥ 0` for even `r`.
The exponent `r` is a separate argument; the items pass `r = q/d`. -/
noncomputable def powLP (n q r : ℕ) {M : ℕ} (g : Fin M → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin n) ℝ) : ENNReal :=
  (⨆ L ∈ momentRegion n q g, ENNReal.ofReal (L (P ^ r))) ^ (1 / (r : ℝ))

end PolySphereLP


