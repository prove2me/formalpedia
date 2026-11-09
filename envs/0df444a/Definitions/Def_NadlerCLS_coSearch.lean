-- Prove2me | Definitions.Def_NadlerCLS_coSearch
-- name    : NadlerCLS_coSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:00:53.018824+00:00
-- url     : https://prove2.me/theorems/cec6b9ef-0891-4585-913b-fd1b68228846
-- title:
--   The search problem Continuous-LocalOpt ($\ell_1$ norm, two circuits)
-- statement:
--   Continuous-LocalOpt on $[0,1]^n$: given an instance $(f,p,\delta,\lambda)$, find one of
--
--   1. **(CO1)** a point $x$ with $p(f(x))\ge p(x)-\delta$;
--   2. **(CO2)** points $x,y$ with $\|f(x)-f(y)\|_1>\lambda\|x-y\|_1$;
--   3. **(CO3)** points $x,y$ with $|p(x)-p(y)|>\lambda\|x-y\|_1$;
--
--   all points rational points of $[0,1]^n$. For $n=3$ this is Definition 2, the standard complete problem for CLS.
--
--   **Formalization Note** This is the paper's formulation (two circuits, $\ell_1$ norm). The platform's class CLS is defined through the public canonical problem `clsSearch` (one shared circuit, max norm); a milestone of this mission relates the two at $n=3$.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Definition 2, p.11

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_l1
import Definitions.Def_NadlerCLS_COInstance

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- The search problem **Continuous-LocalOpt** on `[0, 1]ⁿ` with the ℓ₁ norm
(Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485, Definition 2,
p.11). Valid instances are codes of valid `COInstance`s; an answer is, for rational points of the
cube,

* (CO1) `encNat 0 ++ x` with `p(f(x)) ≥ p(x) − δ`;
* (CO2) `encNat 1 ++ x ++ y` with `‖f(x) − f(y)‖₁ > λ ‖x − y‖₁`;
* (CO3) `encNat 2 ++ x ++ y` with `|p(x) − p(y)| > λ ‖x − y‖₁`.

**Formalization Note** `f` and `p` are the clipped circuits `fC`, `pC`. This is Definition 2 with
two circuits and the ℓ₁ norm, which differs from the public canonical `clsSearch` (one shared DAG,
the max norm); the two are related by a milestone of this mission. -/
def coSearch (n : ℕ) : SearchProblem where
  valid s := ∃ I : COInstance n, I.Valid ∧ encCO I = s
  answer s t := ∃ I : COInstance n, I.Valid ∧ encCO I = s ∧
    ((∃ x : Fin n → ℚ, t = encNat 0 ++ encVector x ∧ InCube (rpt x) ∧
        I.pC (I.fC (rpt x)) ≥ I.pC (rpt x) - I.δ) ∨
     (∃ x y : Fin n → ℚ, t = encNat 1 ++ encVector x ++ encVector y ∧
        InCube (rpt x) ∧ InCube (rpt y) ∧
        l1 (I.fC (rpt x)) (I.fC (rpt y)) > (I.lam : ℝ) * l1 (rpt x) (rpt y)) ∨
     (∃ x y : Fin n → ℚ, t = encNat 2 ++ encVector x ++ encVector y ∧
        InCube (rpt x) ∧ InCube (rpt y) ∧
        |I.pC (rpt x) - I.pC (rpt y)| > (I.lam : ℝ) * l1 (rpt x) (rpt y)))

end NadlerCLS


