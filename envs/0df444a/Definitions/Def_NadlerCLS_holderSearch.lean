-- Prove2me | Definitions.Def_NadlerCLS_holderSearch
-- name    : NadlerCLS_holderSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:00:29.102734+00:00
-- url     : https://prove2.me/theorems/c41a6ec4-90ec-4e2b-98b6-852b3afb4e0e
-- title:
--   The search problem $\beta$-Hölder-LocalOpt
-- statement:
--   $\beta$-Hölder-LocalOpt on $[0,1]^n$, for a fixed rational $\beta\in(0,1]$: given an instance $(f,p,\delta,\lambda)$, find one of
--
--   1. **(HO1)** a point $x$ with $p(f(x))\ge p(x)-\delta$;
--   2. **(HO2)** points $x,y$ with $\|f(x)-f(y)\|_1>\lambda\|x-y\|_1^{\beta}$;
--   3. **(HO3)** points $x,y$ with $|p(x)-p(y)|>\lambda\|x-y\|_1^{\beta}$;
--
--   all points rational points of $[0,1]^n$. It replaces the Lipschitz conditions of Continuous-LocalOpt by Hölder conditions and is the intermediate problem of the membership proof.
--
--   **Formalization Note** The exponent $\beta$ is not part of the input (p.31); $t^\beta$ is the real power.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Definition 5, p.31

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_l1
import Definitions.Def_NadlerCLS_COInstance

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- The search problem **β-Hölder-LocalOpt** on `[0, 1]ⁿ` (Xiong–Vlatakis-Gkaragkounis, *On the
Complexity of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held version of
2026-11-03, sha256 1fcc5a02…6dc485, Definition 5, p.31). Valid instances are codes of valid
`COInstance`s; an answer is, for rational points of the cube,

* (HO1) `encNat 0 ++ x` with `p(f(x)) ≥ p(x) − δ`;
* (HO2) `encNat 1 ++ x ++ y` with `‖f(x) − f(y)‖₁ > λ ‖x − y‖₁^β`;
* (HO3) `encNat 2 ++ x ++ y` with `|p(x) − p(y)| > λ ‖x − y‖₁^β`.

**Formalization Note** `f` and `p` are the clipped circuits `fC`, `pC`; `‖·‖₁^β` is `Real.rpow`.
The exponent `β` is a fixed parameter of the problem (p.31: "The exponent β is not part of the
input"). -/
def holderSearch (n : ℕ) (β : ℚ) : SearchProblem where
  valid s := ∃ I : COInstance n, I.Valid ∧ encCO I = s
  answer s t := ∃ I : COInstance n, I.Valid ∧ encCO I = s ∧
    ((∃ x : Fin n → ℚ, t = encNat 0 ++ encVector x ∧ InCube (rpt x) ∧
        I.pC (I.fC (rpt x)) ≥ I.pC (rpt x) - I.δ) ∨
     (∃ x y : Fin n → ℚ, t = encNat 1 ++ encVector x ++ encVector y ∧
        InCube (rpt x) ∧ InCube (rpt y) ∧
        l1 (I.fC (rpt x)) (I.fC (rpt y)) > (I.lam : ℝ) * (l1 (rpt x) (rpt y)) ^ (β : ℝ)) ∨
     (∃ x y : Fin n → ℚ, t = encNat 2 ++ encVector x ++ encVector y ∧
        InCube (rpt x) ∧ InCube (rpt y) ∧
        |I.pC (rpt x) - I.pC (rpt y)| > (I.lam : ℝ) * (l1 (rpt x) (rpt y)) ^ (β : ℝ)))

end NadlerCLS


