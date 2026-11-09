-- Prove2me | Definitions.Def_NadlerCLS_PNAnswer
-- name    : NadlerCLS_PNAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:01:37.137742+00:00
-- url     : https://prove2.me/theorems/7e844f0c-3416-4b78-9516-752f906dd9eb
-- title:
--   Valid outputs (N1)–(N4) of $\beta$-Projected-Nadler
-- statement:
--   For an instance with clipped circuits $\Pi$, $d$, diagonal map $P$ and residual $r$, a valid output is one of the following, all points rational points of $X=[0,1]^n$:
--
--   1. **(N1)** a point $x$ with $r(x)\le\varepsilon_1$;
--   2. **(N2)** points $x,y,z$ such that, for $u=\Pi(x,z),\ v=\Pi(y,u)$ or for $u=\Pi(y,z),\ v=\Pi(x,u)$,
--   $$ d(u,v)>k\,d(x,y)+\varepsilon_2 ; $$
--   3. **(N3)** points $x,y$ with $\|P(x)-P(y)\|_1>L_P\|x-y\|_1^{\beta}$;
--   4. **(N4)** points $a,b,a',b'$ with $a\ne b$, $a'\ne b'$ and
--   $$ |d(a,b)-d(a',b')|>L_d\big(\|a-a'\|_1+\|b-b'\|_1\big). $$
--
--   (N2) certifies a violation of the contraction, (N3) a violation of the claimed $\beta$-Hölder regularity of $P$, and (N4) a violation of the off-diagonal Lipschitz regularity of $d$.
--
--   **Formalization Note** An answer string is a tag ($0$–$3$, for N1–N4) followed by the coded points; $u$, $v$ are computed, and either orientation of (N2) is accepted. $t^\beta$ is the real power with $0^\beta=0$.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Definition 1, p.9, (N1)–(N4), Eqs. (3.1)–(3.2)

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_l1
import Definitions.Def_NadlerCLS_PNInstance

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- The **valid outputs of β-Projected-Nadler** (Xiong–Vlatakis-Gkaragkounis, *On the Complexity of
Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held version of 2026-11-03,
sha256 1fcc5a02…6dc485, Definition 1, p.9). The string `t` is one of the following, with all points
rational points of `X = [0, 1]ⁿ`:

* (N1) `encNat 0 ++ x`, with `r(x) ≤ ε₁`;
* (N2) `encNat 1 ++ x ++ y ++ z`, such that for `u = Π(x, z), v = Π(y, u)` **or**
  `u = Π(y, z), v = Π(x, u)`, `d(u, v) > k d(x, y) + ε₂` (3.1);
* (N3) `encNat 2 ++ x ++ y`, with `‖P(x) − P(y)‖₁ > L_P ‖x − y‖₁^β`;
* (N4) `encNat 3 ++ a ++ b ++ a' ++ b'`, with `a ≠ b`, `a' ≠ b'` and
  `|d(a, b) − d(a', b')| > L_d (‖a − a'‖₁ + ‖b − b'‖₁)` (3.2).

**Formalization Note** Points are written with the public `encVector` and tagged by answer type;
`u`, `v` are computed values, not answer fields, and either orientation of (N2) is accepted.
`‖·‖₁^β` is the real power `Real.rpow` (so `0 ^ β = 0` for `β > 0`). Π and d are the clipped
circuits of `PNInstance`. -/
def PNAnswer {n : ℕ} (I : PNInstance n) (β : ℚ) (t : List Bool) : Prop :=
  (∃ x : Fin n → ℚ, t = encNat 0 ++ encVector x ∧ InCube (rpt x) ∧
    I.r (rpt x) ≤ (I.ε₁ : ℝ)) ∨
  (∃ x y z : Fin n → ℚ, t = encNat 1 ++ encVector x ++ encVector y ++ encVector z ∧
    InCube (rpt x) ∧ InCube (rpt y) ∧ InCube (rpt z) ∧
    (I.dist (I.Pi (rpt x) (rpt z)) (I.Pi (rpt y) (I.Pi (rpt x) (rpt z))) >
        (I.k : ℝ) * I.dist (rpt x) (rpt y) + I.ε₂ ∨
      I.dist (I.Pi (rpt y) (rpt z)) (I.Pi (rpt x) (I.Pi (rpt y) (rpt z))) >
        (I.k : ℝ) * I.dist (rpt x) (rpt y) + I.ε₂)) ∨
  (∃ x y : Fin n → ℚ, t = encNat 2 ++ encVector x ++ encVector y ∧
    InCube (rpt x) ∧ InCube (rpt y) ∧
    l1 (I.P (rpt x)) (I.P (rpt y)) > (I.LP : ℝ) * (l1 (rpt x) (rpt y)) ^ (β : ℝ)) ∨
  (∃ a b a' b' : Fin n → ℚ,
    t = encNat 3 ++ encVector a ++ encVector b ++ encVector a' ++ encVector b' ∧
    InCube (rpt a) ∧ InCube (rpt b) ∧ InCube (rpt a') ∧ InCube (rpt b') ∧ a ≠ b ∧ a' ≠ b' ∧
    |I.dist (rpt a) (rpt b) - I.dist (rpt a') (rpt b')| >
      (I.Ld : ℝ) * (l1 (rpt a) (rpt a') + l1 (rpt b) (rpt b')))

end NadlerCLS


