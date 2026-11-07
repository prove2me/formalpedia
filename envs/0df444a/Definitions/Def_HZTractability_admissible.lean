-- Prove2me | Definitions.Def_HZTractability_admissible
-- name    : HZTractability_admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:52.688043+00:00
-- url     : https://prove2.me/theorems/2926edd9-c2ad-4e87-85a8-84168147fd46
-- title:
--   Admissible wire sizes $K$ (display (20))
-- statement:
--   Write $a=A/D$ in lowest terms and put
--   $$
--   C=16D^2,\qquad b=4C .
--   $$
--   A natural number $K$ is **admissible** if it is a positive multiple of $D^2(D^2-A^2)$ and
--   $$
--   K\ge\frac{8b+200/\kappa}{a^2(1-a)},
--   $$
--   with $\kappa=1/200$. $K$ is the size of every wire population of the market $M(G;a,\tau,K)$.
--
--   All construction parameters are evaluated from $a$, $\tau$ and an admissible $K$.
--
--   **Formalization Note** $A$ is the absolute value of the numerator and $D$ the denominator of the reduced fraction. $D^2-A^2$ is natural-number subtraction, which is the true difference for $a\in(0,1)$.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §4.4, display (20), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_HZTractability_kappa

namespace HZTractability

/-- The numerator `A` of `a = A/D` in lowest terms (§4.4, p.17). -/
def Aa (a : ℚ) : ℕ := a.num.natAbs

/-- The denominator `D` of `a = A/D` in lowest terms (§4.4, p.17). -/
def Da (a : ℚ) : ℕ := a.den

/-- The constant `C = 16 D²` (§4.4, p.17 (PDF 19)). -/
def Cc (a : ℚ) : ℕ := 16 * Da a ^ 2

/-- The constant `b = 4C` (§4.4, p.17 (PDF 19)). -/
def bb (a : ℚ) : ℕ := 4 * Cc a

/-- **Admissible `K`** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held version, sha256
74b7bf9f…, §4.4, display (20), p.17 (PDF 19)): "Write a = A/D in lowest terms and put C = 16D²,
b = 4C. … choose a positive multiple K of D²(D² − A²) such that K ≥ (8b + 200/κ)/(a²(1 − a)). We
call these values of K admissible."

`K` is the size of every wire population (§3, p.10).

**Formalization Note** `K` is a natural number and `κ = 1/200` (`kappa`). `D² − A²` is natural
subtraction; it is the true difference for `a ∈ (0, 1)` (then `A < D`), the only case the paper
uses. -/
def admissible (a : ℚ) (K : ℕ) : Prop :=
  0 < K ∧ Da a ^ 2 * (Da a ^ 2 - Aa a ^ 2) ∣ K ∧
    (8 * (bb a : ℚ) + 200 / kappa) / (a ^ 2 * (1 - a)) ≤ (K : ℚ)

end HZTractability


