-- Prove2me | Definitions.Def_pade_approximant_def
-- name    : pade_approximant_def
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T10:16:16.808976+00:00
-- url     : https://prove2.me/theorems/e9d91b63-dc30-41db-902b-e393ee9fa31d
-- title:
--   Padé pair of type $[m/n]$ (linearized Padé condition)
-- statement:
--   Fix a field (more generally, a commutative ring) $F$, a formal power series $f \in F[[x]]$, and two natural numbers $m, n \ge 0$. Following Frobenius, the Padé approximation problem of order $[m/n]$ is posed in *linearized* form: rather than requiring that the rational function $P/Q$ agree with $f$ to order $m+n$, which is a nonlinear condition and presupposes $Q(0) \ne 0$, one requires the polynomial congruence below.
--
--   A pair of polynomials $(P, Q)$ is a **Padé pair of type $[m/n]$ for $f$** when
--
--   $$ Q \ne 0, \qquad \deg P \le m, \qquad \deg Q \le n, \qquad Q(x) f(x) - P(x) \equiv 0 \pmod{x^{m+n+1}} . $$
--
--   The congruence is expressed coefficientwise: every coefficient of index $k \le m+n$ of the power series $Qf - P$ vanishes, the polynomials being viewed inside $F[[x]]$ through the canonical inclusion. Degrees are taken with the convention $\deg 0 = -\infty$, so the numerator is allowed to be the zero polynomial while the denominator is explicitly required to be nonzero.
--
--   This predicate is the object every statement in the mission is phrased with. It deliberately does not normalize the denominator: $Q(0)$ may vanish, which is exactly the situation in which the source's displayed form $R = (\sum_{j\le m} a_jx^j)/(1 + \sum_{k\le n} b_kx^k)$ does not exist, and it is what makes the existence theorem unconditional.
-- source:
--   Padé approximant, Wikipedia, revision oldid=1374746248, https://en.wikipedia.org/w/index.php?title=Pad%C3%A9_approximant&oldid=1374746248, section 'Definition'

import Mathlib

/-!
# The linearized Padé condition

Source: "Padé approximant", Wikipedia (oldid 1374746248), section *Definition*.
-/

namespace Pade

/-- `IsPadeApproximant f m n P Q` says that the rational function `P / Q` is a
Padé approximant of order `[m/n]` of the (formal) power series `f`, in the
classical *linearized* sense of Frobenius:

* `Q ≠ 0`;
* `deg P ≤ m` and `deg Q ≤ n`;
* `Q * f - P ≡ 0  (mod X^(m+n+1))`, i.e. all coefficients of index `k ≤ m + n`
  of the power series `Q * f - P` vanish.

This is the linearization of `f - P/Q = O(X^(m+n+1))`. -/
def IsPadeApproximant {R : Type*} [CommRing R] (f : PowerSeries R) (m n : ℕ)
    (P Q : Polynomial R) : Prop :=
  Q ≠ 0 ∧ P.degree ≤ (m : WithBot ℕ) ∧ Q.degree ≤ (n : WithBot ℕ) ∧
    ∀ k ≤ m + n, PowerSeries.coeff k ((Q : PowerSeries R) * f - (P : PowerSeries R)) = 0

end Pade


