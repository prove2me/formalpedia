-- Prove2me | Definitions.Def_SwdAlgebra
-- name    : SwdAlgebra
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/0032ee72-a419-54fb-be5b-72a114e5d380
-- title:
--   Ramanujan's q-series P,Q,R and the Swinnerton-Dyer algebra
-- statement:
--   Over an arbitrary field $F$, three elements of the formal power series ring $F[[q]]$ are defined by explicit integer coefficient formulas, pushed forward along the canonical ring homomorphism $\mathbb{Z} \to F$: `qP F` has constant term $1$ and $n$-th coefficient $-24\sum_{d \mid n} d$ for $n \geq 1$; `qE4 F` has constant term $1$ and $n$-th coefficient $240\sum_{d \mid n} d^3$; `qE6 F` has constant term $1$ and $n$-th coefficient $-504\sum_{d \mid n} d^5$. These are the reductions to $F$ of Ramanujan's series $P = E_2$, $Q = E_4$ and $R = E_6$, the divisor sums being taken over `Nat.divisors`.
--
--   For an integer $n$, `swdSpan F n` is the $F$-submodule of $F[[q]]$ spanned by the set of products $(\mathtt{qE4}\,F)^a (\mathtt{qE6}\,F)^b$ over pairs of natural numbers $a, b$ with $4a + 6b = n$ as integers; this is the weight-$n$ graded piece of the image of $F[X,Y]$ in $F[[q]]$, and it is the zero submodule whenever no such pair exists (in particular for $n$ negative and for $n = 2$).
--
--   The remaining two definitions concern the polynomial model. `ev F` is the $F$-algebra homomorphism from `MvPolynomial (Fin 2) F` to $F[[q]]$ obtained by evaluating the two variables at `qE4 F` and `qE6 F` respectively, so that the first variable carries weight $4$ and the second weight $6$. `sD F` is the $F$-derivation of `MvPolynomial (Fin 2) F` equal to $-4Y \cdot \partial/\partial X + (-6X^2) \cdot \partial/\partial Y$, where $X, Y$ denote the variables indexed by $0$ and $1$; it sends $X$ to $-4Y$ and $Y$ to $-6X^2$, and hence raises the weight $4a + 6b$ of an isobaric polynomial by $2$, reflecting Ramanujan's differential equations for $Q$ and $R$ with respect to $\theta = q\,d/dq$.
--
--   **Relation to Mathlib.** The ambient notions — `PowerSeries` and its functoriality, `Nat.divisors`, `MvPolynomial` with `MvPolynomial.pderiv`, `Derivation` and `Submodule.span` — are Mathlib's. The $q$-series here are defined by their coefficient formulas as formal power series over an arbitrary field, independently of Mathlib's analytic theory of modular forms and Eisenstein series on the upper half-plane.
--
--   **Where it is used.** These definitions provide the vocabulary for the level-one theory of modular forms modulo $p$ in the style of Swinnerton-Dyer: the graded pieces `swdSpan F n` and the derivation `sD F` encode the structure of $F[\tilde{E}_4, \tilde{E}_6]$ and the action of $\theta = q\,d/dq$ on it, which is what is needed for the congruences between $q$-expansions used on the modular side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_SwdAlgebra.lean

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Span.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace SwdAlgebra

noncomputable def qP (F : Type) [Field F] : PowerSeries F :=
  PowerSeries.map (Int.castRingHom F)
    (PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ))

noncomputable def qE4 (F : Type) [Field F] : PowerSeries F :=
  PowerSeries.map (Int.castRingHom F)
    (PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3)

noncomputable def qE6 (F : Type) [Field F] : PowerSeries F :=
  PowerSeries.map (Int.castRingHom F)
    (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5)

noncomputable def swdSpan (F : Type) [Field F] (n : ℤ) : Submodule F (PowerSeries F) :=
  Submodule.span F {ψ | ∃ a b : ℕ, (4 * a + 6 * b : ℤ) = n ∧ ψ = qE4 F ^ a * qE6 F ^ b}

noncomputable def ev (F : Type) [Field F] : MvPolynomial (Fin 2) F →ₐ[F] PowerSeries F :=
  MvPolynomial.aeval ![qE4 F, qE6 F]

noncomputable def sD (F : Type) [Field F] :
    Derivation F (MvPolynomial (Fin 2) F) (MvPolynomial (Fin 2) F) :=
  (MvPolynomial.C (-4 : F) * MvPolynomial.X 1 : MvPolynomial (Fin 2) F) • MvPolynomial.pderiv 0 +
    (MvPolynomial.C (-6 : F) * MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 2) F) • MvPolynomial.pderiv 1

end SwdAlgebra


