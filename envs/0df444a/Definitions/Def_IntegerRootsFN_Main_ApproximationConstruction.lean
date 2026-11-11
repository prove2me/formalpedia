-- Prove2me | Definitions.Def_IntegerRootsFN_Main_ApproximationConstruction
-- name    : IntegerRootsFN_Main_ApproximationConstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:00.842213+00:00
-- url     : https://prove2.me/theorems/42cfa37a-e623-4fae-a0cf-171e9787d548
-- title:
--   Finite shift and inverse-factorization construction
-- statement:
--   The shift uses $R=10d^2$ and circle points $R\exp(2\pi i j/(d+1))$ for $0\le j\le d$. A finite list of represented dyadic samples approximates them to within $1/8$; rounding both coordinates gives Gaussian integer choices. The chosen $q$ maximizes the exact magnitude of $g$ at these choices. Ties are permitted, as in the source.
--
--   For $H(w)=w^dg(q+1/w)$ represented by coefficient reversal, set
--
--   $$P=2b+8d+16+\lceil 2d\log_2(10d^2+2)+\log_2(d+1)\rceil.$$
--
--   A successful construction record contains the finite shift samples, $q$, a common exponent $B$, integer numerator pairs for $w_i$, and represented rational outputs $\beta_i$. Its assertions are conclusions required from the algorithm: root clearance, relative coefficient-norm error at this $P$, every $w_i\ne0$, and $\beta_i=q+1/w_i$. The emitted word contains those actual finite records.
--
--   The predicate describes the source's construction, without asserting any existence or providing an oracle, correctness field or cost estimate as input. The theorem that such records can be computed in the claimed time remains separate.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), pp. 8–10, proof of Lemma 3.3 and Proposition 3.4

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary

set_option autoImplicit false

namespace IntegerRootsFN.Main

noncomputable def roundedGaussian (z : ℂ) : ℤ × ℤ :=
  (⌊z.re + (1 : ℝ) / 2⌋, ⌊z.im + (1 : ℝ) / 2⌋)

noncomputable def circlePoint (d : ℕ) (i : Fin (d + 1)) : ℂ :=
  (10 * (d : ℂ) ^ 2) *
    Complex.exp ((2 * Real.pi * (i.val : ℝ) / ((d : ℝ) + 1) : ℝ) * Complex.I)

/-- Finite dyadic approximations and exact selection, as on pp.8–9. -/
def ShiftChoice (g : Polynomial ℤ) (d : ℕ)
    (samples : Fin (d + 1) → ApproxGKR.GaussDyadic) (q : ℤ × ℤ) : Prop :=
  (∀ i, ‖ApproxGKR.dyadicVal (samples i) - circlePoint d i‖ ≤ (1 : ℝ) / 8) ∧
  ∃ j : Fin (d + 1), q = roundedGaussian (ApproxGKR.dyadicVal (samples j)) ∧
    ∀ i : Fin (d + 1),
      ‖(complexify g).eval (gaussianValue (roundedGaussian (ApproxGKR.dyadicVal (samples i))))‖ ≤
      ‖(complexify g).eval (gaussianValue q)‖

def dyadicWord (z : ApproxGKR.GaussDyadic) : Word :=
  IntMul.joinSep [integerWord z.1, integerWord z.2.1, naturalWord z.2.2]

def samplesWord {d : ℕ} (samples : Fin (d + 1) → ApproxGKR.GaussDyadic) : Word :=
  IntMul.joinSep ((List.ofFn samples).map dyadicWord)

/-- The source construction is a conclusion, never a promise supplied with the input. -/
def ApproximationTrace (g : Polynomial ℤ) (d b : ℕ)
    (samples : Fin (d + 1) → ApproxGKR.GaussDyadic) (q : ℤ × ℤ)
    (B : ℕ) (ws : Fin d → ℤ × ℤ) (β : Fin d → GaussianRational) : Prop :=
  ShiftChoice g d samples q ∧
  (∀ α : ℂ, (complexify g).IsRoot α → 1 < ‖α - gaussianValue q‖) ∧
  normOne (reverseShift g d q -
    factorPolynomial ((reverseShift g d q).coeff d)
      (fun i => ApproxGKR.dyadicVal ((ws i).1, (ws i).2, B))) ≤
    (2 : ℝ) ^ (-(approximationPrecision d b : ℤ)) * normOne (reverseShift g d q) ∧
  (∀ i, ApproxGKR.dyadicVal ((ws i).1, (ws i).2, B) ≠ 0) ∧
  ∀ i, (β i).value = gaussianValue q +
    1 / ApproxGKR.dyadicVal ((ws i).1, (ws i).2, B)

def approximationOutputWord {d : ℕ}
    (samples : Fin (d + 1) → ApproxGKR.GaussDyadic) (q : ℤ × ℤ)
    (B : ℕ) (ws : Fin d → ℤ × ℤ) (β : Fin d → GaussianRational) : Word :=
  IntMul.joinSep [samplesWord samples, gaussianWord q, panOutputWord B (List.ofFn ws),
    rationalsWord (List.ofFn β)]

end IntegerRootsFN.Main


