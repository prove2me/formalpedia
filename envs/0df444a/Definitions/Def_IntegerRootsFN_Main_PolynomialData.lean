-- Prove2me | Definitions.Def_IntegerRootsFN_Main_PolynomialData
-- name    : IntegerRootsFN_Main_PolynomialData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:04.77176+00:00
-- url     : https://prove2.me/theorems/8c5d2214-308b-44f0-ab5e-e21426c132bc
-- title:
--   Polynomial promises, truncation, norms and exact root output
-- statement:
--   For positive integers $n,b$, a valid input is an integer polynomial of exact degree $n$ with $a_n\ne0$ and $|a_j|<2^b$ for every coefficient. Its complexification uses the canonical embedding. With $d=\min(n,b)$ the actual truncation is
--
--   $$g(x)=\sum_{j=0}^{d}a_{n-d+j}x^j.$$
--
--   The maximum coefficient norm is $\|p\|_\infty=\max_j|p_j|$, with zero value on the zero polynomial. The other coefficient norms are $\|p\|_1=\sum_j|p_j|$ and $\|p\|_2=(\sum_j|p_j|^2)^{1/2}$. A common-dyadic polynomial has a finite dense list of Gaussian integer numerators and one nonnegative denominator exponent. A family indexed by $\mathrm{Fin}\ d$ lists roots with multiplicity precisely when the polynomial equals its leading coefficient times the product of the corresponding linear factors. Coverage means every root lies at distance strictly less than $1/8$ from some family member.
--
--   The perturbation threshold, logarithmic size bound, shift, coefficient reversal, reverse transformation and precision are exactly those on pp.6 and 9–10. In particular, $H(w)=\sum_{j=0}^dc_jw^{d-j}$ when $g(q+x)=\sum c_jx^j$. Nearest-integer rounding uses $\lfloor t+1/2\rfloor$, and candidate shifts are $-3,\ldots,3$ together with $-1,0,1$. Exact filtering retains precisely the zeros and removes repetitions. A root output is a repetition-free list $R$ satisfying
--
--   $$\forall r\in\mathbb Z,\quad r\in R\ \Longleftrightarrow\ f(r)=0.$$
--
--   These definitions contain no root-existence or runtime assumptions. Empty support gives zero norms; constants have their usual coefficient norms. Truncation is used only where the positive-degree promise makes its natural subtraction exact.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), pp. 2–3, §1.1; pp. 5–6, §2; pp. 9–11, §3.2

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Representations

set_option autoImplicit false

namespace IntegerRootsFN.Main

/-- The positive-degree, strict coefficient-height promise of p.2. -/
def Valid (f : Polynomial ℤ) (n b : ℕ) : Prop :=
  1 ≤ n ∧ 1 ≤ b ∧ f.natDegree = n ∧ f.coeff n ≠ 0 ∧
    ∀ j : ℕ, |f.coeff j| < (2 : ℤ) ^ b

noncomputable def complexify (f : Polynomial ℤ) : Polynomial ℂ :=
  f.map (Int.castRingHom ℂ)

noncomputable def normOne (p : Polynomial ℂ) : ℝ :=
  ∑ j ∈ p.support, ‖p.coeff j‖

noncomputable def normTwo (p : Polynomial ℂ) : ℝ :=
  Real.sqrt (∑ j ∈ p.support, ‖p.coeff j‖ ^ 2)

/-- Maximum absolute coefficient, with value zero for the zero polynomial. -/
noncomputable def normInfinity (p : Polynomial ℂ) : ℝ :=
  (List.ofFn fun j : Fin (p.natDegree + 1) => ‖p.coeff j.val‖).foldl max 0

/-- The leading `min(n,b)+1` coefficients, with the source's order. -/
noncomputable def truncate (f : Polynomial ℤ) (n b : ℕ) : Polynomial ℤ :=
  let d := min n b
  ∑ j ∈ Finset.range (d + 1), Polynomial.monomial j (f.coeff (n - d + j))

/-- A common denominator is represented by one exponent and a dense numerator list. -/
structure DyadicPolynomial where
  exponent : ℕ
  numerators : List (ℤ × ℤ)

noncomputable def DyadicPolynomial.value (a : DyadicPolynomial) : Polynomial ℂ :=
  ∑ j ∈ Finset.range a.numerators.length,
    Polynomial.monomial j
      (ApproxGKR.dyadicVal ((a.numerators.getD j (0, 0)).1,
        (a.numerators.getD j (0, 0)).2, a.exponent))

noncomputable def logRootSize {d : ℕ} (β : Fin d → ℂ) : ℝ :=
  ∑ i, logTwo (max 1 ‖β i‖)

noncomputable def factorPolynomial {d : ℕ} (c : ℂ) (β : Fin d → ℂ) : Polynomial ℂ :=
  Polynomial.C c * ∏ i, (Polynomial.X - Polynomial.C (β i))

/-- Equality to the full product pins multiplicities, not just the distinct root set. -/
def ListsRoots {d : ℕ} (p : Polynomial ℂ) (β : Fin d → ℂ) : Prop :=
  p = factorPolynomial p.leadingCoeff β

def CoversRoots {d : ℕ} (p : Polynomial ℂ) (β : Fin d → ℂ) : Prop :=
  ∀ α : ℂ, p.IsRoot α → ∃ i : Fin d, ‖α - β i‖ < (1 : ℝ) / 8

noncomputable def perturbationThreshold (d b : ℕ) : ℝ :=
  1 / (8 * 9 ^ d * ((2 : ℝ) ^ b * Real.sqrt ((d : ℝ) + 1) + 1))

noncomputable def rootSizeBound (d b : ℕ) : ℝ :=
  (b : ℝ) + (1 : ℝ) / 2 * logTwo ((d : ℝ) + 1) + 2

noncomputable def gaussianValue (q : ℤ × ℤ) : ℂ :=
  (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

noncomputable def shiftPolynomial (g : Polynomial ℤ) (q : ℤ × ℤ) : Polynomial ℂ :=
  (complexify g).comp (Polynomial.C (gaussianValue q) + Polynomial.X)

/-- Actual coefficient reversal, including the prescribed degree slot. -/
noncomputable def reverseShift (g : Polynomial ℤ) (d : ℕ) (q : ℤ × ℤ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (d + 1),
    Polynomial.monomial (d - j) ((shiftPolynomial g q).coeff j)

noncomputable def backTransform (E : Polynomial ℂ) (d : ℕ) (q : ℤ × ℤ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (d + 1),
    Polynomial.C (E.coeff j) * (Polynomial.X - Polynomial.C (gaussianValue q)) ^ (d - j)

noncomputable def approximationPrecision (d b : ℕ) : ℕ :=
  2 * b + 8 * d + 16 +
    ⌈2 * (d : ℝ) * logTwo (10 * (d : ℝ) ^ 2 + 2) + logTwo ((d : ℝ) + 1)⌉₊

noncomputable def roundedCandidates {d : ℕ} (β : Fin d → ℂ) : List ℤ :=
  ([-1, 0, 1] ++ (List.ofFn fun i : Fin d =>
    (List.range 7).map fun j => ⌊(β i).re + (1 : ℝ) / 2⌋ + (j : ℤ) - 3).flatten).eraseDups

def exactZeros (f : Polynomial ℤ) (cs : List ℤ) : List ℤ :=
  (cs.filter fun c => f.eval c = 0).eraseDups

def RootOutput (f : Polynomial ℤ) (rs : List ℤ) : Prop :=
  rs.Nodup ∧ ∀ r : ℤ, r ∈ rs ↔ f.IsRoot r

end IntegerRootsFN.Main


