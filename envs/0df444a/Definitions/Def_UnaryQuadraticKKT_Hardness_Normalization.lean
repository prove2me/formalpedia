-- Prove2me | Definitions.Def_UnaryQuadraticKKT_Hardness_Normalization
-- name    : UnaryQuadraticKKT_Hardness_Normalization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:44:42.918381+00:00
-- url     : https://prove2.me/theorems/f8ec6558-1309-4243-8e3d-e501949fee77
-- title:
--   Computed normalization and signed binary coefficient expansion
-- statement:
--   For a rational quadratic $P$, let $A$ be the least common multiple of the positive reduced denominators of all its monomial coefficients. Set $P'=AP$, $M=\max(1,\max|\operatorname{coeff}(P')|)$, $L=\lfloor\log_2 M\rfloor+1$ and
--   $$
--   \widetilde P=\frac{A}{2^L}P.
--   $$
--   These quantities are computed from $P$. The sign of a cleared coefficient $z$ is $-1$ if $z<0$ and $+1$ otherwise. Its digit $\delta_k$ is bit $L-k$ of $|z|$. Enumerating only nonzero digits constructs the actual dyadic terms $s_r2^{-k_r}p_r(x)q_r(x)$, where each factor is one or an original coordinate. Squares use the same coordinate twice and a linear term uses one constant factor.
--
--   The zero polynomial has $A=M=L=1$ and no dyadic terms. Thus a zero input remains in scope without inventing an auxiliary variable. These definitions fix the normalization and factor map used throughout the chain construction; the KKT equivalence and expansion identities are separate theorem targets.
--
--   **Formalization Note** $L$ is the binary bit length of $M$, avoiding real logarithms on degenerate inputs. The LCM fold starts at one. Natural subtraction occurs only in $L-k$ with $1\le k\le L$.
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Section 4.1, Lemma 4.2 and Equations (4)–(5), pp.5–6. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Input

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness
open NetworkEquilibriumCLS.LinearNash

/-- Computed from reduced denominators, with lcm of an empty list equal to 1. -/
def denominatorLCM {n : ℕ} (p : Quadratic n) : ℕ :=
  ((slots n).map fun t => (coefficient p t).den).foldl Nat.lcm 1

def clearedCoefficient {n : ℕ} (p : Quadratic n) (t : Monomial n) : ℤ :=
  ((denominatorLCM p : ℚ) * coefficient p t).num

def maximumMagnitude {n : ℕ} (p : Quadratic n) : ℕ :=
  ((slots n).map fun t => (clearedCoefficient p t).natAbs).foldl max 1

/-- M ≥ 1, so bit length is exactly floor(log₂ M)+1, also for the zero polynomial. -/
def normalizationLength {n : ℕ} (p : Quadratic n) : ℕ := (maximumMagnitude p).bits.length

def normalizationScale {n : ℕ} (p : Quadratic n) : ℚ :=
  (denominatorLCM p : ℚ) / 2 ^ normalizationLength p

def normalized {n : ℕ} (p : Quadratic n) : Quadratic n where
  Q i j := normalizationScale p * p.Q i j
  c i := normalizationScale p * p.c i
  symmetric i j := by rw [p.symmetric i j]

def coefficientSign {n : ℕ} (p : Quadratic n) (t : Monomial n) : ℤ :=
  if clearedCoefficient p t < 0 then -1 else 1

/-- j = 0 represents k = 1. Natural subtraction is used only for this bounded bit index. -/
def coefficientBit {n : ℕ} (p : Quadratic n) (t : Monomial n)
    (j : Fin (normalizationLength p)) : Bool :=
  (clearedCoefficient p t).natAbs.testBit (normalizationLength p - (j.val + 1))

structure DyadicTerm (n : ℕ) where
  sign : ℤ
  exponent : ℕ
  left : Option (Fin n)
  right : Option (Fin n)

/-- Actual signed binary expansion. Zero bits produce no gadgets; R may equal zero. -/
def dyadicTerms {n : ℕ} (p : Quadratic n) : List (DyadicTerm n) :=
  (slots n).flatMap fun t =>
    ((List.finRange (normalizationLength p)).filter fun j => coefficientBit p t j).map fun j =>
      { sign := coefficientSign p t, exponent := j.val + 1,
        left := (factors t).1, right := (factors t).2 }

noncomputable def dyadicValue {n : ℕ} (t : DyadicTerm n) (x : Fin n → ℝ) : ℝ :=
  (t.sign : ℝ) * (2 : ℝ) ^ (-(t.exponent : ℤ)) *
    factorValue t.left x * factorValue t.right x

end UnaryQuadraticKKT.Hardness


