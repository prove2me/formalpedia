-- Prove2me | Definitions.Def_PolynomialSampling137_OneThird_BooleanSources
-- name    : PolynomialSampling137_OneThird_BooleanSources
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T10:25:32.22055+00:00
-- url     : https://prove2.me/theorems/ebfa880c-7a6b-4c7b-9772-e6827fbbbd65
-- title:
--   Boolean polynomial sources, positive rank, and acceptance gaps
-- statement:
--   An $s$-bit word is an element of $\mathbb F_2^s$. A Boolean function has degree at most $d$ when it is the evaluation of a multilinear polynomial over $\mathbb F_2$ of total degree at most $d$. Its degree-$d$ rank is at most a positive integer $r$ when it is $\Gamma(q_1,\ldots,q_r)$, with arbitrary Boolean $\Gamma$ and degree-at-most-$d$ functions $q_j$; unused arguments pad smaller ranks. Constants are allowed.
--
--   $$A(q)=2^{-s}\sum_{x\in\mathbb F_2^s}q(x),\qquad P_Q(y)=2^{-s}|\{x:Q(x)=y\}|,\qquad M_{p,n}(y)=\prod_i p^{y_i}(1-p)^{1-y_i}.$$
--
--   Boolean values in real expressions are $0$ and $1$. The two gap predicates quantify over every seed length and the indicated function class, asserting $|A(q)-p|\ge\delta$. A real $p$ is non-dyadic when $p\ne a/2^b$ for every integer $a$ and natural $b$. Uniform averages are finite sums divided by carrier cardinality; word spaces are always nonempty, including dimension zero. These definitions encode actual sampler laws, without output independence or a seed-length restriction.
-- source:
--   Yan Zhong, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, §§2.1–2.2, printed pp. 7–8 / PDF pp. 9–10

import Mathlib

noncomputable section

namespace PolynomialSampling137.OneThird

/-- Binary words, including the unique empty word. -/
abbrev Word (s : ℕ) := Fin s → ZMod 2

/-- The real 0/1 value of a binary-field element. -/
def bitReal (b : ZMod 2) : ℝ := if b = 1 then 1 else 0

/-- Uniform finite average. Every carrier used below is nonempty. -/
def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

/-- Boolean degree bounds the unique multilinear polynomial over F₂. -/
def DegreeLE {s : ℕ} (d : ℕ) (q : Word s → ZMod 2) : Prop :=
  ∃ f : MvPolynomial (Fin s) (ZMod 2),
    f.totalDegree ≤ d ∧ (∀ m ∈ f.support, ∀ i, m i ≤ 1) ∧
      ∀ x, MvPolynomial.eval x f = q x

/-- At most r degree-d polynomial inputs to an arbitrary Boolean function.
For r ≥ 1, unused inputs pad representations of smaller positive rank. -/
def RankLE {s : ℕ} (d r : ℕ) (q : Word s → ZMod 2) : Prop :=
  1 ≤ r ∧ ∃ qs : Fin r → Word s → ZMod 2,
    (∀ j, DegreeLE d (qs j)) ∧
      ∃ Γ : Word r → ZMod 2, ∀ x, q x = Γ (fun j => qs j x)

/-- Acceptance probability under the original uniform seed law. -/
def acceptance {s : ℕ} (q : Word s → ZMod 2) : ℝ :=
  uniformAverage (fun x => bitReal (q x))

/-- Uniform-in-seed-length acceptance gap for bounded degree-d rank. -/
def RankGap (d r : ℕ) (p δ : ℝ) : Prop :=
  ∀ (s : ℕ) (q : Word s → ZMod 2), RankLE d r q → δ ≤ |acceptance q - p|

/-- Uniform-in-seed-length acceptance gap for degree at most d. -/
def DegreeGap (d : ℕ) (p δ : ℝ) : Prop :=
  ∀ (s : ℕ) (q : Word s → ZMod 2), DegreeLE d q → δ ≤ |acceptance q - p|

/-- Non-dyadic real parameters; numerator may be any integer. -/
def NonDyadic (p : ℝ) : Prop := ¬ ∃ (a : ℤ) (b : ℕ), p = (a : ℝ) / 2 ^ b

/-- Actual output masses of Q(U_s), computed from fibers, with no free output law. -/
def samplerMass {s n : ℕ} (Q : Word s → Word n) (y : Word n) : ℝ :=
  uniformAverage (fun x => if Q x = y then 1 else 0)

/-- Independent Bernoulli target masses. Valid as a law for p in [0,1]. -/
def bernoulliProductMass (p : ℝ) (n : ℕ) (y : Word n) : ℝ :=
  ∏ i, if y i = 1 then p else 1 - p

end PolynomialSampling137.OneThird


