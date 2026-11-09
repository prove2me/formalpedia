-- Prove2me | Definitions.Def_DetPermanentApprox_Main_Numerical
-- name    : DetPermanentApprox_Main_Numerical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:30:06.400889+00:00
-- url     : https://prove2.me/theorems/d5ac85c3-759c-4cea-848c-7c8fad03f632
-- title:
--   Concrete dyadic routines and the projected iteration
-- statement:
--   The exponential routine is the rational Taylor sum through $8B+Q+4$, decreased by $2^{-(Q+2)}$, clipped below by zero, and rounded downward to the $2^{-(Q+1)}$ grid. The Turing input encoding is binary for the reduced rational argument and unary for $B,Q$, so polynomial encoded time is the source bound polynomial in $B,Q,\ell(x)$.
--
--   The distinct support monomials of the actual polynomial $U$ supply coefficients $a_j,b_j$, count $S$, and bounds $H_U,D_U$ from Definition A.4. The accuracy parameters of Definition A.6 use repeated-halving precision, equivalent on valid inputs to the displayed base-two logarithmic ceilings. Degree estimates, both rational gradient branches, rounded gradients, objective estimates, clipped iterates, executed-round count, and the recorded minimum are explicit functions. Vertex ties choose the first row vertex, then the first column vertex. The ideal gradients are full ambient derivatives evaluated at those iterates. No accuracy inequality or nonempty-recorded-set assertion is included in the input data.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Appendix A, pp. 24–30, Algorithms 2 and Definitions A.4, A.6 (PDF pp. 24–30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Parameters
import Definitions.Def_OnlineCRS_Combine_encRat

open scoped BigOperators

namespace DetPermanentApprox.Main

/-- Appendix A.3's explicit Taylor sum followed by downward dyadic rounding.
Floor is a mathematical specification of the finite binary-search rounding, not
an instruction in Program; its implementation and bit cost are theorem A.3. -/
def expApprox (x : ℚ) (B Q : ℕ) : ℚ :=
  let N := 8 * B + Q + 4
  let A := ∑ j ∈ Finset.range (N + 1), x ^ j / (j.factorial : ℚ)
  let a := max 0 (A - 1 / (2 : ℚ) ^ (Q + 2))
  (⌊a * (2 : ℚ) ^ (Q + 1)⌋ : ℚ) / (2 : ℚ) ^ (Q + 1)

/-- B and Q are unary because the source's bit bound is polynomial in their
values, while x uses the published reduced binary-rational encoding. -/
def exponentialInputEncoding (I : ℚ × ℕ × ℕ) : List OnlineCRS.Combine.Sym :=
  OnlineCRS.Combine.encRat I.1 ++ [3] ++ List.replicate I.2.1 1 ++ [3] ++
    List.replicate I.2.2 1

def exponentialOutput (I : ℚ × ℕ × ℕ) : ℚ := expApprox I.1 I.2.1 I.2.2

noncomputable def matrixDegree (s : ℕ) : ℕ :=
  truncationDegree (degreeCutoff s) (eta s : ℝ)

abbrev Monomial {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (s : ℕ) :=
  {γ // γ ∈ (matrixSurrogate C s).support}

noncomputable instance monomialFintype {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (s : ℕ) :
    Fintype (Monomial C s) := Fintype.ofFinite _

noncomputable def monomialCount {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (s : ℕ) : ℕ :=
  Fintype.card (Monomial C s)

noncomputable def coefficientA {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (s : ℕ)
    (j : Monomial C s) : ℚ :=
  (matrixSurrogate C s).coeff j.val *
    ∏ e : Support (realMatrix C), C e.val.1 e.val.2 ^ j.val e

open Classical in
noncomputable def coefficientB {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (s : ℕ)
    (j : Monomial C s) (v : Vertex n) : ℕ :=
  ∑ e : Support (realMatrix C), if Incident (supportGraph (realMatrix C)) v e then j.val e else 0

noncomputable def coefficientHeight (n s : ℕ) : ℕ :=
  matrixDegree s * (2 * (n ^ 2 + 1)) ^ matrixDegree s

noncomputable def denominatorBound (s : ℕ) : ℕ :=
  let m := matrixDegree s
  let K := ⌊degreeCutoff s⌋₊
  m.factorial * (4 * K) ^ m * (4 * K + 1) ^ m * (8 * K + 1) ^ m

def epsilonZero (n p s : ℕ) : ℚ := eta s / (64 * (n : ℚ) ^ 2 * boxRadius n p s)
def degreeAccuracy (n p s : ℕ) : ℚ := degreeCutoff s * epsilonZero n p s / (64 * n)

noncomputable def objectiveAccuracy {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (p s : ℕ) : ℚ :=
  epsilonZero n p s / (2 * matrixDegree s * monomialCount C s * coefficientHeight n s)

/-- Repeated-halving precision: the least nonnegative q with 2^-q ≤ x.
For positive x this equals max(0,ceil(log₂(1/x))). For x ≤ 0 its value is 0;
only positive accuracies occur under RoundedData and the source parameters. -/
noncomputable def dyadicPrecision (x : ℚ) : ℕ := sInf {q : ℕ | 1 / (2 : ℚ) ^ q ≤ x}

noncomputable def approximateEdgeExp {n : ℕ} (_C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (θ : Vertex n → ℚ) (i j : Fin n) : ℚ :=
  expApprox (θ (Sum.inl i) + θ (Sum.inr j))
    (max 1 ⌈2 * boxRadius n p s⌉₊) (dyadicPrecision (degreeAccuracy n p s))

noncomputable def estimatedDegree {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (θ : Vertex n → ℚ) (v : Vertex n) : ℚ :=
  match v with
    | .inl i => ∑ j, C i j * approximateEdgeExp C p s θ i j
    | .inr j => ∑ i, C i j * approximateEdgeExp C p s θ i j

noncomputable def correctionVertex {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (θ : Vertex n → ℚ) : Option (Vertex n) :=
  ((List.ofFn fun i : Fin n => Sum.inl i) ++ (List.ofFn fun j : Fin n => Sum.inr j)).find?
    (fun v => decide (3 * degreeCutoff s / 8 < estimatedDegree C p s θ v))

noncomputable def monomialDot {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (s : ℕ)
    (j : Monomial C s) (θ : Vertex n → ℚ) : ℚ :=
  ∑ v, (coefficientB C s j v : ℚ) * θ v

noncomputable def estimatedMonomialExp {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (θ : Vertex n → ℚ) (j : Monomial C s) : ℚ :=
  expApprox (monomialDot C s j θ)
    (max 1 ⌈2 * matrixDegree s * boxRadius n p s⌉₊)
    (dyadicPrecision (objectiveAccuracy C p s))

noncomputable def estimatedObjective {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (θ : Vertex n → ℚ) : ℚ :=
  (∑ j : Monomial C s, coefficientA C s j * estimatedMonomialExp C p s θ j) -
    targetMarginal s * ∑ v, θ v + eta s / 4

noncomputable def rationalGradient {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (θ : Vertex n → ℚ) : Vertex n → ℚ :=
  match correctionVertex C p s θ with
  | none => fun v => (∑ j : Monomial C s,
      coefficientA C s j * coefficientB C s j v * estimatedMonomialExp C p s θ j) - targetMarginal s
  | some v => fun z =>
      (∑ i : Fin n, ∑ j : Fin n,
        (if v = Sum.inl i ∨ v = Sum.inr j then
          C i j * approximateEdgeExp C p s θ i j *
            (if z = Sum.inl i ∨ z = Sum.inr j then 1 else 0) else 0)) /
        estimatedDegree C p s θ v

noncomputable def roundedGradient {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (θ : Vertex n → ℚ) : Vertex n → ℚ :=
  let P := dyadicPrecision (epsilonZero n p s)
  fun v => (⌊rationalGradient C p s θ v * (2 : ℚ) ^ (P + 1) + 1 / 2⌋ : ℚ) /
    (2 : ℚ) ^ (P + 1)

noncomputable def iterateTheta {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (p s : ℕ) :
    ℕ → (Vertex n → ℚ)
  | 0 => 0
  | k + 1 =>
    let θ := iterateTheta C p s k
    clip n p s (fun v => θ v - stepSize n s * roundedGradient C p s θ v)

noncomputable def idealGradient {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (p s k : ℕ) :
    Vertex n → ℝ :=
  let θ := iterateTheta C p s k
  match correctionVertex C p s θ with
  | none => fun v => partialR (surrogateObjective C s) (fun v => (θ v : ℝ)) v
  | some v => fun z => partialR (fun x => Real.log (vertexDegree C x v)) (fun v => (θ v : ℝ)) z

noncomputable def iterationCount (n p s : ℕ) : ℕ :=
  1 + ⌈4 * (n : ℚ) * boxRadius n p s ^ 2 / (stepSize n s * eta s)⌉₊

open Classical in
noncomputable def recordedRounds {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (p s : ℕ) : Finset ℕ :=
  (Finset.range (iterationCount n p s)).filter fun k =>
    correctionVertex C p s (iterateTheta C p s k) = none

open Classical in
noncomputable def minimizedValue {n : ℕ} (C : Matrix (Fin n) (Fin n) ℚ) (p s : ℕ) : ℚ :=
  let values := (recordedRounds C p s).image fun k => estimatedObjective C p s (iterateTheta C p s k)
  if h : values.Nonempty then values.min' h else 0

end DetPermanentApprox.Main


