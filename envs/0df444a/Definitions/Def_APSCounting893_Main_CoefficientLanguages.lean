-- Prove2me | Definitions.Def_APSCounting893_Main_CoefficientLanguages
-- name    : APSCounting893_Main_CoefficientLanguages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:25:09.319264+00:00
-- url     : https://prove2.me/theorems/0e67884d-355b-4d8e-9e8b-84bcdc464d1b
-- title:
--   Uniform coefficient representations and trailing-zero languages
-- statement:
--   A rational coefficient representation assigns each encoded family input $x$ and exponent vector $e$ an integer numerator $a_{x,e}$ and strictly positive natural denominator $b_{x,e}$, with $[X^e]R_x=a_{x,e}/b_{x,e}$. Reduction to lowest terms is not required. Bit queries specify numerator sign, numerator magnitude or denominator and a binary bit position. The family word is prefixed by its binary length before the exponent, part and bit-position codes, so distinct requests decode uniquely.
--
--   A single pair of constants bounds every family degree and representation bit length by $2^{c(|x|+1)^d}$. For fixed $k$, the tested language is
--
--   $$\{x:(\mathrm{TC}_{t_k}\cdots\mathrm{TC}_{t_1}R_x)(0)=0\}.$$
--
--   Parameter substitution preserves the other polynomial variables and is defined over every field extension of $\mathbb Q$. These interfaces do not assume a vanishing oracle or permit the complexity level to depend on the input.
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), §§6.2–6.3; Lemmas 6.2, 6.5, p. 24, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Resultant
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_CircuitInputs

set_option autoImplicit false

namespace APSCounting893.Main

/-- The variables in the result of parameter substitution are t₁,…,tₖ,T. -/
noncomputable def specializeParameters {K : Type} [Field K] [Algebra ℚ K]
    {s k : ℕ} (theta : Fin s → K)
    (R : MvPolynomial (Fin (s + (k + 1))) ℚ) : MvPolynomial (Fin (k + 1)) K :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap ℚ K)) (Fin.addCases (fun i => MvPolynomial.C (theta i)) MvPolynomial.X) R

/-- Numerator and denominator need not be reduced, and denominators are strictly positive. -/
abbrev CoefficientRepresentation (k : ℕ) := Word → (Fin (k + 1) →₀ ℕ) → ℤ × ℕ

inductive CoefficientPart where
  | sign | numerator | denominator
  deriving DecidableEq

def CoefficientPart.encode : CoefficientPart → Word
  | .sign => [false, false]
  | .numerator => [false, true]
  | .denominator => [true]

def representationBit (a : ℤ × ℕ) (part : CoefficientPart) (q : ℕ) : Bool :=
  match part with
  | .sign => decide (a.1 < 0)
  | .numerator => a.1.natAbs.testBit q
  | .denominator => a.2.testBit q

def coefficientQuery {k : ℕ} (x : Word) (e : Fin (k + 1) →₀ ℕ)
    (part : CoefficientPart) (q : ℕ) : Word :=
  encodeNat x.length ++ x ++ encodeList encodeNat (List.ofFn (fun i => e i)) ++
    part.encode ++ encodeNat q

def CoefficientBitLanguage {k : ℕ} (rho : CoefficientRepresentation k) : Language :=
  fun w => ∃ (x : Word) (e : Fin (k + 1) →₀ ℕ) (part : CoefficientPart) (q : ℕ),
    w = coefficientQuery x e part q ∧ representationBit (rho x e) part q = true

noncomputable def RepresentsPolynomialFamily {k : ℕ}
    (R : Word → MvPolynomial (Fin (k + 1)) ℚ) (rho : CoefficientRepresentation k) : Prop :=
  ∀ x e, 0 < (rho x e).2 ∧ (R x).coeff e = (rho x e).1 / ((rho x e).2 : ℚ)

/-- A single polynomial bounds degrees and representation bit lengths for every family input. -/
noncomputable def SinglyExponentialFamily {k : ℕ}
    (R : Word → MvPolynomial (Fin (k + 1)) ℚ) (rho : CoefficientRepresentation k) : Prop :=
  ∃ c d : ℕ, ∀ x : Word,
    (R x).totalDegree ≤ 2 ^ polyBound c d x.length ∧
    ∀ e, (rho x e).1.natAbs.bits.length ≤ 2 ^ polyBound c d x.length ∧
      (rho x e).2.bits.length ≤ 2 ^ polyBound c d x.length

noncomputable def TrailingZeroLanguage {k : ℕ}
    (R : Word → MvPolynomial (Fin (k + 1)) ℚ) : Language :=
  fun x => MvPolynomial.eval (fun _ => (0 : ℚ))
    (nestedTrailing (List.ofFn (fun i : Fin k => i.castSucc)) (R x)) = 0

end APSCounting893.Main


