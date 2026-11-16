-- Prove2me | Definitions.Def_IQPForrelation832_SingleQuery_Supplement_RazTal
-- name    : IQPForrelation832_SingleQuery_Supplement_RazTal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:52:48.727631+00:00
-- url     : https://prove2.me/theorems/9c2ef4f1-13cd-4536-ac56-45fe3fb6ed0f
-- title:
--   Concrete truncated-and-rounded Raz–Tal product laws
-- statement:
--   For positive address length $n$, put $N=2^n$ and $\varepsilon=(24\log(2)n)^{-1}$. Sample independent centered real Gaussians $X_a$ of variance $\varepsilon$ and set $Y=H_NX$, where $(H_N)_{ab}=(-1)^{a\cdot b}/\sqrt N$. Truncate each coordinate to $[-1,1]$ and, conditionally independently given $X$, round a truncated value $t$ to $+1$ with probability $(1+t)/2$. The two rounded vectors form a pair $(f,g)$. Its exact finite-law weights are
--   $$
--   D_n(f,g)=\mathbb E_X\prod_a\frac{1+f_a\operatorname{trnc}(X_a)}2\frac{1+g_a\operatorname{trnc}((H_NX)_a)}2,
--   \qquad U_n(f,g)=2^{-2N}.
--   $$
--   The Gaussian expectation is a nonnegative integral of the conditional rounding weights. These integrands lie in $[0,1]$ and are continuous, so the extended integral is finite before conversion to a real number. Product expectations use the product of $m$ such weights, enforcing independent input pairs. The proof's concrete repetition count is $m(n)=147456n^2$. Fixed local block labels are self-delimiting encodings of $(n,i)$; a direct total Boolean oracle can instead use distinct lengths $\langle n,i\rangle+1$ with unused query wires, so it needs no constant-prefix query facility. The zero-dimensional Gaussian parameter has Lean's total default value; all uses of this distribution in the construction theorem have $n\ge1$.
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), pp. 21–24, Definitions 7–8, Lemma 3 proof and Proposition 10 proof. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Supplement_OracleFourier

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery.Supplement

open MeasureTheory ProbabilityTheory

abbrev SignPair (n : ℕ) := (Cube n → Bool) × (Cube n → Bool)

noncomputable def epsilon (n : ℕ) : ℝ := (24 * Real.log 2 * n)⁻¹

/-- Independent centered coordinates of variance epsilon, before truncation and rounding. -/
noncomputable def gaussianInput (n : ℕ) : Measure (Cube n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 (epsilon n).toNNReal)

noncomputable def truncation (t : ℝ) : ℝ := max (-1) (min 1 t)

noncomputable def roundWeight (t : ℝ) (b : Bool) : ℝ :=
  (1 + signValue b * truncation t) / 2

/-- Exact conditional independent rounding, integrated over the actual Gaussian input.
The nonnegative integral has no Bochner nonintegrability default. -/
noncomputable def structuredWeight (n : ℕ) (z : SignPair n) : ℝ :=
  (∫⁻ X : Cube n → ℝ,
    ∏ a : Cube n, ENNReal.ofReal (roundWeight (X a) (z.1 a)) *
      ENNReal.ofReal (roundWeight (realFourier X a) (z.2 a)) ∂gaussianInput n).toReal

noncomputable def uniformWeight (n : ℕ) (_z : SignPair n) : ℝ :=
  ((2 : ℝ) ^ (2 * 2^n))⁻¹

/-- Independent m-fold sampling of input PAIRS. A measurement probability is then averaged
against this law; this does not substitute an expectation-gap hypothesis for a distribution. -/
noncomputable def productExpectation {n m : ℕ} (w : SignPair n → ℝ)
    (p : (Fin m → SignPair n) → ℝ) : ℝ :=
  ∑ z : Fin m → SignPair n, (∏ i, w (z i)) * p z

def repetitionCount (n : ℕ) : ℕ := 147456 * n^2

/-- One fixed, self-delimiting oracle block label, followed by the joint address bit and
then the original n address bits. This encoding is independent of all oracle answers. -/
def blockPrefix (n i : ℕ) : QAlgorithms.Complexity.Str :=
  QAlgorithms.Complexity.encNat n ++ QAlgorithms.Complexity.encNat i

/-- A direct total-oracle implementation can distinguish blocks by address LENGTH, with
extra query wires whose bits O ignores. Cantor pairing is injective and at least n, so
this length leaves n+1 genuine joint-address bits and only polynomially many dummy bits.
No constant prefix wires or oracle-dependent address maps are needed in IQPO. -/
def totalBlockLength (n i : ℕ) : ℕ := Nat.pair n i + 1

/-- Decode the length of a raw total-oracle query into its fixed block indices. -/
def totalBlockIndices (word : QAlgorithms.Complexity.Str) : ℕ × ℕ :=
  Nat.unpair (word.length - 1)

end IQPForrelation832.SingleQuery.Supplement


