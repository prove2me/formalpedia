-- Prove2me | Definitions.Def_LinSysAmp_omegaAlg
-- name    : LinSysAmp_omegaAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:11.121979+00:00
-- url     : https://prove2.me/theorems/c9dbe0b4-44f6-4ad1-be42-be7abb3c221d
-- title:
--   $\omega$: the algebraic exponent of matrix multiplication over a field
-- statement:
--   Let $F$ be a field. A **straight-line program** over $F$ is a sequence of gates, each a constant from $F$, an input variable, or the sum, difference or product of two earlier gates. Constants and inputs are free and every other gate costs $1$. Every gate computes a polynomial in the input variables, with coefficients in $F$.
--
--   A program **computes the $n\\times n$ product formally** if, for all $i,k$, some gate computes the polynomial $\\sum_{j}a_{ij}b_{jk}$ in the $2n^2$ variables $a_{ij},b_{jk}$. A real number $\\tau$ is **admissible** if for every $\\varepsilon>0$ there is a constant $C>0$ such that for each $n\\ge1$ some program computes the $n\\times n$ product formally at cost at most $Cn^{\\tau+\\varepsilon}$. The **exponent of matrix multiplication over $F$** is
--   $$
--   \\omega(F)=\\inf\\{\\tau:\\tau\\text{ is admissible}\\}.
--   $$
--
--   This is the quantity $\\omega$ of the paper, and it controls the cost of one low-rank update.
--
--   **Formalization Note** The program type, gates and cost are those of the published `OAI.MatrixMultiplication.Arithmetic`. The published exponent `omega` asks a program to be correct on all matrices over $F$. Over a finite field that is correctness as a function, which is not known to give the bilinear algorithms needed to apply a fixed-size algorithm recursively to blocks. The source's $\\omega$ is the algebraic one, so correctness is required here as an identity of polynomials. Every admissible exponent here is admissible in the published sense.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), §3.2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

open OAI.MatrixMultiplication.Arithmetic

namespace LinSysAmp

/-!
# The algebraic exponent of matrix multiplication over a field

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), §3.2, p.13 (PDF p.15):
"We denote by ω the exponent of matrix multiplication over the field under consideration."

**Formalization Note.** This is the standard exponent of algebraic complexity theory: straight-line
programs over `F` that compute the entries of the product **as polynomials** in the input entries.
It reuses the published program type, gates and cost of `OAI.MatrixMultiplication.Arithmetic`
(constants and inputs free; each `+`, `−`, `×` costs `1`). It differs from the published
`OAI.MatrixMultiplication.Arithmetic.omega` in one respect only, the notion of correctness: the
published `AdmissibleExponent` asks for correctness on all matrices over `F`. Over an infinite field
the two notions agree. Over a finite field, which is the setting of this paper, correctness on all
matrices is correctness as a function, and a program can use `x ^ q = x`. The known passage from a
program to a bilinear algorithm, which the matrix-multiplication literature needs in order to apply a
fixed algorithm recursively to blocks, takes homogeneous components of polynomials and does not apply
to a program that is correct only as a function. The polynomial notion is the source's `ω`.
Every formally admissible exponent is admissible in the published sense.
-/

variable {F Input Register : Type*} [Field F]

/-- The polynomial computed by a gate, given the polynomials of the earlier registers.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.2, p.13 (PDF p.15).) -/
noncomputable def gatePoly (regs : Register → MvPolynomial Input F) :
    Gate F Input Register → MvPolynomial Input F
  | .constant z => MvPolynomial.C z
  | .input i => MvPolynomial.X i
  | .add i j => regs i + regs j
  | .sub i j => regs i - regs j
  | .mul i j => regs i * regs j

/-- The polynomials computed by the registers of a straight-line program.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.2, p.13 (PDF p.15).) -/
noncomputable def programPoly : {r : ℕ} → Program F Input r → Fin r → MvPolynomial Input F
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases (gatePoly (programPoly p) g) (programPoly p)

/-- The algorithm computes the `n × n` product formally: each output register holds the polynomial
`∑ⱼ a_{ij} b_{jk}` in the input variables.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.2, p.13 (PDF p.15).) -/
def ComputesFormally {n : ℕ} (P : MatrixAlgorithm F n n n) : Prop :=
  ∀ i k : Fin n, programPoly P.program (P.output i k) =
    ∑ j : Fin n, MvPolynomial.X (Sum.inl (i, j)) * MvPolynomial.X (Sum.inr (j, k))

/-- `τ` is admissible: positive slack, one uniform constant, and a formally correct program at every
size. (arXiv:2611.04680, version held, sha256 af7a90ac…, §3.2, p.13 (PDF p.15).) -/
def FormalAdmissibleExponent (F : Type*) [Field F] (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n n n,
      ComputesFormally P ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

/-- `ω` over the field `F`: the infimum of the formally admissible exponents.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.2, p.13 (PDF p.15).) -/
noncomputable def omegaAlg (F : Type*) [Field F] : ℝ := sInf {τ : ℝ | FormalAdmissibleExponent F τ}

end LinSysAmp


