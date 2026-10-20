-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:00:10.309753+00:00
-- url     : https://prove2.me/theorems/87b4ef61-3ec0-4a8f-96bb-3f9d74c2873a
-- title:
--   Coefficient blocks and the remainder modulo X^m + 1
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Coefficient polynomial.** For a coefficient function $c:\mathbb N\to R$ and $n\in\mathbb N$, the polynomial $\sum_{i<n}c_iX^i$ built from the first $n$ coefficients.
--   2. **Dyadic remainder.** For $m\in\mathbb N$, the polynomial
--   $$
--   \sum_{i<m}\bigl(c_i-c_{i+m}\bigr)X^i,
--   $$
--   which subtracts the upper block of coefficients from the lower one. It is the remainder of $\sum_{i<2m}c_iX^i$ modulo $X^m+1$, since $X^m\equiv-1$; its coefficient of $X^j$ for $j<m$ is $c_j-c_{j+m}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/DyadicRemainder.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/DyadicRemainder.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_PeriodicModFour
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation__EvenBarker

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

universe uR

/-!
# Paired coefficients in a dyadic cyclotomic remainder

Reducing a polynomial of length `2 * m` modulo `X ^ m + 1` subtracts
the upper block of coefficients from the lower block. The construction
and the coefficient formulas work over every commutative ring.
-/

noncomputable section

namespace CirculantHadamard.DyadicRemainder

open Polynomial Finset

variable {R : Type uR} [CommRing R]

/-- The polynomial with the first `n` entries of a coefficient function. -/
def coefficientPolynomial (n : ℕ) (c : ℕ → R) : R[X] :=
  ∑ i ∈ range n, monomial i (c i)

/-- The difference between coefficient blocks at distance `m`. -/
def remainder (m : ℕ) (c : ℕ → R) : R[X] :=
  coefficientPolynomial m (fun i => c i - c (i + m))

@[simp]
theorem coefficientPolynomial_coeff (n : ℕ) (c : ℕ → R) (j : ℕ) :
    (coefficientPolynomial n c).coeff j = if j < n then c j else 0 := by
  classical
  simp [coefficientPolynomial, coeff_monomial]

@[simp]
theorem remainder_coeff (m : ℕ) (c : ℕ → R) (j : ℕ) (hj : j < m) :
    (remainder m c).coeff j = c j - c (j + m) := by
  simp only [remainder, coefficientPolynomial_coeff, ite_eq_left hj]

end CirculantHadamard.DyadicRemainder

end

end OAI


