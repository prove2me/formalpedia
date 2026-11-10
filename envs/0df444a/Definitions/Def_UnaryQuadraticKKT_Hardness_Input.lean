-- Prove2me | Definitions.Def_UnaryQuadraticKKT_Hardness_Input
-- name    : UnaryQuadraticKKT_Hardness_Input
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:43:43.081777+00:00
-- url     : https://prove2.me/theorems/9ea6d044-0e24-42ae-b5c0-4f2152214d74
-- title:
--   Unary rational input codes and exact Quadratic-KKT search
-- statement:
--   Let $n\ge1$ and let $P(x)=\sum_iq_{ii}x_i^2+\sum_{i<j}q_{ij}x_ix_j+\sum_ic_ix_i$ have arbitrary signed rational coefficients. The public symmetric matrix representation has $Q_{ii}=2q_{ii}$ and $Q_{ij}=Q_{ji}=q_{ij}$ for $i<j$. No definiteness or normalization condition is imposed.
--
--   The unary code charges $n$ in unary, then lists the upper-triangular monomial coefficients and the linear coefficients, retaining zeros. Each reduced rational $a/b$ uses a sign bit and the unary magnitudes $|a|$ and $b>0$, each terminated by a zero bit. Thus even zero entries and the dimension consume input length. This is an explicit dense list, polynomially interconvertible with the source's explicit monomial list when dimension is charged.
--
--   Writing $U$ for the search problem, its accepted answers are exactly the public binary codes of rational vectors $x\in[0,1]^n$ satisfying
--   $$
--   x_i=0\Rightarrow\partial_iP(x)\ge0,\qquad 0<x_i<1\Rightarrow\partial_iP(x)=0,\qquad x_i=1\Rightarrow\partial_iP(x)\le0.
--   $$
--   The integer subfamily $U_{\mathbb Z}$ restricts valid inputs to coefficients with denominator one and uses the same answer relation. Answers have no fixed length restriction here; membership will assert a sufficient uniform polynomial length bound separately. The definitions add the paper-specific unary input convention to the public quadratic, exact KKT and search-reduction interfaces.
--
--   **Formalization Note** Unary naturals are $1^a0$. Source slots are the upper triangle followed by linear terms. Malformed bitstrings are invalid rather than silently decoded to a default instance.
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Definitions 3.1–3.2, Equations (2)–(3), p.4, and Section 4.5, pp.10–11. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_CardinalMatching_SearchReduces

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness
open NetworkEquilibriumCLS.LinearNash

/-- Source Eq. (2) slots: a linear term, or a pair in the upper triangle. -/
inductive Monomial (n : ℕ) where
  | linear : Fin n → Monomial n
  | quadratic : Fin n → Fin n → Monomial n
  deriving DecidableEq

def slots (n : ℕ) : List (Monomial n) :=
  ((List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => i ≤ j).map (Monomial.quadratic i)) ++
  (List.finRange n).map Monomial.linear

/-- The public matrix convention is ½ xᵀQx + cᵀx: q_ii = Q_ii/2, q_ij = Q_ij. -/
def coefficient {n : ℕ} (p : Quadratic n) : Monomial n → ℚ
  | .linear i => p.c i
  | .quadratic i j => if i = j then p.Q i i / 2 else p.Q i j

def factors {n : ℕ} : Monomial n → Option (Fin n) × Option (Fin n)
  | .linear i => (some i, none)
  | .quadratic i j => (some i, some j)

def factorValue {n : ℕ} (a : Option (Fin n)) (x : Fin n → ℝ) : ℝ :=
  a.elim 1 x

/-- Unary natural with an explicit terminating delimiter; zero is encoded as [false]. -/
def unaryNat (a : ℕ) : List Bool := List.replicate a true ++ [false]

def unaryRat (a : ℚ) : List Bool :=
  (a.num < 0) :: (unaryNat a.num.natAbs ++ unaryNat a.den)

/-- Dense upper-triangular monomial list, including zeros. Dimension is charged in unary. -/
def unaryCode {n : ℕ} (p : Quadratic n) : List Bool :=
  unaryNat n ++ (slots n).flatMap (fun t => unaryRat (coefficient p t))

def IntegerCoefficients {n : ℕ} (p : Quadratic n) : Prop :=
  ∀ t ∈ slots n, (coefficient p t).den = 1

def unarySearch : SearchProblem where
  valid a := ∃ n, 0 < n ∧ ∃ p : Quadratic n, unaryCode p = a
  answer a b := ∃ n, 0 < n ∧ ∃ p : Quadratic n, unaryCode p = a ∧
    ∃ x : Fin n → ℚ, encVector x = b ∧ QuadraticKKT p (fun i => (x i : ℝ))

/-- The reduction's output subfamily has integer monomial coefficients. -/
def unaryIntegerSearch : SearchProblem where
  valid a := ∃ n, 0 < n ∧ ∃ p : Quadratic n, IntegerCoefficients p ∧ unaryCode p = a
  answer a b := unarySearch.answer a b

end UnaryQuadraticKKT.Hardness


