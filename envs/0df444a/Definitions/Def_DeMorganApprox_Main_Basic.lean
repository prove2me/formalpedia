-- Prove2me | Definitions.Def_DeMorganApprox_Main_Basic
-- name    : DeMorganApprox_Main_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:28.122745+00:00
-- url     : https://prove2.me/theorems/2af3af15-12b4-4755-a3ae-5d4295f8d7b0
-- title:
--   §3.1 — De Morgan formulas, leaf count, multilinearity and the coefficient ℓ1-norm
-- statement:
--   A **De Morgan formula** over the input variables $x_1,\dots,x_m$ is a binary formula whose internal nodes are $\wedge$ and $\vee$ gates and whose leaves are literals $x_i$ or $\neg x_i$ (negations pushed to the leaves; no constants and no XOR gates). Its **size** $n$ is the number of leaf occurrences, counted with multiplicity, so $n\ge 1$. A formula $\varphi$ computes the Boolean function $\varphi(x)$ obtained by evaluating the literals and gates on $x\in\{0,1\}^m$.
--
--   For a real polynomial $P$ in $x_1,\dots,x_m$, $P$ is **multilinear** if no variable appears with exponent larger than one in any monomial. Its **coefficient ℓ1-norm** in the $\{0,1\}$-monomial basis is
--   $$\|P\|_1=\sum_{T}|p_T|,$$
--   the sum of the absolute values of its coefficients. For a multilinear $P=\sum_{T\subseteq[m]}p_T\prod_{i\in T}x_i$ this is exactly the norm of §3.1.
--
--   These objects fix the statement of the main theorem: the formula, its size $n$, and the two complexity measures (total degree and coefficient ℓ1-norm) of an approximating polynomial.
--
--   **Formalization Note** Inputs are `Fin m → Bool`; a polynomial is evaluated at the 0/1 real point of an input, and a Boolean value is read as the real number $0$ or $1$. The literal `lit i true` is $x_i$ and `lit i false` is $\neg x_i$. `coeffL1` sums over the whole support with no reduction modulo $x_i^2=x_i$, so it is also the "before multilinearization" norm used inside the proof of Lemma 4.1.
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), §3.1 Notation, PDF p. 10 (printed p. 8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf

import Mathlib

namespace DeMorganApprox.Main

/-- De Morgan formulas in negation normal form over the inputs `xᵢ`, `i : Fin m` (§3.1, PDF p. 10):
a leaf is a literal (`lit i true` is `xᵢ`, `lit i false` is `¬xᵢ`), and the gates are binary
`∧` and `∨`. There are no constant leaves. -/
inductive Formula (m : ℕ) : Type where
  | lit (i : Fin m) (b : Bool) : Formula m
  | and (φ ψ : Formula m) : Formula m
  | or (φ ψ : Formula m) : Formula m
  deriving DecidableEq

namespace Formula

variable {m : ℕ}

/-- The size of a formula: the number of leaf occurrences, counted with multiplicity. -/
def leaves : Formula m → ℕ
  | lit _ _ => 1
  | and φ ψ => φ.leaves + ψ.leaves
  | or φ ψ => φ.leaves + ψ.leaves

/-- The Boolean function computed by a formula. -/
def eval : Formula m → (Fin m → Bool) → Bool
  | lit i b, x => if b then x i else !x i
  | and φ ψ, x => φ.eval x && ψ.eval x
  | or φ ψ, x => φ.eval x || ψ.eval x

/-- Whether the formula is a single leaf. -/
def isLeaf : Formula m → Bool
  | lit _ _ => true
  | _ => false

end Formula

/-- The 0/1 real point of a Boolean input. -/
def boolPoint {m : ℕ} (x : Fin m → Bool) : Fin m → ℝ := fun i => if x i then 1 else 0

/-- The real value `0` or `1` of a Boolean. -/
def boolVal (b : Bool) : ℝ := if b then 1 else 0

/-- A polynomial is multilinear when every variable has exponent at most one in every monomial
of its support. -/
def IsMultilinear {σ : Type} (P : MvPolynomial σ ℝ) : Prop :=
  ∀ s ∈ P.support, ∀ i, s i ≤ 1

/-- The coefficient ℓ1-norm: the sum of the absolute values of all coefficients, in the monomial
basis, with no reduction modulo `xᵢ² = xᵢ`. -/
noncomputable def coeffL1 {σ : Type} (P : MvPolynomial σ ℝ) : ℝ :=
  ∑ s ∈ P.support, |P.coeff s|

end DeMorganApprox.Main


