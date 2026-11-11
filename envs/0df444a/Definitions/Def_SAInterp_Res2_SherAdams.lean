-- Prove2me | Definitions.Def_SAInterp_Res2_SherAdams
-- name    : SAInterp_Res2_SherAdams
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:35:41.995204+00:00
-- url     : https://prove2.me/theorems/a93c7c78-5821-43db-aac5-5a3db845b562
-- title:
--   Sherali-Adams and R-Nullstellensatz refutations in the dual-variable encoding, their degree and size; designs and pseudoexpectations (Definitions 2.1–2.5)
-- statement:
--   Let $F$ be a CNF over a finite set $\alpha$ of boolean variables $x_i$ (literals, clauses, CNFs and unsatisfiability as in the published definition `MultiplierAssoc206_Resolution_CNF`: a clause is a finite set of literals, a CNF a finite set of clauses). For each variable $x_i$ introduce a **dual variable** $\bar x_i$ and work in $\mathbb R[x,\bar x]$. A **conjunction** $C$ (a finite set of literals) is encoded by the monomial $\prod_{i\in P}x_i\prod_{j\in N}\bar x_j$; its degree $\deg C$ is its number of literals. For a clause $C$, $\bar C$ is the conjunction of the negations of its literals. $C \Rightarrow \bar C_i$ means that every assignment satisfying $C$ falsifies the clause $C_i$.
--
--   An **$\mathbb R$-Nullstellensatz refutation** (Definition 2.1) is a family of multilinear polynomials $p_C$ ($C\in F$), $q_j$, $r_j$ with
--   $$\sum_{C\in F}p_C\,\bar C+\sum_j q_j(x_j^2-x_j)+r_j(1-x_j-\bar x_j)=1,$$
--   of degree $\max\{\deg(p_C\bar C),\deg(q_j(x_j^2-x_j)),\deg(r_j(1-x_j-\bar x_j))\}$.
--
--   A **Sherali-Adams refutation** (Definitions 2.2, 2.3) consists of arbitrary polynomials $p_C,q_i,r_i\in\mathbb R[x,\bar x]$ and a **conical junta** $J=\sum_D\lambda_D D$ (finitely many conjunctions $D$, $\lambda_D\ge0$) with
--   $$\sum_{C\in F}p_C\,\bar C+\sum_i q_i(x_i^2-x_i)+\sum_i r_i(x_i+\bar x_i-1)+J=-1 .$$
--   Its **degree** is the maximum of $\deg(p_C\bar C)$, $\deg(q_i(x_i^2-x_i))$, $\deg(r_i(x_i+\bar x_i-1))$ and $\deg J$ (the largest conjunction with $\lambda_D>0$). Its **size** is the number of monomials produced by expanding every product before cancellation:
--   $$\mathrm{size}=\sum_{C\in F}|\mathrm{supp}\,p_C|+2\sum_i|\mathrm{supp}\,q_i|+3\sum_i|\mathrm{supp}\,r_i|+|\{D:\lambda_D>0\}|.$$
--   The size of a CNF is $|F|=\sum_{C\in F}(|C|+1)$.
--
--   A **degree-$d$ design** (Definition 2.4) is a map $D$ on the polynomials of degree $\le d$ with $D[1]=1$, linear on them, $D[p(x_j^2-x_j)]=0$ for $\deg p\le d-2$ and $D[p(1-x_j-\bar x_j)]=0$ for $\deg p\le d-1$. It is **$F$-nonwitnessing** if $D[C]=0$ for every clause $C_i\in F$ and every conjunction $C\Rightarrow\bar C_i$ with $\deg C\le d$. A **degree-$d$ pseudoexpectation** (Definition 2.5) is a degree-$d$ design with $D[C]\ge0$ for every conjunction of degree $\le d$.
--
--   **Formalization Note.** $\mathbb R[x,\bar x]$ is `MvPolynomial (α ⊕ α) ℝ` with `Sum.inl i` $=x_i$ and `Sum.inr i` $=\bar x_i$. There is no booleanity axiom for $\bar x_i$, as in Definition 2.3. The junta is a finitely supported nonnegative function on conjunctions. The polynomials $p_C$ are indexed by all clauses, but only those of $F$ enter the identity, degree and size. Size reading: p. 2 says "the number of monomials produced by expanding all polynomial expressions in the proof before performing any cancellations", Definition 2.3 says "the maximum number"; we take the total count, which is within a factor $|F|+2|\alpha|+1$ of the maximum over the summands. A design is a function on all of $\mathbb R[x,\bar x]$ of which only the values on degree-$\le d$ polynomials are constrained, and the degree bounds $d-2$, $d-1$ are written $\deg p+2\le d$, $\deg p+1\le d$.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), pp. 1–2 (SA refutation, degree and size), p. 16 (§2.1), pp. 17–18, Definitions 2.1–2.5

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

open Classical

/-!
# Sherali-Adams and R-Nullstellensatz refutations, designs and pseudoexpectations

Acheampong, Davis, Robere, *Polynomial Interpolation for Sherali-Adams Lower Bounds*,
STOC 2027 submission (manuscript sha256 8de0a787…), §1 pp. 1–2 and §2.1–2.2 pp. 16–18
(Definitions 2.1–2.5).

* CNFs, clauses, literals and unsatisfiability are those of the published definition
  `MultiplierAssoc206_Resolution_CNF`: a literal `(x, b)` asserts `x = b`, a clause is a finite
  set of literals, a CNF a finite set of clauses, over a variable type `α`.
* The dual-variable ring `ℝ[x₁, …, xₙ, x̄₁, …, x̄ₙ]` is `MvPolynomial (α ⊕ α) ℝ`:
  `Sum.inl i` is `xᵢ` and `Sum.inr i` is the dual variable `x̄ᵢ`.
* A conjunction is a finite set of literals; it is encoded by the product of `xᵢ` (positive
  literal) and `x̄ⱼ` (negative literal). `C̄` is the conjunction of the negated literals of the
  clause `C`, so `C` is satisfied iff `C̄ = 0` on 0/1 points with `x̄ = 1 − x`.
-/

variable {α : Type}

/-- The dual-variable polynomial ring `ℝ[x, x̄]`: `Sum.inl i ↦ xᵢ`, `Sum.inr i ↦ x̄ᵢ`. -/
abbrev DualPoly (α : Type) := MvPolynomial (α ⊕ α) ℝ

/-- The variable `xᵢ`. -/
noncomputable def xv (i : α) : DualPoly α := MvPolynomial.X (Sum.inl i)

/-- The dual variable `x̄ᵢ`. -/
noncomputable def xbar (i : α) : DualPoly α := MvPolynomial.X (Sum.inr i)

/-- The polynomial of a literal: `xᵢ` for `(i, true)`, `x̄ᵢ` for `(i, false)`. -/
noncomputable def litPoly (l : Literal α) : DualPoly α := if l.2 then xv l.1 else xbar l.1

/-- A conjunction of literals (a finite set of literals, read as their conjunction). -/
abbrev Conjunction (α : Type) := Finset (Literal α)

/-- The multilinear encoding `∏_{i∈P} xᵢ ∏_{j∈N} x̄ⱼ` of a conjunction. -/
noncomputable def conjPoly (C : Conjunction α) : DualPoly α := ∏ l ∈ C, litPoly l

/-- The negation of a literal. -/
def negLit (l : Literal α) : Literal α := (l.1, !l.2)

/-- `C̄`: the conjunction of the negations of the literals of the clause `C` (De Morgan). -/
noncomputable def clauseNeg (C : Clause α) : Conjunction α := C.image negLit

/-- An assignment satisfies a conjunction when it satisfies each of its literals. -/
def ConjSat (a : α → Bool) (C : Conjunction α) : Prop := ∀ l ∈ C, LitSat a l

/-- `C ⇒ C̄ᵢ`: every assignment satisfying the conjunction `C` falsifies the clause `Ci`
(`C` witnesses the falsity of `Ci`). -/
def Witnesses (C : Conjunction α) (Ci : Clause α) : Prop :=
  ∀ a : α → Bool, ConjSat a C → ¬ ClauseSat a Ci

/-- `|F|`: the size of a CNF, counted as the number of clauses plus the number of literal
occurrences, `∑_{C ∈ F} (|C| + 1)`. -/
def cnfSize (F : CNF α) : ℕ := ∑ C ∈ F, (C.card + 1)

/-- A polynomial is multilinear when no variable occurs with exponent `≥ 2` in any of its
monomials. -/
def IsMultilinear (p : DualPoly α) : Prop := ∀ m ∈ p.support, ∀ v, m v ≤ 1

/-- An `ℝ`-Nullstellensatz refutation of `F` (Definition 2.1): multilinear polynomials
`p_C` (one per clause `C ∈ F`), `q_j`, `r_j` with
`∑_C p_C C̄ + ∑_j q_j (x_j² − x_j) + r_j (1 − x_j − x̄_j) = 1`. -/
structure NSRefutation [Fintype α] (F : CNF α) where
  p : Clause α → DualPoly α
  q : α → DualPoly α
  r : α → DualPoly α
  p_ml : ∀ C ∈ F, IsMultilinear (p C)
  q_ml : ∀ j, IsMultilinear (q j)
  r_ml : ∀ j, IsMultilinear (r j)
  identity :
    ∑ C ∈ F, p C * conjPoly (clauseNeg C) +
      ∑ j, (q j * (xv j ^ 2 - xv j) + r j * (1 - xv j - xbar j)) = 1

/-- The degree of a Nullstellensatz refutation: the maximum of `deg(p_C C̄)`,
`deg(q_j (x_j² − x_j))`, `deg(r_j (1 − x_j − x̄_j))`. -/
noncomputable def NSRefutation.degree [Fintype α] {F : CNF α} (π : NSRefutation F) : ℕ :=
  max (max (F.sup fun C => (π.p C * conjPoly (clauseNeg C)).totalDegree)
      (Finset.univ.sup fun j => (π.q j * (xv j ^ 2 - xv j)).totalDegree))
    (Finset.univ.sup fun j => (π.r j * (1 - xv j - xbar j)).totalDegree)

/-- A Sherali-Adams refutation of `F` in the dual-variable encoding (Definitions 2.2, 2.3):
arbitrary polynomials `p_C` (`C ∈ F`), `q_i`, `r_i ∈ ℝ[x, x̄]` and a conical junta
`J = ∑ λ_D D` (nonnegative coefficients `λ_D` on conjunctions `D`) with
`∑_C p_C C̄ + ∑_i q_i (x_i² − x_i) + ∑_i r_i (x_i + x̄_i − 1) + J = −1`.
Only `x_i² − x_i` is a booleanity axiom; there is none for `x̄_i`. -/
structure SARefutation [Fintype α] (F : CNF α) where
  p : Clause α → DualPoly α
  q : α → DualPoly α
  r : α → DualPoly α
  J : Conjunction α →₀ ℝ
  J_nonneg : ∀ D, 0 ≤ J D
  identity :
    ∑ C ∈ F, p C * conjPoly (clauseNeg C) + ∑ i, q i * (xv i ^ 2 - xv i) +
      ∑ i, r i * (xv i + xbar i - 1) + J.sum (fun D c => c • conjPoly D) = -1

/-- The degree of a Sherali-Adams refutation: the maximum of `deg(p_C C̄)`,
`deg(q_i (x_i² − x_i))`, `deg(r_i (x_i + x̄_i − 1))` and `deg(J)`, the largest number of
literals of a conjunction with a nonzero coefficient in `J`. -/
noncomputable def SARefutation.degree [Fintype α] {F : CNF α} (π : SARefutation F) : ℕ :=
  max (max (max (F.sup fun C => (π.p C * conjPoly (clauseNeg C)).totalDegree)
      (Finset.univ.sup fun i => (π.q i * (xv i ^ 2 - xv i)).totalDegree))
      (Finset.univ.sup fun i => (π.r i * (xv i + xbar i - 1)).totalDegree))
    (π.J.support.sup Finset.card)

/-- The size of a Sherali-Adams refutation: the number of monomials produced by expanding
every product before cancellation. `p_C C̄` contributes one monomial per monomial of `p_C`,
`q_i (x_i² − x_i)` two per monomial of `q_i`, `r_i (x_i + x̄_i − 1)` three per monomial of
`r_i`, and `J` one per conjunction with a nonzero coefficient. -/
noncomputable def SARefutation.size [Fintype α] {F : CNF α} (π : SARefutation F) : ℕ :=
  ∑ C ∈ F, (π.p C).support.card + ∑ i, 2 * (π.q i).support.card +
    ∑ i, 3 * (π.r i).support.card + π.J.support.card

/-- A degree-`d` `ℝ`-design (Definition 2.4), as a function on all of `ℝ[x, x̄]` of which only
the values on `P_d`, the polynomials of total degree `≤ d`, are constrained: normalization,
linearity on `P_d`, booleanity `D[p (x_j² − x_j)] = 0` for `deg p ≤ d − 2`, complementarity
`D[p (1 − x_j − x̄_j)] = 0` for `deg p ≤ d − 1`. -/
structure IsDesign (d : ℕ) (D : DualPoly α → ℝ) : Prop where
  normalization : D 1 = 1
  linearity : ∀ (a b : ℝ) (p q : DualPoly α), p.totalDegree ≤ d → q.totalDegree ≤ d →
    D (a • p + b • q) = a * D p + b * D q
  booleanity : ∀ (p : DualPoly α) (j : α), p.totalDegree + 2 ≤ d →
    D (p * (xv j ^ 2 - xv j)) = 0
  complementarity : ∀ (p : DualPoly α) (j : α), p.totalDegree + 1 ≤ d →
    D (p * (1 - xv j - xbar j)) = 0

/-- `F`-nonwitnessing (Definition 2.4): `D[C] = 0` for every clause `Cᵢ ∈ F` and every
conjunction `C ⇒ C̄ᵢ` with `deg(C) ≤ d` (the degree of a conjunction is its number of
literals). -/
def IsNonwitnessing (F : CNF α) (d : ℕ) (D : DualPoly α → ℝ) : Prop :=
  ∀ Ci ∈ F, ∀ C : Conjunction α, Witnesses C Ci → C.card ≤ d → D (conjPoly C) = 0

/-- A degree-`d` pseudoexpectation (Definition 2.5): a degree-`d` design that is nonnegative on
every conjunction of degree `≤ d`. -/
def IsPseudoexpectation (d : ℕ) (D : DualPoly α → ℝ) : Prop :=
  IsDesign d D ∧ ∀ C : Conjunction α, C.card ≤ d → 0 ≤ D (conjPoly C)

end SAInterp.Res2


