-- Prove2me | Definitions.Def_CNFLearnMQ_cores
-- name    : CNFLearnMQ_cores
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:21.670668+00:00
-- url     : https://prove2.me/theorems/156cb271-5b49-4d2c-b638-5c8d83e05b54
-- title:
--   Cores $\mathcal R_X$ of a solution and induced subclauses $c(X,R)$
-- statement:
--   Let $\Phi$ be a CNF formula on the variable set $V=\{0,\dots,n-1\}$ and $X\in\{\mathrm{True},\mathrm{False}\}^V$ an assignment. For $R\subseteq V$, $X^{\oplus R}$ is $X$ with every variable of $R$ flipped. A set $R$ is a **core** of $X$ if
--   $$\Phi(X^{\oplus R})=0\quad\text{and}\quad \Phi(X^{\oplus R'})=1\ \text{ for every } R'\subsetneq R,$$
--   i.e. flipping $R$ falsifies $\Phi$ but flipping any proper subset does not. The **core family** $\mathcal R_X$ is the set of all cores of $X$.
--
--   For a core $R$, the **induced subclause** is $c(X,R)=(R,\neg X_R)$: the subclause on the variables $R$ whose forbidden assignment is the negation of $X$ on $R$. An assignment $Y$ violates $c(X,R)$ exactly when $Y_R=\neg X_R$. For a family $\mathcal R$ of cores, $\mathcal C(\mathcal R)=\{c(X,R): R\in\mathcal R\}$.
--
--   Cores are the objects LearnCore recovers with membership queries; every core sits inside a clause of $\Phi$ (Lemma 4.3), which is what makes the seeds and extensions of LearnCNF small.
--
--   **Formalization Note** Clauses are the published `Fin n → Option Bool`, storing the *satisfying* literal value of each variable (`none` = absent); the paper's forbidden assignment is its negation. Hence $c(X,R)$ stores the value $X_v$ on each $v\in R$. The paper defines cores only for solutions $X$; every statement of the mission assumes $X$ is a solution.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Definitions 4.1 and 4.2, p.16

import Mathlib
import Definitions.Def_CNFLearning873_Valiant_CNF

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

variable {n : ℕ}

/-- `X^{⊕R}`: the assignment obtained from `X` by flipping every variable of `R` (Feng, Yu, Zhang,
STOC 2027 submission (manuscript sha256 519ee6d4…), Definition 4.1, p.16). -/
def flipOn (X : Assignment n) (R : Finset (Fin n)) : Assignment n :=
  fun v => if v ∈ R then !X v else X v

/-- `Φ(X) = 1`: the assignment `X` satisfies every clause of `Φ`. -/
def SatAll (Φ : CNF n) (X : Assignment n) : Prop := ∀ c ∈ Φ, Sat X c

/-- `R` is a core of `X` (Definition 4.1, p.16): `Φ(X^{⊕R}) = 0` and `Φ(X^{⊕R′}) = 1` for every
proper subset `R′ ⊊ R`.

**Formalization Note** The paper defines cores only for solutions `X ∈ supp(µ_Φ)`; every statement
of the mission that uses cores assumes `X ∈ solutions Φ`. (For a non-solution the predicate holds
for `R = ∅`; no statement uses that case.) -/
def IsCore (Φ : CNF n) (X : Assignment n) (R : Finset (Fin n)) : Prop :=
  ¬ SatAll Φ (flipOn X R) ∧ ∀ R' : Finset (Fin n), R' ⊂ R → SatAll Φ (flipOn X R')

/-- The core family `R_X` of `X` (Definition 4.1, p.16). -/
noncomputable def cores (Φ : CNF n) (X : Assignment n) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (IsCore Φ X)

/-- The subclause induced by `R` with respect to `X`, `c(X, R) = (R, ¬X_R)` (Definition 4.2, p.16).

**Formalization Note** The published clause type `Fin n → Option Bool` stores the *satisfying*
literal value (`Sat x c ↔ ∃ i, c i = some (x i)`); the paper's forbidden assignment is its negation,
`σ_c(v) = ¬ b` when `c v = some b`. The forbidden assignment of `c(X, R)` is `¬X_R`, so its stored
literal value on `v ∈ R` is `X v`; an assignment `Y` violates it exactly when `Y_v ≠ X_v` on all of
`R`, i.e. `Y_R = ¬X_R`. -/
def inducedClause (X : Assignment n) (R : Finset (Fin n)) : Clause n :=
  fun v => if v ∈ R then some (X v) else none

/-- `C(R) = {c(X, R) | R ∈ R}`, the induced subclauses of a family of cores of `X`
(Definition 4.2, p.16). -/
def inducedFamily (X : Assignment n) (Rs : Finset (Finset (Fin n))) : Finset (Clause n) :=
  Rs.image (inducedClause X)

end CNFLearnMQ


