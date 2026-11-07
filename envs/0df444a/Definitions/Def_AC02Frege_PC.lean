-- Prove2me | Definitions.Def_AC02Frege_PC
-- name    : AC02Frege_PC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:16.277929+00:00
-- url     : https://prove2.me/theorems/2b82bcf8-8ba0-4111-beae-c49d23d73e46
-- title:
--   Polynomial calculus over $\mathbb F_2$ in formal degree $D$, and the space $C_D$
-- statement:
--   Let $F$ be a CNF in the Boolean variables $y_1,\dots,y_n$. For a literal $\lambda$ its truth polynomial $\lambda(y)$ is $y_i$ for the positive literal $y_i$ and $1+y_i$ for $\neg y_i$. The **complement** of a clause $J$ is
--   $$
--   \overline J=\prod_{\lambda\in J}\bigl(1+\lambda(y)\bigr),
--   $$
--   which is one exactly when $J$ is falsified. The polynomial encoding $G_F$ of $F$ asserts $1+\overline J=1$ for every clause $J$ of $F$ and the Boolean axioms $1+y_i^2+y_i=1$; an assertion $p=1$ is represented by its complement $1+p$.
--
--   A **polynomial-calculus (PC) derivation** starts from these complements ($\overline J$ and $y_i^2+y_i$) and may take a scalar linear combination of two previously derived complements or multiply a previously derived complement by a variable. A derivation has degree at most $D$ if every polynomial in it has formal degree at most $D$. A **refutation** derives the complement $1$ of the assertion $0=1$.
--
--   The space $C_D$ consists of the multilinear complements derivable in degree at most $D$:
--   $$
--   p\in C_D\iff \text{PC derives } 1+p=1 \text{ from } F \text{ in degree at most } D .
--   $$
--   In particular, if $F$ has no degree-$D$ PC refutation then $1\notin C_D$. The width $w(F)$ is the largest number of literals of a clause of $F$.
--
--   **Formalization Note** CNFs are the published `LiftSAParity.CNF` (finite sets of clauses, a clause a finite set of literals `(v, b)`). Derivations are the published `PCNonBool.IsDerivation` with the identity as reduction (no multilinearization inside PC), axioms `clauseCompl J` and `X i ^ 2 + X i`, and the bound `totalDegree ≤ D` on every line. The complement $0$ of the true assertion $1=1$ is counted as derivable (the empty derivation), so that $C_D$ is a vector space even when $G_F$ is empty.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Definitions 2.2–2.4, p.9

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_PCNonBool_IsDerivation
import Definitions.Def_AC02Frege_ML

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- The truth polynomial `λ(y)` of a literal (Definition 2.2, p.9): `y_v` for the positive literal
`(v, true)` and `1 + y_v` for the negative literal `(v, false)`. -/
noncomputable def litPoly {V : Type*} (l : V × Bool) : MvPolynomial V (ZMod 2) :=
  if l.2 then X l.1 else 1 + X l.1

/-- The complement `J̄ = ∏_{λ ∈ J} (1 + λ(y))` of a clause `J` (Definition 2.2, p.9): the
polynomial that is one exactly when `J` is falsified. The empty clause has complement `1`. -/
noncomputable def clauseCompl {V : Type*} (J : Clause V) : MvPolynomial V (ZMod 2) :=
  ∏ l ∈ J, (1 + litPoly l)

/-- The complements of the assertions of the polynomial encoding `G_F` of a CNF `F`
(Definitions 2.2–2.3, p.9): the clause complements `J̄`, `J ∈ F`, and the complements
`y_i² + y_i` of the Boolean axioms `1 + y_i² + y_i = 1`. -/
def pcAxioms {n : ℕ} (F : CNF (Fin n)) : Set (MvPolynomial (Fin n) (ZMod 2)) :=
  {p | (∃ J ∈ F, p = clauseCompl J) ∨ ∃ i : Fin n, p = X i ^ 2 + X i}

/-- **PC derivability in degree `D`** (Definition 2.3, p.9; Definition 2.4, p.9): the complement
`p` (of the assertion `1 + p = 1`) is derived from `F` by a polynomial-calculus derivation in which
every line has formal (total) degree at most `D`. PC takes scalar linear combinations of two
previously derived complements and multiplies a derived complement by a variable. A refutation
derives the complement `1` (of the assertion `0 = 1`).

**Formalization Note** The derivation is the published `PCNonBool.IsDerivation` with the
identity as reduction map (no multilinearization), from the axiom set `pcAxioms F`, together with
the formal-degree bound on every line. The Boolean axioms are axioms, as in the paper. The
complement `0` (of the trivially true assertion `1 = 1`) is counted as derivable by the empty
derivation, so that `C_D` is a vector space even when `G_F` is empty; this changes no other
polynomial. -/
def PCDerivable {n : ℕ} (F : CNF (Fin n)) (D : ℕ) (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation LinearMap.id (pcAxioms F) π ∧ (∀ q ∈ π, q.totalDegree ≤ D) ∧ p ∈ π

/-- The space `C_D` (Definition 2.4, p.9): the multilinear complements derivable from `F` in PC
degree at most `D`. Thus `p ∈ C_D ⟺ PC derives 1 + p = 1 from F in degree at most D`, and `F`
has no degree-`D` PC refutation iff `¬ PCDerivable F D 1`. -/
def CD {n : ℕ} (F : CNF (Fin n)) (D : ℕ) : Set (MvPolynomial (Fin n) (ZMod 2)) :=
  {p | IsMultilinear p ∧ PCDerivable F D p}

/-- The width `w(F)` of a CNF: the largest number of literals in one of its clauses (`0` for the
empty CNF). -/
def width {V : Type*} (F : CNF V) : ℕ :=
  F.sup Finset.card

end AC02Frege


