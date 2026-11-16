-- Prove2me | Definitions.Def_SemAC02_Supplement_ResPC
-- name    : SemAC02_Supplement_ResPC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:42:16.832587+00:00
-- url     : https://prove2.me/theorems/b2fa5827-d06f-40a6-ac89-de321b07d6a2
-- title:
--   Semantic Res(PC) over a field and its size
-- statement:
--   Over a field $\mathbb F$, a line of **semantic Res(PC)** is a finite disjunction $(f_1=0)\vee\dots\vee(f_k=0)$ with $f_i\in\mathbb F[x]$, each polynomial written explicitly as a sum of monomials. A refutation of a CNF $\varphi$ is a sequence of lines, each an axiom (a clause of $\varphi$, the literal $x_i$ written as $1-x_i=0$ and $\neg x_i$ as $x_i=0$) or a semantically sound inference from at most two earlier lines, ending with the empty disjunction. **Res(PC$_w$)** requires every polynomial to have degree at most $w$.
--
--   The size $\mathrm{size}(\pi)$ counts distinct rooted subcircuits across the derivation when every polynomial is displayed as a ΣΠ circuit: distinct lines, distinct polynomials, distinct monomials and distinct variables.
--
--   Theorem 2.4 simulates this system line by line in semantic ΣΠΣΠ-PC.
--
--   **Formalization Note** Lines are lists of `MvPolynomial`s; the degree of a polynomial is its total degree. The size also counts each distinct line once, as the gate joining its polynomials.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §2.2, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_clauseAx

namespace SemAC02.Supplement

open MvPolynomial LiftSAParity

/-- The assignment `x` satisfies the Res(PC) line `(f₁ = 0) ∨ ⋯ ∨ (f_k = 0)` (Alekseev–Gryaznov–
Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript
(STOC 2027 submission), §2.2, p.17): some `f_i` vanishes at `x`. The empty line is satisfied by
no assignment. -/
def ResPCSat {F σ : Type} [CommRing F] (x : σ → Bool) (D : List (MvPolynomial σ F)) : Prop :=
  ∃ f ∈ D, polyFn f x = 0

/-- An **arity-2 semantic Res(PC) refutation** over a field `F` of a CNF `φ` (§2.2, p.17): proof
lines are finite disjunctions `(f₁ = 0) ∨ ⋯ ∨ (f_k = 0)` of polynomial equations,
`f_i ∈ F[x]`; every line is an axiom (a clause `C` of `φ`, each literal written as the equation
`litPolyF l = 0`, i.e. `1 − x_i = 0` for `x_i` and `x_i = 0` for `¬x_i`, in any order) or a
semantically sound inference from at most two earlier lines (`i = j` allowed); the refutation
ends with the empty disjunction.

**Formalization Note** A line is a `List` of polynomials; each polynomial is stored in
`MvPolynomial σ F`, i.e. "represented explicitly as a sum of monomials" (its support with
coefficients). -/
def IsSemResPCRef {F σ : Type} [Field F] (φ : CNF σ) (π : List (List (MvPolynomial σ F))) :
    Prop :=
  (∀ (k : ℕ) (hk : k < π.length),
    (∃ C ∈ φ, π[k].Perm (C.toList.map litPolyF)) ∨
    (∃ (i j : ℕ) (hi : i < k) (hj : j < k), ∀ x : σ → Bool,
      ResPCSat x (π[i]'(hi.trans hk)) → ResPCSat x (π[j]'(hj.trans hk)) → ResPCSat x π[k])) ∧
  π.getLast? = some []

/-- The **size** `size(π)` of a Res(PC) derivation (p.17): the number of distinct rooted
subcircuits across the derivation, each polynomial being displayed as its ΣΠ circuit (a plus
gate over the product gates of its monomials, the coefficients on the edges, the variables as
leaves) and each line as the gate joining its polynomials. Distinct lines, distinct polynomials,
distinct monomials and distinct variables are counted.

**Formalization Note** The sum gate of a polynomial is determined by the polynomial, the product
gate of a monomial by the monomial (the constant monomial is the empty product), and the root of
a line by the list of its polynomials. -/
noncomputable def resPCSize {F σ : Type} [CommRing F] (π : List (List (MvPolynomial σ F))) : ℕ :=
  open Classical in
  π.toFinset.card + π.flatten.toFinset.card +
    (π.flatten.toFinset.biUnion (fun f => f.support)).card +
    (π.flatten.toFinset.biUnion (fun f => f.vars)).card

end SemAC02.Supplement


