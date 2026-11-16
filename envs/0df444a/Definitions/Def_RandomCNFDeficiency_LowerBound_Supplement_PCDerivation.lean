-- Prove2me | Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_PCDerivation
-- name    : RandomCNFDeficiency_LowerBound_Supplement_PCDerivation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:55:31.705812+00:00
-- url     : https://prove2.me/theorems/c28e47c0-cd91-4c19-9c30-667f5bad8e55
-- title:
--   PC derivations, all-field upper bounds and $\mathrm{PC}$ over $\mathbb F_p$
-- statement:
--   Let $F$ be a CNF on the variables $x_1,\dots,x_n$ and $K$ a field. A **polynomial calculus derivation** of $q\in K[x_1,\dots,x_n]$ from $F$ is a finite sequence of polynomials ending in $q$, each of which is a clause polynomial $p_C$ ($C\in F$), a Boolean axiom $x_i^2-x_i$, a linear combination $\alpha p+\beta p'$ of two earlier lines, or $x_i p$ for an earlier line $p$; its degree is the largest total degree of a line. A refutation is a derivation of $1$.
--
--   $F$ is **easy in degree $b$ over every field** if, for every field $K$, $F$ has some refutation over $K$ of degree at most the real number $b$:
--
--   $$\forall K\ \exists \pi:\ \pi \text{ refutes } F \text{ over } K,\qquad \deg\pi\le b.$$
--
--   Over $\mathbb F_p$ write $Q(F)=\{p_C : C\in F\}\cup\mathrm{Bool}$, the axiom set whose degree-$D$ consequences $\mathrm{PC}_D$ appear in Appendix A, and say $\operatorname{Deg}_{\mathrm{PC},\mathbb F_p}(F)>D$ when every refutation of $F$ over $\mathbb F_p$ has degree greater than $D$.
--
--   These notions express the upper bound of Section 4 (existence of one refutation per field) and the degree premise of the tradeoff theorems of Appendix A.
--
--   **Formalization Note** The PC rules, clause polynomials and refutations are the published base definitions; $\mathbb F_p$ is `ZMod p` for prime $p$; fields range over one universe. Variables are indexed by $\{0,\dots,n-1\}$.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Section 2.2, printed p. 7, PDF p. 9; Section 4, printed p. 15, PDF p. 17; Appendix A, printed p. 20, PDF p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
set_option autoImplicit false
universe uPC

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound

/-- A PC derivation of the last line `q` from the CNF `F`: every line is an input clause
polynomial, a Boolean axiom `x_i^2 - x_i`, or follows from earlier lines by the linear-combination
or variable-multiplication rule (the published `PCStep`). The case `q = 1` is `IsPCRefutation`. -/
def IsPCDerivation {n : ℕ} {K : Type uPC} [Field K]
    (F : CNF n) (π : List (MvPolynomial (Fin n) K)) (q : MvPolynomial (Fin n) K) : Prop :=
  π.getLast? = some q ∧
    ∀ (j : ℕ) (p : MvPolynomial (Fin n) K), π[j]? = some p → PCStep F (π.take j) p

/-- Simultaneously over every field `K` (in the universe `uPC`), `F` has SOME ordinary PC
refutation of degree at most the real number `b`. -/
def AllFieldsEasy {n : ℕ} (F : CNF n) (b : ℝ) : Prop :=
  ∀ (K : Type uPC) [Field K], ∃ π : List (MvPolynomial (Fin n) K),
    IsPCRefutation F π ∧ (pcDegree π : ℝ) ≤ b

/-- `Q(F) = {p_C : C ∈ F} ∪ Bool` over `F_p`, with the published clause polynomials `p_C`. -/
noncomputable def fpAxioms {n : ℕ} (p : ℕ) [Fact p.Prime] (F : CNF n) :
    Set (ResPCDegreeSize.Main.Poly n p) :=
  ResPCDegreeSize.Main.boolAxioms n p ∪ {q | ∃ C ∈ F, q = clausePolynomial C}

/-- `Deg_{PC,F_p}(F) > D`: every ordinary PC refutation of `F` over `F_p` has degree `> D`
(vacuously true when `F` has no refutation). -/
def FpDegreeExceeds {n : ℕ} (p : ℕ) [Fact p.Prime] (F : CNF n) (D : ℝ) : Prop :=
  ∀ π : List (MvPolynomial (Fin n) (ZMod p)), IsPCRefutation F π → D < (pcDegree π : ℝ)

end RandomCNFDeficiency.LowerBound.Supplement


