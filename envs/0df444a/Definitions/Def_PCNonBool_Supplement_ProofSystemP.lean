-- Prove2me | Definitions.Def_PCNonBool_Supplement_ProofSystemP
-- name    : PCNonBool_Supplement_ProofSystemP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:27:05.254621+00:00
-- url     : https://prove2.me/theorems/f90f2f9b-5b30-4ee2-980a-268c73bbf330
-- title:
--   The proof system $\mathcal P$: PCR with $\{\pm1\}$-variables
-- statement:
--   The proof system $\mathcal P$ of Section 7 is polynomial calculus resolution supplied with $\{\pm1\}$-valued variables over a field $\mathbb F$ with $\operatorname{char}\mathbb F\ne2$. For every Boolean variable $w$ it has three variables: $w$ itself, its dual $\bar w=1-w$, and its Fourier extension $w^{F}=(-1)^w=1-2w$. For a CNF formula $\Phi$ the axioms are, for every variable $w$ of $\Phi$,
--   $$w^2-w,\qquad \bar w^2-\bar w,\qquad w+\bar w-1,\qquad w^{F}-(1-2w),\qquad (w^{F})^2-1,$$
--   and, for every clause $C$ of $\Phi$, the monomial $\prod_{x\in C}\bar x\cdot\prod_{\neg x\in C}x$.
--
--   Lines are kept in reduced form: exponents of $w,\bar w$ are capped at $1$, exponents of $w^F$ are taken modulo $2$, and a monomial containing both a variable and its dual is $0$. A $\mathcal P$-refutation of $\Phi$ is a refutation of these axioms with lines in this reduced form, and its size is the number of monomials of its reduced lines.
--
--   **Formalization Note** The variable $(v,0)$ is $w=x_v$, $(v,1)$ is $\bar w$ and $(v,2)$ is $w^F$. The reduction is the paper's lower-bound convention (p.11) together with its syntactic convention on duals (p.53).
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §7, p.50 (PDF p.53); §7.1, pp.52–53 (PDF pp.55–56); §3.4 (PCR), p.12 (PDF p.15)

import Mathlib
import Definitions.Def_PCNonBool_Supplement_CNF

namespace PCNonBool.Supplement

open MvPolynomial

/-- The variables of the proof system `P` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §7, p.50 (PDF p.53) and §7.1, pp.52–53
(PDF pp.55–56)): for every Boolean variable `w = x_v` (`v ∈ ℕ`), the variable itself `(v, 0)`,
its dual `w̄ = 1 - w` `(v, 1)`, and its `{±1}`-valued Fourier extension `w^F = 1 - 2w` `(v, 2)`. -/
abbrev PVar : Type := ℕ × Fin 3

/-- The reduced form of the lines of `P`: the `F`-linear map sending a monomial to `0` if it contains
a variable together with its dual ("no monomial contains both a variable and its dual (simplified
to 0)", p.53 (PDF p.56)), and otherwise reducing every exponent modulo the range axioms: `w² = w`,
`w̄² = w̄` (exponent `min a 1`) and `(w^F)² = 1` (exponent `a mod 2`). This is the quotient-ring
representation in which lines are taken for lower bounds (p.11 (PDF p.14)). -/
noncomputable def redP {F : Type*} [Field F] : MvPolynomial PVar F →ₗ[F] MvPolynomial PVar F :=
  open Classical in
  (MvPolynomial.basisMonomials PVar F).constr F
    (fun m => if ∃ x ∈ m.support, x.2 = 0 ∧ m (x.1, 1) ≠ 0 then 0
      else ∏ x ∈ m.support, X x ^ (if x.2 = 2 then m x % 2 else min (m x) 1))

/-- The axioms of `P` for a CNF formula `Φ` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §7, p.50 (PDF p.53): "PCR supplied with
`{±1}`-variables"; §3.4, p.12 (PDF p.15) for PCR): for every `w = x_v`, `v ∈ Vars(Φ)`,

* the Boolean axioms `w² - w` and `w̄² - w̄`;
* the negation axiom `w + w̄ - 1` (PCR);
* the defining axiom `w^F - (1 - 2w)` of the Fourier extension and its order axiom `(w^F)² - 1`;

and for every clause `C` of `Φ` the monomial `∏_{x_v ∈ C} x̄_v · ∏_{¬x_v ∈ C} x_v` (the PCR
clause encoding, which vanishes exactly at the assignments satisfying `C`). A `P`-refutation of `Φ`
is a refutation `PCNonBool.IsRefutation redP (PAxioms F Φ)`. -/
noncomputable def PAxioms (F : Type*) [Field F] (Φ : CNF) : Set (MvPolynomial PVar F) :=
  {p | (∃ v ∈ Φ.vars,
      p = X (v, 0) ^ 2 - X (v, 0) ∨ p = X (v, 1) ^ 2 - X (v, 1) ∨
      p = X (v, 0) + X (v, 1) - 1 ∨ p = X (v, 2) - (1 - 2 * X (v, 0)) ∨ p = X (v, 2) ^ 2 - 1) ∨
    (∃ C ∈ Φ, p = ∏ l ∈ C.toFinset, (if l.2 then X (l.1, 1) else X (l.1, 0)))}

end PCNonBool.Supplement


