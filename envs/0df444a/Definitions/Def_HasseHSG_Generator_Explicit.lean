-- Prove2me | Definitions.Def_HasseHSG_Generator_Explicit
-- name    : HasseHSG_Generator_Explicit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:10.962874+00:00
-- url     : https://prove2.me/theorems/7ee2dddd-befc-4c89-943c-2a64ddd6b48f
-- title:
--   Input and output layout of the generator program (Theorem 1.2, Remark 1.3)
-- statement:
--   Remark 1.3 says that "explicit" means the polynomial map $G$ can be constructed in time $\mathrm{poly}(n,r,d)$. The goal states this on a uniform algebraic machine (published definition `EllipticRootFinding_Online_Machine`): field registers with $+,-,\times$, inversion and a zero test, the constants $0$ and $1$ only, and integer registers. The same program runs over every field. This definition fixes how the program receives its input and how its output is read as polynomials.
--
--   1. **Input.** The value $(n,r,d,e)$: three integers followed by a finite list $e$ of field elements.
--   2. **Output.** For each $i\in\{1,\dots,n\}$, a finite list of terms $[a,b,c]$ with $a,b\in\mathbb N$ and $c\in F$. The polynomial $G_i\in F[z,t]$ is the sum of the monomials $c\,z^a t^b$ over its list; repetitions and zero coefficients are allowed.
--
--   Supplying a list of distinct field elements as input is how the hypothesis $|F|\ge 2n^2r^4d^2$ becomes usable by an algorithm that has only the constants $0$ and $1$.
--
--   **Formalization Note.** `generatorInput n r d e` is the input value. `IsGeneratorVal w G` says the output value `w` lists the terms of `G : Fin n → MvPolynomial (Fin 2) F`, where `z = X 0` and `t = X 1`.
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), pp. 5–6, Theorem 1.2 and Remark 1.3; p. 38, proof of Theorem 1.2

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine

open EllipticRootFinding.Online

namespace HasseHSG.Generator

/-!
Input and output layout for "explicit" in Theorem 1.2 / Remark 1.3 (pp. 5–6), on the published
uniform algebraic machine `EllipticRootFinding.Online`.
-/

/-- The input `(n, r, d, e)`: three integers and a list `e` of field elements. -/
def generatorInput {F : Type} (n r d : ℕ) (e : List F) : Val F :=
  Val.ofList [Val.int n, Val.int r, Val.int d, fieldListVal e]

/-- One term `c · z^a · t^b` of a bivariate polynomial, written as the value `[a, b, c]`. -/
def termVal {F : Type} (x : ℕ × ℕ × F) : Val F :=
  Val.ofList [Val.int x.1, Val.int x.2.1, Val.fld x.2.2]

/-- The monomial `c · z^a · t^b` in `F[z, t]`, where `z = X 0` and `t = X 1`. -/
noncomputable def termPoly {F : Type} [Field F] (x : ℕ × ℕ × F) : MvPolynomial (Fin 2) F :=
  MvPolynomial.monomial (Finsupp.single 0 x.1 + Finsupp.single 1 x.2.1) x.2.2

/-- Output reading: the value `w` lists, for each `i < n`, a finite list of terms `[a, b, c]`
(repetitions and zero coefficients allowed), and `Gᵢ ∈ F[z, t]` is the sum of the terms
`c · z^a · t^b` of the `i`-th list. Variables: `z = X 0`, `t = X 1`. -/
def IsGeneratorVal {F : Type} [Field F] {n : ℕ} (w : Val F)
    (G : Fin n → MvPolynomial (Fin 2) F) : Prop :=
  ∃ T : Fin n → List (ℕ × ℕ × F),
    w = Val.ofList (List.ofFn fun i => Val.ofList ((T i).map termVal)) ∧
    ∀ i, G i = ((T i).map termPoly).sum

end HasseHSG.Generator


