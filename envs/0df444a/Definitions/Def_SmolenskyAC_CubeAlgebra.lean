-- Prove2me | Definitions.Def_SmolenskyAC_CubeAlgebra
-- name    : SmolenskyAC_CubeAlgebra
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:12.222469+00:00
-- url     : https://prove2.me/theorems/43158ad8-c2dd-4734-80cc-881ba6fed1ec
-- title:
--   The algebra $U^n_F$ of functions on the cube and the degree $\deg_A$ in a quotient
-- statement:
--   Let $F$ be a field. $U^n_F$ is the algebra of functions $D^n\to F$ with pointwise operations; 'False' is $0_F$ and 'Truth' is $1_F$, and $X_i\in U^n_F$ is the function $X_i(d)=d(X_i)$. A polynomial $P\in F[X_1,\dots,X_n]$ is evaluated at $x\in D^n$ by substituting the $0/1$ values of $x$.
--
--   For a set $E\subseteq D^n$ the functions vanishing outside $E$ form an ideal $I_E$, and $A=U^n_F/I_E$ identifies functions that coincide outside $E$. The **degree** of $f$ in $A$ is
--
--   $$\deg_A(f)=\min\{\deg P : P(x)=f(x)\ \text{for all } x\notin E\},$$
--
--   the least total degree of a polynomial that coincides with $f$ outside $E$. The dimension of $A$ is the number of assignments outside $E$.
--
--   These are the objects in which the paper measures how hard a Boolean function is.
--
--   **Formalization Note** An algebra $A\in\Omega^n_F$ is encoded by its erased set $E$; every ideal of $U^n_F$ is some $I_E$ (p.79). The minimum is over a nonempty set, since every function on the cube is a polynomial (Proposition 1).
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, The Mappings from the set of Boolean functions to F-algebras, p.78 (pdf 2), and p.79 (pdf 3), the paragraph defining $deg_A$ and $\Omega^n_F$

import Mathlib
import Definitions.Def_SmolenskyAC_Operations

namespace SmolenskyAC

/-- The embedding of the Booleans in a field: 'False' is `0_F` and 'Truth' is `1_F`
(Smolensky, STOC 1987, p.78). -/
def toF {F : Type*} [Field F] (b : Bool) : F := if b then 1 else 0

/-- The variable `X_i` as an element of `U^n_F`, the algebra of functions `D^n → F` with pointwise
operations (p.78): `X_i(d) = d(X_i)`. In Lean `U^n_F` is the Pi algebra `Cube n → F`. -/
def cubeVar (F : Type*) [Field F] (n : ℕ) (i : Fin n) : Cube n → F := fun x => toF (x i)

/-- The value at the assignment `x` of a polynomial `P` in `X_1, …, X_n`. -/
noncomputable def evalAt {F : Type*} [Field F] {n : ℕ} (P : MvPolynomial (Fin n) F)
    (x : Cube n) : F :=
  MvPolynomial.eval (fun i => toF (x i)) P

/-- The degree `deg_A(f)` of `f ∈ U^n_F` in the quotient algebra `A = U^n_F / I`, where `I` is the
ideal of the functions vanishing outside a set `E ⊆ D^n` (Smolensky, STOC 1987, p.79): the least
total degree of a polynomial that coincides with `f` outside `E`.

**Formalization Note.** An algebra `A ∈ Ω^n_F` is encoded by its erased set `E` (the page's own
picture: "we ignore the assignments in E"); its dimension is the number of assignments outside `E`.
Every ideal of `U^n_F` is of this form (p.79). The set in `sInf` is nonempty, because every
function on the cube is a polynomial (Proposition 1), so `sInf` takes no junk value. -/
noncomputable def degOff {F : Type*} [Field F] {n : ℕ} (E : Finset (Cube n)) (f : Cube n → F) :
    ℕ :=
  sInf {d | ∃ P : MvPolynomial (Fin n) F, P.totalDegree ≤ d ∧ ∀ x, x ∉ E → evalAt P x = f x}

end SmolenskyAC


