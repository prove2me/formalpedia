-- Prove2me | Definitions.Def_LineVsPoint_lineRestrict
-- name    : LineVsPoint_lineRestrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:03.908873+00:00
-- url     : https://prove2.me/theorems/bfdc4cdc-01b2-4e9b-87e3-f59faea58a5e
-- title:
--   Restrictions $R(L(t))$, $B(L(t),p_L(t))$ and the substitution $B(X,Y,Q(X,Y))$
-- statement:
--   Three formal substitutions used throughout the paper.
--
--   1. For $R\in\mathbb F[X_1,\dots,X_m]$ and a parameterized line $L(t)=a+tu$, the **restriction** $R(L(t))=R(a+tu)\in\mathbb F[t]$. The paper writes $R(L(t))\equiv 0$ when this polynomial is zero and $Q|_L=P_L$ when $Q(L(t))=p_L(t)$.
--   2. For $B\in\mathbb F[X,Y,Z]$, a line $L(t)=a+tu$ of $\mathbb F^2$ and $p\in\mathbb F[t]$, the restriction of $B$ to the **polynomial graph** $\{(L(t),p(t))\}$: $B(L(t),p(t))\in\mathbb F[t]$.
--   3. For $B\in\mathbb F[X,Y,Z]$ and $Q\in\mathbb F[X,Y]$, the polynomial $B(X,Y,Q(X,Y))\in\mathbb F[X,Y]$.
--
--   All three are identities of formal polynomials, as §2.1 of the paper requires.
--
--   **Formalization Note** `lineRestrict a u R`, `graphRestrict a u p B` and `substZ B Q` are `MvPolynomial.aeval`/`bind₁` substitutions; $X,Y,Z$ are the variables $0,1,2$. Reading $Q|_L=P_L$ as the formal identity is the strongest reading; for $d<q$ it is the same as equality of functions on $L$.
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), §2.4, p.13; Lemmas 2.4–2.7, pp.12–14

import Mathlib

set_option autoImplicit false

namespace LineVsPoint

open Polynomial in
/-- The **restriction of a polynomial to a parameterized line**, as a formal univariate
polynomial: for `R ∈ F[X₁, …, X_m]`, a translate `a` and a direction `u`, the polynomial
`R(a + t u) ∈ F[t]`. Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the
Line–versus–Point Test* (manuscript, sha256 328a8943…), Lemma 2.4, p.12 ("`R(L(t)) ≡ 0`") and
Lemma 2.7, p.14 ("`Q|_L = P_L`").

**Formalization Note.** "`R(L(t)) ≡ 0`" is `lineRestrict a u R = 0` in `F[t]`, and
"`Q|_L = P_L`" is the formal identity `lineRestrict a_L u_L Q = p_L` (for `d < q` the same as
equality of functions on `L`). -/
noncomputable def lineRestrict {F : Type*} [Field F] {m : ℕ} (a u : Fin m → F)
    (R : MvPolynomial (Fin m) F) : F[X] :=
  MvPolynomial.aeval (fun i => C (a i) + C (u i) * X) R

open Polynomial in
/-- The **restriction of a trivariate polynomial to the polynomial graph of a line**: for
`B ∈ F[X, Y, Z]`, a line `L(t) = a + t u` of `F²` and `p ∈ F[t]`, the polynomial
`B(L(t), p(t)) ∈ F[t]`. Manuscript (sha256 328a8943…), §2.4, p.13 (the polynomial graph
`{(L(t), p_L(t))}`), Lemma 2.5, p.13 and Lemma 2.7, p.14 ("`B(L(t), p_L(t)) ≡ 0`").

**Formalization Note.** Variables `X, Y, Z` are `MvPolynomial` variables `0, 1, 2`. "`≡ 0`"
means this formal polynomial in `t` is `0`. -/
noncomputable def graphRestrict {F : Type*} [Field F] (a u : Fin 2 → F) (p : F[X])
    (B : MvPolynomial (Fin 3) F) : F[X] :=
  MvPolynomial.aeval ![C (a 0) + C (u 0) * X, C (a 1) + C (u 1) * X, p] B

/-- **Substituting a bivariate polynomial for `Z`**: `B(X, Y, Q(X, Y)) ∈ F[X, Y]` for
`B ∈ F[X, Y, Z]` and `Q ∈ F[X, Y]`. Manuscript (sha256 328a8943…), Lemma 2.6 and Lemma 2.7,
p.14. -/
noncomputable def substZ {F : Type*} [Field F] (B : MvPolynomial (Fin 3) F)
    (Q : MvPolynomial (Fin 2) F) : MvPolynomial (Fin 2) F :=
  MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1, Q] B

end LineVsPoint


