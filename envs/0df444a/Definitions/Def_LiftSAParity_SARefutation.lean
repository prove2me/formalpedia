-- Prove2me | Definitions.Def_LiftSAParity_SARefutation
-- name    : LiftSAParity_SARefutation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:40.943195+00:00
-- url     : https://prove2.me/theorems/3665d578-f114-4620-b734-6f533a38a7ad
-- title:
--   Sherali–Adams refutation of a CNF formula
-- statement:
--   Let $\varphi$ be a CNF formula over the variables $V$. Work in $\mathbb R[X_V]$ with $X_V=\{x_v,\bar x_v\}_{v\in V}$. A clause $C=\bigvee_{i\in I}x_i\vee\bigvee_{j\in J}\bar x_j$ becomes the monomial $p_C=\prod_{i\in I}\bar x_i\prod_{j\in J}x_j$, which equals $1$ exactly on the assignments falsifying $C$. The axioms are $\mathcal P=\{p_C\}_{C\in\varphi}$, the complementarity axioms $C_V=\{1-\bar x_v-x_v\}$ (4) and the Boolean axioms $B_V=\{x_v(1-x_v)\}\cup\{\bar x_v(1-\bar x_v)\}$ (5).
--
--   A **Sherali–Adams refutation** of $\varphi$ consists of polynomials $q_p$, one for each axiom $p$, and a polynomial $h_\alpha=\sum_{A,B}\alpha_{A,B}\prod_{i\in A}x_i\prod_{j\in B}\bar x_j$ with all $\alpha_{A,B}\ge0$ (6), such that
--   $$\sum_{p\in\mathcal P\cup C_V\cup B_V}p\cdot q_p+h_\alpha=-1 . \tag{7}$$
--
--   **Formalization Note** The multipliers are indexed by the names of the axioms (a clause, a variable, a pair (variable, polarity)) instead of by the set of axiom polynomials; merging equal polynomials gives a set-indexed refutation of no larger degree or coefficient size.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §3, p.8, eqs. (4)–(7)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsNonnegMultilinear

namespace LiftSAParity

open MvPolynomial

/-- The clause monomial `p_C` (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to
Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §3, p.8): "A clause of the
form C = ⋁_{i∈I} x_i ∨ ⋁_{j∈J} x̄_j is converted to a monomial p_C = ∏_{i∈I} x̄_i · ∏_{j∈J} x_j".
In `ℝ[X_n] = MvPolynomial (V × Bool) ℝ`, `X (v, true)` is `x_v` and `X (v, false)` is `x̄_v`; a
literal `(v, b)` contributes the variable `X (v, !b)`, so `p_C = 1` exactly on falsifying
assignments. -/
noncomputable def clauseMono {V : Type*} (C : Clause V) : MvPolynomial (V × Bool) ℝ :=
  ∏ l ∈ C, X (l.1, !l.2)

/-- The complementarity axiom `1 − x̄_v − x_v` of `C_n`, eq. (4), p.8. -/
noncomputable def compAxiom {V : Type*} (v : V) : MvPolynomial (V × Bool) ℝ :=
  1 - X (v, false) - X (v, true)

/-- The Boolean axioms `x_v(1 − x_v)` and `x̄_v(1 − x̄_v)` of `B_n`, eq. (5), p.8. -/
noncomputable def boolAxiom {V : Type*} (vb : V × Bool) : MvPolynomial (V × Bool) ℝ :=
  X vb * (1 - X vb)

/-- **Sherali–Adams refutation** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree
to Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §3, p.8): "A
Sherali-Adams refutation π of P is a set of polynomials {q_p}_{p∈P∪A_n} over the polynomial ring
R[X_n] and a polynomial h_α ∈ R[X_n] of the form ∑_{A,B⊆[n]} α_{A,B} · ∏_{i∈A} x_i · ∏_{j∈B} x̄_j,
(6) where α_{A,B} ≥ 0 for any A and B, such that ∑_{p∈P∪A_n} p · q_p + h_α = −1. (7)" Here
`P = {p_C : C ∈ φ}` and `A_n = B_n ∪ C_n` (eqs. (4), (5)).

**Formalization Note** The multipliers are indexed by the names of the axioms (a clause of `φ`, a
variable `v` for `1 − x̄_v − x_v`, a pair `(v, b)` for the Boolean axiom of `x_v` or `x̄_v`) rather
than by the set of axiom polynomials. Merging the multipliers of equal polynomials gives a
set-indexed refutation of no larger degree or coefficient size, so existence statements and
lower bounds are the same. -/
structure SARefutation {V : Type*} [Fintype V] (φ : CNF V) where
  /-- the multiplier `q_{p_C}` of each clause `C` of `φ` -/
  qClause : φ → MvPolynomial (V × Bool) ℝ
  /-- the multiplier of the axiom `1 − x̄_v − x_v` -/
  qComp : V → MvPolynomial (V × Bool) ℝ
  /-- the multiplier of the axiom `X(v,b)(1 − X(v,b))` -/
  qBool : V × Bool → MvPolynomial (V × Bool) ℝ
  /-- the nonnegative part `h_α` -/
  h : MvPolynomial (V × Bool) ℝ
  h_form : IsNonnegMultilinear h
  identity : (∑ C : φ, clauseMono C.1 * qClause C) + (∑ v : V, compAxiom v * qComp v) +
      (∑ vb : V × Bool, boolAxiom vb * qBool vb) + h = -1

end LiftSAParity


