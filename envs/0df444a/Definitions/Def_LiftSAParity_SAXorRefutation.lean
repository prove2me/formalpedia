-- Prove2me | Definitions.Def_LiftSAParity_SAXorRefutation
-- name    : LiftSAParity_SAXorRefutation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:58.23001+00:00
-- url     : https://prove2.me/theorems/e9a2868c-98bb-407f-8dcf-848b6a81fb5c
-- title:
--   Sherali–Adams over parities (SA(⊕)) refutation
-- statement:
--   With the variables $\tilde X_V=\{x_I,\bar x_I\}_{I\subseteq V}$ and the clause monomials $p_C$ of semantic SA(⊕), the axioms of SA(⊕) are
--   $$C_V=\{1-\bar x_I-x_I\},\quad B_V=\{x_I(1-x_I)\}\cup\{\bar x_I(1-\bar x_I)\},\quad D_V=\{x_I+x_J-2x_Ix_J-x_{I\triangle J}\} \tag{8–10}$$
--   over all $I,J\subseteq V$. An **SA(⊕) refutation** of $\varphi$ is a family of multipliers $q_p$, one for each clause monomial and each axiom, and a nonnegative multilinear $h_\alpha$ (12) with
--   $$\sum_{p}p\cdot q_p+h_\alpha=-1$$
--   exactly. Its **coefficient size** is the sum of the magnitudes of all coefficients of the multipliers and of $h_\alpha$; SA(⊕) measured this way is unary SA(⊕), uSA(⊕).
--
--   **Formalization Note** The multipliers are indexed by the names of the axioms; $D_{I,J}$ and $D_{J,I}$ are the same polynomial with two names, which changes no coefficient-size lower bound.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §3, p.9, eqs. (8)–(10); §1.1, p.4 (uSA(⊕))

import Mathlib
import Definitions.Def_LiftSAParity_SemSAXorRefutation

namespace LiftSAParity

open MvPolynomial

/-- The Boolean axioms `x_I(1 − x_I)` and `x̄_I(1 − x̄_I)` of `B_N` (de Rezende–Engström–Shekhovtsov,
*Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size*, manuscript (sha256
cab5a032…), §3, p.9, eq. (9)). -/
noncomputable def xorBoolAxiom {V : Type*} (Ib : Finset V × Bool) :
    MvPolynomial (Finset V × Bool) ℝ :=
  X Ib * (1 - X Ib)

/-- The parity axiom `x_I + x_J − 2 x_I x_J − x_{I△J}` of `D_N` (§3, p.9, eq. (10)). -/
noncomputable def xorParityAxiom {V : Type*} [DecidableEq V] (IJ : Finset V × Finset V) :
    MvPolynomial (Finset V × Bool) ℝ :=
  X (IJ.1, true) + X (IJ.2, true) - 2 * X (IJ.1, true) * X (IJ.2, true) -
    X (symmDiff IJ.1 IJ.2, true)

/-- **SA(⊕) refutation** (§3, p.9): "A SA(⊕) refutation π of P is a SA refutation of P, as in (7),
with the extended formal variables X̃_n and axioms Ã_n", where `Ã_n = B_n ∪ C_n ∪ D_n`
(eqs. (8)–(10)): polynomials `{q_p}_{p∈P∪Ã_n}` and `h_α` of the form (12) with
`∑_{p∈P∪Ã_n} p · q_p + h_α = −1` exactly. Here `P = {p_C : C ∈ φ}` over the variables `V` of `φ`.

**Formalization Note** Multipliers are indexed by the names of the axioms (a clause, a set `I` for
`c_I`, a pair `(I, b)` for a Boolean axiom, an ordered pair `(I, J)` for a parity axiom). The
names `(I, J)` and `(J, I)` give the same polynomial; merging their multipliers gives a
set-indexed refutation of no larger coefficient size, and conversely, so lower bounds on the
coefficient size are the same. -/
structure SAXorRefutation {V : Type*} [Fintype V] [DecidableEq V] (φ : CNF V) where
  /-- the multiplier of each clause monomial `p_C` -/
  qClause : φ → MvPolynomial (Finset V × Bool) ℝ
  /-- the multiplier of each complementarity axiom `c_I` -/
  qComp : Finset V → MvPolynomial (Finset V × Bool) ℝ
  /-- the multiplier of each Boolean axiom -/
  qBool : Finset V × Bool → MvPolynomial (Finset V × Bool) ℝ
  /-- the multiplier of each parity axiom -/
  qParity : Finset V × Finset V → MvPolynomial (Finset V × Bool) ℝ
  /-- the nonnegative part `h_α` -/
  h : MvPolynomial (Finset V × Bool) ℝ
  h_form : IsNonnegMultilinear h
  identity : (∑ C : φ, xorClauseMono C.1 * qClause C) +
      (∑ I : Finset V, xorCompAxiom I * qComp I) +
      (∑ Ib : Finset V × Bool, xorBoolAxiom Ib * qBool Ib) +
      (∑ IJ : Finset V × Finset V, xorParityAxiom IJ * qParity IJ) + h = -1

/-- The **coefficient size** of an SA(⊕) refutation (§3, p.9): the sum of the magnitudes of the
coefficients of all multipliers and of `h_α`. -/
noncomputable def SAXorRefutation.coeffSize {V : Type*} [Fintype V] [DecidableEq V]
    {φ : CNF V} (π : SAXorRefutation φ) : ℝ :=
  (∑ C : φ, coeffNorm (π.qClause C)) + (∑ I : Finset V, coeffNorm (π.qComp I)) +
    (∑ Ib : Finset V × Bool, coeffNorm (π.qBool Ib)) +
    (∑ IJ : Finset V × Finset V, coeffNorm (π.qParity IJ)) + coeffNorm π.h

end LiftSAParity


