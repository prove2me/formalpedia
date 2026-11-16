-- Prove2me | Definitions.Def_IterRoundDet_Supplement_BasisPoly
-- name    : IterRoundDet_Supplement_BasisPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:04:52.513458+00:00
-- url     : https://prove2.me/theorems/45880b7e-b146-4054-84ba-7c61f5e9894c
-- title:
--   Weighted matroid basis polynomials $p_{\mathcal N,w}$ and the two-oracle input model of Theorem 1.3
-- statement:
--   Let $\mathcal N$ be a matroid on $[n]$ of rank $d$ and let $w_1,\dots,w_n$ be positive rational weights. The **weighted matroid basis polynomial** of $\mathcal N$ is
--
--   $$p_{\mathcal N,w}(z)=\sum_{I\in\mathcal B(\mathcal N)} w^I z^I,\qquad w^I=\prod_{i\in I}w_i,\quad z^I=\prod_{i\in I}z_i,$$
--
--   a homogeneous multiaffine polynomial of degree $d$ whose coefficient on $z^S$ is $w^S$ when $S$ is a base of $\mathcal N$ and $0$ otherwise. At an indicator vector it is $p_{\mathcal N,w}(\mathbf 1_B)=\sum_{I\in\mathcal B(\mathcal N),\,I\subseteq B} w^I$.
--
--   The file also fixes how an algorithm for Theorem 1.3 receives its instance:
--
--   1. the **oracle model** `basisModel M N`: tag $0$ is the independence oracle for the constraint matroid $\mathcal M$, tag $1$ the independence oracle for $\mathcal N$ (sets encoded as characteristic words, as in the base mission's oracles); any other tag answers $[0]$;
--   2. the **weight bit bound** $b$: every weight's numerator (in absolute value) and denominator, in lowest terms, is below $2^b$.
--
--   The weighted basis polynomials are the canonical completely log-concave polynomials that need not be real stable; they are the subject of Section 5.1 of the paper.
--
--   **Formalization Note** The polynomial is stored as its coefficient function and evaluated with the base mission's `pEval`; it is not assumed stable. Weights are rational, as Section 5.1 fixes them.
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), §1.1 before Theorem 1.3, p.3 (PDF p.4); §5.1, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Machine
import Definitions.Def_IterRoundDet_Oracles

set_option autoImplicit false

namespace IterRoundDet.Supplement

/-!
# Weighted matroid basis polynomials and the input model of Theorem 1.3

N. Bansal, W. Li, M. Singh, Y. Xu, *Iterative Rounding for Determinant Maximization and Real Stable
Polynomials*, STOC 2027 submission (manuscript sha256 aa18bcee…), §1.1, p.3 (PDF p.4), and §5.1,
p.24 (PDF p.25): for a matroid `N` of rank `d` on `[n]` and positive weights `w`,
`p_{N,w}(z) = ∑_{I ∈ B(N)} w^I z^I` with `w^I = ∏_{i∈I} w_i`.

**Formalization Note.** The polynomial is its coefficient function, as in `IterRoundDet.StablePoly`:
the coefficient of `z^S` is `∏_{i∈S} w_i` when `S` is a base of `N` and `0` otherwise; it is evaluated
with the published `IterRoundDet.pEval`. It is not assumed real stable (§5.1: it need not be).
Weights are rational, as §5.1 fixes them ("positive rational weights"). Theorem 1.3's algorithm sees
`N` and `M` through independence oracles, the encodings of `IterRoundDet.Oracles`, and the weights on
its input tape.
-/

open IterRoundDet

variable {n : ℕ}

open Classical in
/-- §5.1, p.24: the coefficients of the weighted matroid basis polynomial `p_{N,w}`:
`c_S = ∏_{i∈S} w_i` if `S ∈ B(N)`, else `0`. -/
noncomputable def basisCoef (N : Matroid (Fin n)) (w : Fin n → ℚ) : Finset (Fin n) → ℚ :=
  fun S => if N.IsBase (S : Set (Fin n)) then ∏ i ∈ S, w i else 0

/-- Theorem 1.3's oracle model: tag `0` is the independence oracle for the constraint matroid `M`,
tag `1` the independence oracle for `N`. Other tags answer `[0]`. -/
noncomputable def basisModel (M N : Matroid (Fin n)) : Oracle :=
  fun tag q =>
    match tag with
    | 0 => indepAnswer M q
    | 1 => indepAnswer N q
    | _ => [0]

/-- `b` bounds the bit length of every weight: each numerator (in absolute value) and each
denominator, in lowest terms, is below `2^b` (the shape of `IterRoundDet.BitBounded`). -/
def WeightBits (b : ℕ) (w : Fin n → ℚ) : Prop :=
  ∀ i, (w i).num.natAbs < 2 ^ b ∧ (w i).den < 2 ^ b

end IterRoundDet.Supplement


