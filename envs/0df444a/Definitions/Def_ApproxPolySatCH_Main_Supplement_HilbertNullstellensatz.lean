-- Prove2me | Definitions.Def_ApproxPolySatCH_Main_Supplement_HilbertNullstellensatz
-- name    : ApproxPolySatCH_Main_Supplement_HilbertNullstellensatz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:53:55.586201+00:00
-- url     : https://prove2.me/theorems/bd250fef-4f37-45dd-89ea-1e05465e54a5
-- title:
--   Exact common zeros and the sparse Hilbert Nullstellensatz language
-- statement:
--   Let $k$ be a field, $K=\overline{k}$ its algebraic closure, and $f=(f_1,\ldots,f_m)$ a finite tuple of polynomials in $n$ variables. Exact common-zero feasibility means
--   $$\operatorname{ExactZero}(f)\iff \exists x\in K^n\;\forall i\in\{1,\ldots,m\},\ f_i(x)=0.$$
--   For a rational or presented finite coefficient field, the sparse Hilbert Nullstellensatz language is
--   $$\mathrm{HN}_{k,\mathrm{sparse}}=\{\operatorname{encodeSparse}(S):\operatorname{ValidSparse}_k(S)\ \text{and}\ \operatorname{ExactZero}(\operatorname{sparsePolynomials}_k(S))\}.$$
--   The polynomial interpretation, binary exponents, scalar codes and validity predicate are exactly the published input interface. Invalid words are no instances. Empty systems, zero polynomials, constants and zero variables are allowed; no certificate is assumed.
--
--   This definition distinguishes exact solvability from image-closure membership while keeping precisely the same sparse encodings. It supplies the source language for Theorem 15.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §2, HN definition and §6, Theorem 15, p.6,26–27 (PDF p.6,26–27), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=6

import Definitions.Def_ApproxPolySatCH_Main_Inputs

set_option autoImplicit false

namespace ApproxPolySatCH.Main.Supplement

/-- Exact common zeros are taken in the algebraic closure, just as for APS. -/
def ExactZero {k : Type} [Field k] {n m : ℕ} (f : Fin m → Poly k n) : Prop :=
  ∃ x : Fin n → AlgebraicClosure k,
    ∀ i : Fin m, MvPolynomial.eval₂ (algebraMap k (AlgebraicClosure k)) x (f i) = 0

/-- The source's default sparse HN problem, with exactly the published input validity. -/
noncomputable def HNSparseLanguage (k : CoefficientField) : Language :=
  {w | ∃ (n : ℕ) (S : SparseSystem n), w = encodeSparse S ∧
    ValidSparse k S ∧ ExactZero (sparsePolynomials k S)}

end ApproxPolySatCH.Main.Supplement


