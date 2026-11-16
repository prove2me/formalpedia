-- Prove2me | Definitions.Def_CubicProductLB_Supplement_HasMultilinearDegLEP
-- name    : CubicProductLB_Supplement_HasMultilinearDegLEP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:37:53.717568+00:00
-- url     : https://prove2.me/theorems/b40ff747-e2ee-4e21-b3c6-8982b3921c2b
-- title:
--   Multilinear degree at most $d$ on $\{-1,1\}^n \subseteq \mathbb F_p^n$
-- statement:
--   A function $f : \mathbb F_p^n \to \mathbb F_p$ has **multilinear degree at most $d$ on the sign cube** if some multilinear polynomial over $\mathbb F_p$ (every variable to power at most $1$) of total degree at most $d$ agrees with $f$ at every point of $\{-1,1\}^n$. Values off the cube are irrelevant.
--
--   This is the paper's degree convention (Definition 1, Section 2), which Sections 14 and 15.14 carry over: a factor may be replaced by its canonical multilinear representative on the cube without increasing its degree.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 1, pp.3–4; Section 14, p.43; Section 15.14, p.65

import Mathlib
import Definitions.Def_CubicProductLB_Supplement_signCubeP

namespace CubicProductLB.Supplement

/-- `f` has multilinear degree at most `d` on `{-1, 1}^n ⊆ F_p^n`: some multilinear polynomial over
`F_p` of total degree at most `d` agrees with `f` on the sign cube (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 1 and the paragraph
after it, pp.3–4; Section 14, p.43: "Every factor may be replaced by its canonical multilinear
representative on the sign cube without increasing its degree or its occurrence cost").

**Formalization Note** The base mission's `CubicProductLB.HasMultilinearDegLE` with `ZMod 3` replaced
by `ZMod p`. It is a condition on the function on the cube, not on a listing. -/
def HasMultilinearDegLEP {p n : ℕ} (d : ℕ) (f : (Fin n → ZMod p) → ZMod p) : Prop :=
  ∃ Q : MvPolynomial (Fin n) (ZMod p),
    (∀ m ∈ Q.support, ∀ i, m i ≤ 1) ∧ Q.totalDegree ≤ d ∧
      ∀ x ∈ signCubeP p n, MvPolynomial.eval x Q = f x

end CubicProductLB.Supplement


