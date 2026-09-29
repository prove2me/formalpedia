-- Prove2me | Definitions.Def_clearedDerivativeRows
-- name    : clearedDerivativeRows
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-12T17:33:03.798485+00:00
-- url     : https://prove2.me/theorems/4c8cf3da-f825-4750-9986-2ce830646dd5
-- title:
--   Polynomial numerator rows for repeated differentiation
-- statement:
--   Let $T\in\mathbb Q[X]$, let $B$ be an $m\times m$ matrix over $\mathbb Q[X]$, and let $P$ be a polynomial row over $\mathbb C$. After embedding rational polynomials in $\mathbb C[X]$, define
--
--   $$R_0(P)=P,\qquad R_{k+1}(P)=T R_k(P)' + R_k(P)B-kT'R_k(P).$$
--
--   These are polynomial rows; the recurrence uses no division. For a formal system $Tf'=Bf$, the associated intended numerator identity is $R_k(P)f=T^k(Pf)^{(k)}$. That identity is a proof obligation, not an additional axiom of this definition. The correction term accounts for the changing denominator under repeated differentiation.
-- source:
--   Auxiliary formalization of Beukers, A refined version of the Siegel–Shidlovskii theorem, Theorem 3.2, printed pp. 6–7 (prescribed derivative rows and determinant equation), https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf. These explicit polynomial-numerator and module-coordinate interfaces are derived from the proof, not quoted named lemmas.

import Definitions.Def_beukersLiftingData

noncomputable section
open scoped BigOperators
namespace ArithmeticE

/-- Polynomial numerators of differentiated coefficient rows for `T f' = B f`.
If `F = ∑ i, P i * f i`, their contractions with `f` are `T^k * F^(k)`.
The term `-k T' R_k` compensates for differentiating the denominator `T^k`. -/
def clearedDerivativeRows {m : ℕ} (T : Polynomial ℚ)
    (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (P : Fin m → Polynomial ℂ) : ℕ → Fin m → Polynomial ℂ
  | 0 => P
  | k + 1 => fun i =>
      T.map (algebraMap ℚ ℂ) * (clearedDerivativeRows T B P k i).derivative +
      (∑ j, clearedDerivativeRows T B P k j * (B j i).map (algebraMap ℚ ℂ)) -
      Polynomial.C (k : ℂ) * (T.map (algebraMap ℚ ℂ)).derivative *
        clearedDerivativeRows T B P k i

end ArithmeticE


