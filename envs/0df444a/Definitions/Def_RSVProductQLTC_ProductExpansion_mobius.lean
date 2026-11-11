-- Prove2me | Definitions.Def_RSVProductQLTC_ProductExpansion_mobius
-- name    : RSVProductQLTC_ProductExpansion_mobius
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:32.954376+00:00
-- url     : https://prove2.me/theorems/0488e514-dd1f-4b08-a8fd-486aea2e1a4c
-- title:
--   Projective Möbius label and scale
-- statement:
--   Let $K$ be a field, $B$ an invertible $2\times2$ matrix over $K$, and $a\in K\cup\{\infty\}$. For the fixed representatives $r_a$, define the label $\beta_B(a)$ and the nonzero scalar $\lambda_B(a)$ through
--   $$B r_a=\lambda_B(a)r_{\beta_B(a)}.$$
--   For a vector $v=(u,v_1)$ with $v_1\ne0$, the label is $u/v_1$ and the scale is $v_1$; if $v_1=0$, the label is infinity and the scale is $u$. This covers both poles and the infinity input and specifies the scaled code symmetry.
--
--   **Formalization Note** These functions also have total values for singular matrices and the zero vector: the zero vector has label infinity and scale zero. Claim 3.5 assumes invertibility, so those defaults are never used in its image equality.
-- source:
--   Mitali Bafna, Anqi Li, Quynh T. Nguyen, STOC 2027 submission #1136 (October 2026), §3.2, Möbius transformations preceding Claim 3.5, printed p.9 (PDF p.10)

import Mathlib
import Definitions.Def_RSVProductQLTC_ProductExpansion_projectiveLine
set_option autoImplicit false

open Classical

namespace RSVProductQLTC.ProductExpansion

/-- §3.2: the projective label of a vector, with the zero-vector default unused for invertible B. -/
noncomputable def vectorLabel {K : Type} [Field K] (v : Fin 2 → K) : ProjectiveLine K :=
  if v 1 = 0 then none else some (v 0 / v 1)

/-- Möbius action, also defined at a pole and infinity. -/
noncomputable def mobiusLabel {K : Type} [Field K]
    (B : Matrix (Fin 2) (Fin 2) K) (a : ProjectiveLine K) : ProjectiveLine K :=
  vectorLabel (B.mulVec (projectiveRep a))

/-- Scale in `B r_a = λ_B(a) r_(β_B(a))`; nonzero for invertible B. -/
noncomputable def mobiusScale {K : Type} [Field K]
    (B : Matrix (Fin 2) (Fin 2) K) (a : ProjectiveLine K) : K :=
  let v := B.mulVec (projectiveRep a)
  if v 1 = 0 then v 0 else v 1

end RSVProductQLTC.ProductExpansion


