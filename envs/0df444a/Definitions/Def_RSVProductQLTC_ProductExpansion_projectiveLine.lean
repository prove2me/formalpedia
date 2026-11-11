-- Prove2me | Definitions.Def_RSVProductQLTC_ProductExpansion_projectiveLine
-- name    : RSVProductQLTC_ProductExpansion_projectiveLine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:35:51.038083+00:00
-- url     : https://prove2.me/theorems/b712fdf2-b503-4991-a564-dea42a8f1e14
-- title:
--   Projective labels and homogeneous polynomial evaluation
-- statement:
--   Let $K$ be a field. Its **projective line** is represented by $A=K\cup\{\infty\}$, with fixed representatives
--   $$r_x=(x,1)^{\mathsf T}\quad(x\in K),\qquad r_\infty=(1,0)^{\mathsf T}.$$
--   For coefficients $f_0,\ldots,f_d$ in a field $E$, evaluation of the homogeneous polynomial of degree $d$ means
--   $$f(v_0,v_1)=\sum_{j=0}^{d}f_j v_0^jv_1^{d-j}.$$
--   The Frobenius label map sends $x$ to $x^{2^h}$ and fixes $\infty$. It acts on evaluation labels, rather than on the coefficients of $f$. These conventions specify the coordinates used by the projective codes and the later local constraints.
--
--   **Formalization Note** `Option K` represents the projective line, with `none` for infinity. `Fin (d+1)` includes exactly the coefficient indices $0,\ldots,d$, including the degree-zero case. Definitions are total on all fields; the finite and characteristic-two hypotheses are supplied at the source uses.
-- source:
--   Mitali Bafna, Anqi Li, Quynh T. Nguyen, STOC 2027 submission #1136 (October 2026), §3.2, printed p.8 (PDF p.9), projective coordinates and Definition 3.3; §4.2, printed p.11 (PDF p.12), Frobenius label permutation

import Mathlib
set_option autoImplicit false

namespace RSVProductQLTC.ProductExpansion

/-- §3.2, printed p.8 (PDF p.9). `none` is infinity. -/
abbrev ProjectiveLine (K : Type) := Option K

/-- Fixed projective representatives: `(x,1)` and `(1,0)`. -/
def projectiveRep {K : Type} [Field K] : ProjectiveLine K → Fin 2 → K
  | some x => ![x, 1]
  | none => ![1, 0]

/-- Frobenius acts on the labels, fixing infinity; it does not act on coefficients. -/
def frobeniusLabel {K : Type} [Field K] (h : ℕ) : ProjectiveLine K → ProjectiveLine K :=
  Option.map (fun x => x ^ (2 ^ h))

/-- Homogeneous bivariate degree-d polynomial in its d+1 coefficients, including zero. -/
def homogeneousEval {E : Type} [Field E] (d : ℕ) (f : Fin (d + 1) → E)
    (v : Fin 2 → E) : E :=
  ∑ j, f j * v 0 ^ j.val * v 1 ^ (d - j.val)

end RSVProductQLTC.ProductExpansion


