-- Prove2me | Definitions.Def_RainsSep_Distill_polyS
-- name    : RainsSep_Distill_polyS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T16:01:09.26141+00:00
-- url     : https://prove2.me/theorems/c9f0021d-fae4-45cf-b574-c81b5c23a562
-- title:
--   The shadow polynomial $S(x,y)=B\big(\tfrac{3y-x}{2},\tfrac{x+y}{2}\big)$
-- statement:
--   For a superoperator $\mathcal P$ from two $n$-qubit registers to $\mathbb C^K\otimes\mathbb C^K$,
--
--   $$
--   S(x,y)=B\Big(\frac{3y-x}{2},\frac{x+y}{2}\Big),
--   $$
--
--   the polynomial obtained by substituting into $B$. It is the analogue of the shadow enumerator of a code; the bound $(x+3y)^n/K\ge S(x,y)$ for $x,y\ge0$ yields Theorem 1.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (33), p. 3

import Mathlib
import Definitions.Def_RainsSep_Distill_polyB

namespace RainsSep.Distill

/-- **The shadow polynomial `S(x, y) = B((3y − x)/2, (x + y)/2)`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (33), p. 3: "where S(x, y) = B((3y − x)/2, (x + y)/2). (33)"

**Formalization Note.** A formal polynomial in `x = X 0`, `y = X 1`, obtained by substituting
into `polyB P`. -/
noncomputable def polyS {n K : ℕ}
    (P : QAlgorithms.Superop (QAlgorithms.Qubits n × QAlgorithms.Qubits n) (Fin K × Fin K)) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.bind₁
    ![MvPolynomial.C (1 / 2) * (3 * MvPolynomial.X 1 - MvPolynomial.X 0),
      MvPolynomial.C (1 / 2) * (MvPolynomial.X 0 + MvPolynomial.X 1)] (polyB P)

end RainsSep.Distill


