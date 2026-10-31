-- Prove2me | Definitions.Def_RainsSep_Distill_polyB
-- name    : RainsSep_Distill_polyB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T16:00:09.990383+00:00
-- url     : https://prove2.me/theorems/29119c2e-6b94-487a-a042-3fa592516c68
-- title:
--   The enumerator polynomial $B(x,y)=\sum_i B_i(\mathcal P)x^{n-i}y^i$
-- statement:
--   For a superoperator $\mathcal P$ from two $n$-qubit registers to $\mathbb C^K\otimes\mathbb C^K$,
--
--   $$
--   B(x,y)=\sum_{i=0}^n B_i(\mathcal P)\,x^{n-i}y^i ,
--   $$
--
--   a homogeneous polynomial of degree $n$ in two variables with real coefficients. By Eq. (21), $B(f,(1-f)/3)$ is the output fidelity of $\mathcal P$ on $\Delta(\epsilon)^{\otimes n}$.
--
--   **Formalization Note** A formal polynomial in two variables $x,y$ with real coefficients, so that statements about its coefficients can be made.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (25), p. 2

import Mathlib
import Definitions.Def_RainsSep_Distill_enumB

namespace RainsSep.Distill

/-- **The enumerator polynomial `B(x, y) = Σ_i B_i(P) x^{n−i} y^i`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (25), p. 2: "B′(1, 0, x − y, 2y) = B(x, y) = Σ_i B_i(P) x^{n−i} y^i. (25)"

A polynomial in two variables `x = X 0`, `y = X 1` with real coefficients `B_i(P)`.

**Formalization Note.** A formal polynomial (`MvPolynomial (Fin 2) ℝ`), so that statements about
its coefficients can be made. -/
noncomputable def polyB {n K : ℕ}
    (P : QAlgorithms.Superop (QAlgorithms.Qubits n × QAlgorithms.Qubits n) (Fin K × Fin K)) :
    MvPolynomial (Fin 2) ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    MvPolynomial.C (enumB P j) * MvPolynomial.X 0 ^ (n - j) * MvPolynomial.X 1 ^ j

end RainsSep.Distill


