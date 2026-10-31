-- Prove2me | Definitions.Def_RainsSep_Distill_enumB
-- name    : RainsSep_Distill_enumB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:59:08.776333+00:00
-- url     : https://prove2.me/theorems/54f930d0-c8c3-42bf-84a1-3811529c60a3
-- title:
--   The enumerator coefficient $B_j(\mathcal P)=\sum_{\mathrm{wt}(E)=j}F_{\mathcal P}(E)$
-- statement:
--   For a superoperator $\mathcal P$ from two $n$-qubit registers to $\mathbb C^K\otimes\mathbb C^K$ and $0\le j\le n$,
--
--   $$
--   B_j(\mathcal P)=\sum_{\mathrm{wt}(E)=j}F_{\mathcal P}(E),
--   $$
--
--   the sum over all $n$-qubit Pauli products $E$ with exactly $j$ non-identity factors. These are the coefficients of the polynomial $B(x,y)$ whose value at $(f,(1-f)/3)$ is the output fidelity on $\Delta^{\otimes n}$.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (22), p. 2

import Mathlib
import Definitions.Def_RainsSep_Distill_pauliFid

namespace RainsSep.Distill

/-- **The enumerator coefficient `B_j(P)`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (22), p. 2: "where E ranges over the set E of tensor products of matrices from the set
{1, σx, σy, σz}, and wt(E) is the number of components in the tensor product not equal to the
identity. The quantity B_j(P) = Σ_{wt(E)=j} F_P(E) (22)".

`B_j(P)` is the sum of `F_P(E)` over the `n`-qubit Pauli products `E` of weight `j`. -/
noncomputable def enumB {n K : ℕ}
    (P : QAlgorithms.Superop (QAlgorithms.Qubits n × QAlgorithms.Qubits n) (Fin K × Fin K))
    (j : ℕ) : ℝ :=
  ∑ o ∈ Finset.univ.filter (fun o : Fin n → QAlgorithms.Stabilizer.Pauli =>
      QAlgorithms.opsWeight o = j), pauliFid P o

end RainsSep.Distill


