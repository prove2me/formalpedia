-- Prove2me | Definitions.Def_StabTestMem_Aval
-- name    : StabTestMem_Aval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:08.35145+00:00
-- url     : https://prove2.me/theorems/7a43eebd-9628-48d4-b5e2-e3afd1f48031
-- title:
--   Largest Pauli completion $A(a,r)$ of a prefix
-- statement:
--   For a state $|\psi\rangle$ on $k+m$ qubits and a prefix $(a,r)$,
--
--   $$A(a,r)=\max_{t\in\mathbb F_2^m}\big|\langle\psi|P_{a_Xr,\,a_Zt}|\psi\rangle\big|,$$
--
--   the closest any completion of $(a,r)$ to a full Pauli string comes to stabilizing $|\psi\rangle$ (ignoring phases). It controls the soundness of the affine-graph test (Lemma 4.5).
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Eq. (55), p. 30

import Definitions.Def_StabTestMem_weyl
import Definitions.Def_StabTestMem_concat

namespace StabTestMem

open QAlgorithms

/-- **Largest Pauli completion of a prefix, `A(a, r)`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Eq. (55), p. 30 (restated in
Lemma 4.5): "A(a, r) := max_{t∈F_2^{n−k}} |⟨ψ|P_{a_X r, a_Z t}|ψ⟩|".

The maximum over the `2^m` completions `t` is a finite `sup'` (the index set is nonempty). -/
noncomputable def Aval {k m : ℕ} (ψ : EuclideanSpace ℂ (Qubits (k + m))) (a : CutRankSched.Pauli k)
    (r : Fin m → ZMod 2) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun t : Fin m → ZMod 2 =>
    ‖inner ℂ ψ (act (weyl (concat a r t)) ψ)‖

end StabTestMem


