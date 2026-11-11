-- Prove2me | Definitions.Def_StabTestMem_charDist
-- name    : StabTestMem_charDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:58.822862+00:00
-- url     : https://prove2.me/theorems/8a109a32-a60a-490f-8ad9-778dc3c463d5
-- title:
--   Characteristic distribution $p_\psi(u)=2^{-n}|\langle\psi|P_u|\psi\rangle|^2$
-- statement:
--   For an $n$-qubit pure state $|\psi\rangle$ the **characteristic distribution** on labels is
--
--   $$p_\psi(u)=2^{-n}\,|\langle\psi|P_u|\psi\rangle|^2,\qquad u\in\mathbb F_2^{2n}.$$
--
--   For a unit vector it is a probability distribution; for a stabilizer state it is uniform on $M_\psi$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §2.1, Characteristic distribution, p. 15

import Definitions.Def_StabTestMem_weyl

namespace StabTestMem

open QAlgorithms

/-- **Characteristic distribution `p_ψ(u) = 2^{−n} |⟨ψ|P_u|ψ⟩|²`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §2.1, "Characteristic
distribution", p. 15: "c_ψ(u) := 2^{−n/2} Tr(P_u ψ), p_ψ(u) := |c_ψ(u)|^2 = 2^{−n}|⟨ψ|P_u|ψ⟩|^2".

For a unit vector `ψ` this is a probability distribution on the `4ⁿ` Pauli labels. -/
noncomputable def charDist {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (u : CutRankSched.Pauli n) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ‖inner ℂ ψ (act (weyl u) ψ)‖ ^ 2

end StabTestMem


