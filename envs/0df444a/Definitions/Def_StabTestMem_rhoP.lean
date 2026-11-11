-- Prove2me | Definitions.Def_StabTestMem_rhoP
-- name    : StabTestMem_rhoP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:30.298404+00:00
-- url     : https://prove2.me/theorems/a473a2e2-49ce-49f0-b0fc-246d77269147
-- title:
--   Phase-state moment $\rho_P=\mathbb E_A[\psi_A^{\otimes t}]$
-- statement:
--   The $t$-copy moment of a uniformly random degree-2 phase state:
--
--   $$\rho_P=\mathbb E_A\big[(|\psi_A\rangle\langle\psi_A|)^{\otimes t}\big],$$
--
--   the average over upper-triangular $A\in\mathbb F_2^{n\times n}$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §3.2, p. 21; §5.2, p. 38; Theorem 5.5, p. 39

import Definitions.Def_StabTestMem_IsUpperTri
import Definitions.Def_StabTestMem_phaseState
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_WildeQIT_Schumacher_tensorPow

namespace StabTestMem

open QAlgorithms

open Classical in
/-- **The phase-state moment `ρ_P = E_A[ψ_A^{⊗t}]`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §3.2, p. 21 ("ρ_P := E_A[ψ_A^{⊗t}]"),
§5.2, p. 38, item 1, and Theorem 5.5, p. 39.

The uniform average of `|ψ_A⟩⟨ψ_A|^{⊗t}` over the upper-triangular `A ∈ F₂^{n×n}`. -/
noncomputable def rhoP (n t : ℕ) : Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ :=
  ((Finset.univ.filter fun A : Matrix (Fin n) (Fin n) (ZMod 2) => IsUpperTri A).card : ℂ)⁻¹ •
    ∑ A ∈ Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => IsUpperTri A),
      WildeQIT.Schumacher.tensorPow t (ObliviousRSP.pureState (phaseState A))

end StabTestMem


