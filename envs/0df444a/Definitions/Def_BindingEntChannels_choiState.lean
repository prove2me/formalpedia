-- Prove2me | Definitions.Def_BindingEntChannels_choiState
-- name    : BindingEntChannels_choiState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:38:50.082746+00:00
-- url     : https://prove2.me/theorems/e47fa2d0-c67f-4ef1-a5b9-fd7c8b0c6b6c
-- title:
--   The state $(I\otimes\Lambda)P^m_+$: half of the singlet sent through $\Lambda$
-- statement:
--   Let $\Lambda$ be a map from $m\times m$ to $n\times n$ complex matrices. The state
--
--   $$
--   (I\otimes\Lambda)P^m_+
--   $$
--
--   on $\mathbb C^m\otimes\mathbb C^n$ is obtained by applying $\Lambda$ to the second half of the singlet $P^m_+$ of Eq. (1) and leaving the first half untouched. Its matrix is $\frac1m\sum_{i,j}|i\rangle\langle j|\otimes\Lambda(|i\rangle\langle j|)$.
--
--   This is the state the Theorem characterizes binding entanglement channels by.
--
--   **Formalization Note** $P^m_+$ is the published maximally entangled state $|\Phi_m\rangle\langle\Phi_m|$ (entries $1/m$ at $((i,i),(j,j))$), the symmetric state of Eq. (1), not the two-qubit $\Psi^-$ that distillability targets. The untouched reference half is the first tensor factor (Alice holds it); the channel output is the second (Bob's). The factor $1/m$ of Eq. (1) is included, so for a channel the state has trace one; the paper's Eq. (4), which omits this factor, is not used. The paper once writes $(\Lambda^n_m\otimes I_m)P^m_+$ for this state, a typo.
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, Theorem, p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_ObliviousRSP_maxEnt

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (the Theorem): the state `(I ⊗ Λ)P^m_+` obtained by sending the second half of the
singlet `P^m_+` of Eq. (1) through the map `Λ`, acting on `C^m ⊗ C^n`.

**Formalization Note.** `P^m_+` is the symmetric maximally entangled state of Eq. (1), not the
two-qubit `Ψ⁻` targeted by `BoundEntPPT.IsDistillable`. The reference (untouched) half is the first factor and Alice holds it;
`Λ` acts on the second factor and its output is Bob's. This is `QAlgorithms.idTensorSuperop`
applied to the published singlet `ObliviousRSP.maxEnt I` (the projector onto
`(1/√|I|) Σ_i |i⟩|i⟩`, Eq. (1)), so the factor `1/m` of Eq. (1) is included and the state has trace
one for a channel (the paper's Eq. (4), which omits that factor, is not used). The paper writes
`(Λ^n_m ⊗ I_m)P^m_+` once on p. 2, a typo for this state. -/
noncomputable def choiState {I : Type} {O : Type*} [Fintype I] [DecidableEq I]
    (Λ : QAlgorithms.Superop I O) : Matrix (I × O) (I × O) ℂ :=
  QAlgorithms.idTensorSuperop (R := I) Λ (ObliviousRSP.maxEnt I)

end BindingEntChannels


