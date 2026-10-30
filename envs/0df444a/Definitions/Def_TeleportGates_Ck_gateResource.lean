-- Prove2me | Definitions.Def_TeleportGates_Ck_gateResource
-- name    : TeleportGates_Ck_gateResource
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:14.027409+00:00
-- url     : https://prove2.me/theorems/3ea35a4f-a262-488b-9594-1e327a20017d
-- title:
--   Resource state $(I\otimes U)\Phi$: $U$ applied to the second register
-- statement:
--   Let $\iota$ be a finite index set, $\Phi$ a vector of the two-register space $\mathbb C^{\iota}\otimes\mathbb C^{\iota}$ and $U$ an operator on $\mathbb C^{\iota}$. Then
--
--   $$\bigl((I\otimes U)\Phi\bigr)(b,c)=\sum_{c'}U_{c\,c'}\,\Phi(b,c').$$
--
--   With $\Phi=|\Psi^n\rangle$ this is the paper's resource state $|\Psi^n_U\rangle=(I\otimes U)|\Psi^n\rangle$ of Eq. (3): $U$ acting on the lower qubits of all the EPR pairs.
--
--   **Formalization Note** Defined for every square matrix $U$, not only unitaries.
-- source:
--   Gottesman, Chuang, Quantum teleportation is a universal computational primitive, arXiv:quant-ph/9908010v1, §II, Eq. (3), p. 3; and p. 2 ('(I ⊗ U)|Ψn⟩ … is U acting on the lower qubits of all the EPR pairs')

import Mathlib

namespace TeleportGates.Ck

/-- **The resource state `(I ⊗ U)Φ`: `U` applied to the second register.**
Gottesman, Chuang, *Quantum teleportation is a universal computational primitive*,
arXiv:quant-ph/9908010v1, §II, Eq. (3), p. 3: "|Ψn_U⟩ = (I ⊗ U)|Ψn⟩", and
p. 2: "(I ⊗ U)|Ψn⟩ (where I is the identity on n qubits) is U acting on the lower qubits of all
the EPR pairs."

For a state `Φ` of two registers with index set `ι` each and an operator `U` on `ι`,
`gateResource U Φ (b, c) = ∑_{c'} U c c' · Φ (b, c')`, the vector `(I ⊗ U)Φ`. The paper's
`|Ψⁿ_U⟩` is `gateResource U (eprState n)`.

**Formalization Note.** Defined for every square matrix `U` (not only unitaries) and every finite
index type. The first register (upper qubits) is left alone, `U` acts on the second (lower
qubits). -/
noncomputable def gateResource {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ)
    (Φ : EuclideanSpace ℂ (ι × ι)) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 fun p => ∑ c' : ι, U p.2 c' * Φ (p.1, c')

end TeleportGates.Ck


