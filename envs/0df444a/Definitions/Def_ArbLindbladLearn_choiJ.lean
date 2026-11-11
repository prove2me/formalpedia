-- Prove2me | Definitions.Def_ArbLindbladLearn_choiJ
-- name    : ArbLindbladLearn_choiJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:25.963193+00:00
-- url     : https://prove2.me/theorems/733e44ff-8b7b-4280-9817-3363de7addf8
-- title:
--   Choi operator $J(\mathcal N)=(\mathrm{id}\otimes\mathcal N)(|\Phi_0\rangle\langle\Phi_0|)$
-- statement:
--   The Choi operator of a superoperator $\mathcal N$ is
--   $$J(\mathcal N)=(\mathrm{id}\otimes\mathcal N)\big(|\Phi_0\rangle\langle\Phi_0|\big).$$
--   For $\mathcal N=e^{t\mathcal L}$ it is the Choi state $J_t$, and for $\mathcal N=\mathcal L$ it is the endpoint derivative $J_0'=(\mathrm{id}\otimes\mathcal L)(|\Phi_0\rangle\langle\Phi_0|)$.
--
--   **Formalization Note** Reference factor first; the entry at $((r,s),(r',s'))$ is $\mathcal N(|r\rangle\langle r'|)_{ss'}/d$. The public `choi` puts the system first and is not used.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Definition 2.9, p.15; J_t and J′₀, p.19

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The Choi operator `J(𝒩) = (id ⊗ 𝒩)(|Φ₀⟩⟨Φ₀|)` of a superoperator (Definition 2.9,
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.15). For `𝒩 = e^{tℒ}` it is `J_t` (p.19); for `𝒩 = ℒ` it is
`J′₀ = (id ⊗ ℒ)(|Φ₀⟩⟨Φ₀|)` (p.19).

**Formalization Note** The reference factor is first, as in the paper. Since
`|Φ₀⟩⟨Φ₀| = d⁻¹ Σ_{j,l} |j⟩⟨l| ⊗ |j⟩⟨l|`, the entry at `((r, s), (r′, s′))` is
`𝒩(|r⟩⟨r′|)_{s s′} / d`, i.e. `g (s, s′) (r, r′) / d` for the superoperator matrix `g`. This differs
from the public `choi`, which puts the system first. The definition is linear in `g`, so it is
also used for generators, which are not channels. -/
def choiJ {n : ℕ} (g : Super (Qubits n) (Qubits n)) : Op (Qubits n × Qubits n) :=
  fun x y => g (x.2, y.2) (x.1, y.1) / ((2 : ℂ) ^ n)

end ArbLindbladLearn


