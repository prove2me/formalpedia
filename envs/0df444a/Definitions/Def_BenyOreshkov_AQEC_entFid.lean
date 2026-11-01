-- Prove2me | Definitions.Def_BenyOreshkov_AQEC_entFid
-- name    : BenyOreshkov_AQEC_entFid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:22.999043+00:00
-- url     : https://prove2.me/theorems/ee510c19-13e1-4545-ab1c-f179a1ca1dcb
-- title:
--   Entanglement fidelity $F_\rho(\mathcal N,\mathcal M)$ between two channels
-- statement:
--   Let $f(\rho,\sigma)=\mathrm{Tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho}$ be the (root) fidelity between states $\rho$ and $\sigma$. For channels $\mathcal N,\mathcal M$ from $A$ to a space $X$ and a state $\rho$ on $A$, the **entanglement fidelity** between $\mathcal N$ and $\mathcal M$ at $\rho$ is
--   $$
--   F_\rho(\mathcal N,\mathcal M) = f\big((\mathrm{id}\otimes\mathcal N)(|\psi_\rho\rangle\langle\psi_\rho|),\ (\mathrm{id}\otimes\mathcal M)(|\psi_\rho\rangle\langle\psi_\rho|)\big),
--   $$
--   where $|\psi_\rho\rangle$ is a purification of $\rho$ on $A_{\mathrm{ref}}\otimes A$ and the channels act on $A$ only. When $\mathcal M=\mathrm{id}$ this is (the square root of) Schumacher's entanglement fidelity of $\mathcal N$.
--
--   **Formalization Note** $f$ is the platform's `QAlgorithms.rootFidelity` (root, not squared), with square roots taken by `cfc Real.sqrt`; on the positive semidefinite arguments that occur here it is the positive square root. The purification is the canonical one, reference first, and $\mathrm{id}\otimes\mathcal N$ is `QAlgorithms.idTensorSuperop` (the paper writes $\mathcal N\otimes\mathrm{id}$; only the order of the factors differs).
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, §Main result, p. 2 (definition of f and F_ρ)

import Definitions.Def_BenyOreshkov_AQEC_purif
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation

open Matrix QAlgorithms

namespace BenyOreshkov.AQEC

/-- **Entanglement fidelity between two channels.** Bény, Oreshkov, arXiv:0907.5391v4,
§Main result, p. 2: with `f(ρ, σ) = Tr √(√ρ σ √ρ)` the fidelity,
`F_ρ(N, M) = f((N ⊗ id)(|ψ⟩⟨ψ|), (M ⊗ id)(|ψ⟩⟨ψ|))`, where `|ψ⟩` is a purification of `ρ`.

**Formalization Note** `f` is `QAlgorithms.rootFidelity` (the root fidelity, not its square),
with square roots by `cfc Real.sqrt`, which is the positive square root on the positive
semidefinite arguments that occur here. `|ψ⟩⟨ψ|` is the canonical purification `purif ρ`, with
the reference system first; `N ⊗ id` is `QAlgorithms.idTensorSuperop N` (identity on the first,
reference, factor). -/
noncomputable def entFid {A X : Type} [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X]
    (ρ : Matrix A A ℂ) (N M : Superop A X) : ℝ :=
  rootFidelity (idTensorSuperop (R := A) N (purif ρ)) (idTensorSuperop (R := A) M (purif ρ))

end BenyOreshkov.AQEC


