-- Prove2me | Definitions.Def_ShorEBAdditivity_sigmaABC
-- name    : ShorEBAdditivity_sigmaABC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:53.177194+00:00
-- url     : https://prove2.me/theorems/4206c75e-346b-4223-97c0-282ad36442e2
-- title:
--   The flagged state $\sigma_{ABC}$ of eq. (19)
-- statement:
--   Let $\Psi : M_A \to M_{A'}$ be a map, $q_1,\dots,q_m$ real numbers, $|a_j\rangle \in \mathbb C^A$ and $|b_j\rangle \in \mathbb C^{B'}$ vectors. The **flagged state** is
--
--   $$
--   \sigma_{ABC} = \sum_{j=1}^m q_j\, \Psi(|a_j\rangle\langle a_j|) \otimes |b_j\rangle\langle b_j| \otimes |j\rangle\langle j| ,
--   $$
--
--   an operator on $\mathcal H_{A'}\otimes\mathcal H_{B'}\otimes\mathbb C^m$, where $\{|j\rangle\}$ is the standard basis of a classical flag register $C = \mathbb C^m$.
--
--   In Shor's proof the data $q_j, |a_j\rangle, |b_j\rangle$ come from the separable decomposition (18) of $(I\otimes\Phi)(\rho_i)$, and strong subadditivity is applied to $\sigma_{ABC}$.
--
--   **Formalization Note** The registers are ordered $(A'\times B')\times C$. Hence $\sigma_{AB}$ is the partial trace over the last factor (`traceRight`), $\sigma_B$ is `traceLeft (traceRight σ)`, and $\sigma_{BC}$ is `traceLeft` of $\sigma$ after reassociating to $A'\times(B'\times C)$. No condition on $q$, $a$, $b$ is built in.
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (19), p.4 (and eq. (8), p.2)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel

open QAlgorithms
open scoped Kronecker

namespace ShorEBAdditivity

/-- Shor, arXiv:quant-ph/0201149v3, eq. (19), p.4 (and eq. (8), p.2): the flagged state
`σ_ABC = Σ_j q_j Ψ(|a_j⟩⟨a_j|) ⊗ |b_j⟩⟨b_j| ⊗ |j⟩⟨j|`
built from the data `q_j, |a_j⟩, |b_j⟩` of a decomposition (18), with `|j⟩` an orthonormal flag
basis of a classical register `C`.

**Formalization Note.** The register order is `((A' × B') × Fin m)`: the output of `Ψ` (the
paper's system A), then the output of `Φ` (system B), then the flag register C, built as the
Kronecker product `(Ψ(|a_j⟩⟨a_j|) ⊗ₖ |b_j⟩⟨b_j|) ⊗ₖ |j⟩⟨j|`. Hence `σ_AB = traceRight σ`,
`σ_B = traceLeft (traceRight σ)`, and `σ_BC` is `traceLeft` of `σ` reindexed along
`Equiv.prodAssoc A' B' (Fin m)`. `|a⟩⟨a|` is `QAlgorithms.pureDensity a`; `|j⟩⟨j|` is
`Matrix.single j j 1`. No condition on `q`, `a`, `b` is built in. -/
noncomputable def sigmaABC {A A' B' : Type*} {m : ℕ} (Ψ : Superop A A') (q : Fin m → ℝ)
    (a : Fin m → EuclideanSpace ℂ A) (b : Fin m → EuclideanSpace ℂ B') :
    Matrix ((A' × B') × Fin m) ((A' × B') × Fin m) ℂ :=
  ∑ j, (q j : ℂ) • ((Ψ (pureDensity (a j)) ⊗ₖ pureDensity (b j)) ⊗ₖ Matrix.single j j (1 : ℂ))

end ShorEBAdditivity


