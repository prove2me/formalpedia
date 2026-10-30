-- Prove2me | Definitions.Def_ShorEBAdditivity_holevoChi
-- name    : ShorEBAdditivity_holevoChi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:18:10.900582+00:00
-- url     : https://prove2.me/theorems/b053036c-77ff-45c9-b8ea-922841ac6d99
-- title:
--   Holevo quantity $\chi(\{p_i,\rho_i\})$ of an ensemble through a channel
-- statement:
--   Let $\Psi : M_A \to M_{A'}$ be a map and $\{p_i, \rho_i\}_{i=1}^n$ a finite family of weights and matrices on $\mathcal H_A$. The **Holevo quantity** of the family through $\Psi$ is
--
--   $$
--   \chi(\{p_i,\rho_i\}) = H\Big(\Psi\Big(\sum_i p_i\rho_i\Big)\Big) - \sum_i p_i\, H\big(\Psi(\rho_i)\big),
--   $$
--
--   where $H(\rho) = -\operatorname{Tr}\rho\log\rho$ is the von Neumann entropy.
--
--   It is the objective maximized in the definition (15) of the Holevo–Schumacher–Westmoreland capacity $\chi^*(\Psi)$. For a linear $\Psi$ the first term equals $H(\sum_i \Psi(p_i\rho_i))$, the form written in (2).
--
--   **Formalization Note** $H$ is the published `QAlgorithms.vnEntropy`, computed in bits ($\log_2$) by the continuous functional calculus with $0\log 0 = 0$; the paper leaves the base open. No condition on the weights or the matrices is built in; the ensemble conditions are the separate predicate `IsEnsemble`.
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (2), p.1 and eq. (15), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble

open QAlgorithms

namespace ShorEBAdditivity

/-- Shor, arXiv:quant-ph/0201149v3, eq. (2), p.1 and the objective of eq. (15), p.3: the Holevo
quantity of the ensemble `{p_i, ρ_i}` through the channel `Ψ`,
`χ({p_i, ρ_i}) = H(Ψ(Σ_i p_i ρ_i)) − Σ_i p_i H(Ψ(ρ_i))`,
where `H(ρ) = −Tr ρ log ρ` is the von Neumann entropy.

**Formalization Note.** `H` is `QAlgorithms.vnEntropy`, computed in bits
(`−Re Tr (ρ log₂ ρ)` by the continuous functional calculus, `0 log 0 = 0`); the paper leaves the
base of the logarithm open. The first term is written as in (15), `H(Ψ(Σ p_i ρ_i))`; for a linear
`Ψ` (a channel) it equals (2)'s `H(Σ Ψ(p_i ρ_i))`. No condition on `p`, `ρ` is built in: the
ensemble conditions are `IsEnsemble`. -/
noncomputable def holevoChi {A A' : Type*} [Fintype A'] [DecidableEq A'] {n : ℕ}
    (Ψ : Superop A A') (p : Fin n → ℝ) (ρ : Fin n → Matrix A A ℂ) : ℝ :=
  vnEntropy (Ψ (∑ i, (p i : ℂ) • ρ i)) - ∑ i, p i * vnEntropy (Ψ (ρ i))

end ShorEBAdditivity


