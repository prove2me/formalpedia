-- Prove2me | Definitions.Def_ShorEBAdditivity_holevoCapacity
-- name    : ShorEBAdditivity_holevoCapacity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:18:56.838699+00:00
-- url     : https://prove2.me/theorems/d426a46f-90bb-413b-aadc-3ab236b4b33f
-- title:
--   Holevo–Schumacher–Westmoreland capacity $\chi^*(\Psi)$
-- statement:
--   Let $\Psi : M_A \to M_{A'}$ be a map between operators on finite-dimensional spaces. Its **Holevo–Schumacher–Westmoreland capacity** is
--
--   $$
--   \chi^*(\Psi) = \max_{p_i,\rho_i}\; H\Big(\Psi\Big(\sum_i p_i\rho_i\Big)\Big) - \sum_i p_i\, H\big(\Psi(\rho_i)\big),
--   $$
--
--   the maximum running over all finite probability distributions $p_i$ and density matrices $\rho_i$ on $\mathcal H_A$, with $H$ the von Neumann entropy.
--
--   This is the classical capacity of the channel $\Psi$ when the sender is not allowed to entangle inputs across channel uses. For a product channel $\Psi\otimes\Phi$ the maximization runs over all density matrices on $\mathcal H_A\otimes\mathcal H_B$, entangled ones included.
--
--   **Formalization Note** The maximum is a supremum in the extended reals `EReal` over ensembles (`IsEnsemble`) of every finite size and of mixed states. The paper notes that the maximum is attained, so the value is the same. For an empty index type there is no density matrix and the supremum is $-\infty$ ($\bot$). Entropy is in bits.
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (1), p.1 and eq. (15), p.3

import Mathlib
import Definitions.Def_ShorEBAdditivity_IsEnsemble
import Definitions.Def_ShorEBAdditivity_holevoChi

open QAlgorithms

namespace ShorEBAdditivity

/-- Shor, arXiv:quant-ph/0201149v3, eq. (1), p.1 and eq. (15), p.3: the
Holevo–Schumacher–Westmoreland capacity
`χ*(Ψ) = max_{p_i, ρ_i} H(Ψ(Σ_i p_i ρ_i)) − Σ_i p_i H(Ψ(ρ_i))`
"over probability distributions pi and density matrices ρi" on the input space of `Ψ`.

**Formalization Note.** The maximum is taken as a supremum in `EReal` over all finite ensembles
(`IsEnsemble`) of every size `n` and of mixed states. The paper notes (p.1) that the maximum is
attained, so the supremum has the same value; `EReal` avoids the junk value of a real `sSup`.
For an empty input type there is no density matrix, so the supremum is `⊥`. Entropy is in bits
(`QAlgorithms.vnEntropy`). For a tensor channel `Ψ ⊗ Φ` on `A × B` the ensembles range over all
density matrices on `A × B`, entangled ones included. -/
noncomputable def holevoCapacity {A A' : Type*} [Fintype A] [Fintype A'] [DecidableEq A']
    (Ψ : Superop A A') : EReal :=
  ⨆ (n : ℕ) (p : Fin n → ℝ) (ρ : Fin n → Matrix A A ℂ) (_ : IsEnsemble p ρ),
    ((holevoChi Ψ p ρ : ℝ) : EReal)

end ShorEBAdditivity


