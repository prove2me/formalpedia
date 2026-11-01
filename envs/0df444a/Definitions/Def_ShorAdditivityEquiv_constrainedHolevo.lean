-- Prove2me | Definitions.Def_ShorAdditivityEquiv_constrainedHolevo
-- name    : ShorAdditivityEquiv_constrainedHolevo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:29:50.981975+00:00
-- url     : https://prove2.me/theorems/28d7ff09-d18a-4a43-980b-f50e8be351e1
-- title:
--   Constrained Holevo capacity $\chi_N(\rho)$ (Eq. (3))
-- statement:
--   For a quantum channel $N$ and a density matrix $\rho$ on its input space, the constrained Holevo capacity is "just the Holevo capacity over ensembles whose average input is $\rho$":
--   $$
--   \chi_N(\rho) = \max_{\substack{\{p_i,|\phi_i\rangle\}\\ \sum_i p_i|\phi_i\rangle\langle\phi_i|=\rho}} H\Big(N\big(\textstyle\sum_i p_i|\phi_i\rangle\langle\phi_i|\big)\Big) - \sum_i p_i\,H\big(N(|\phi_i\rangle\langle\phi_i|)\big).
--   $$
--   Through the Matsumoto–Shimono–Winter correspondence it equals $H(N(\rho))-E_F(\sigma)$ for the bipartite state $\sigma$ obtained from $\rho$ by a Stinespring isometry of $N$.
--
--   **Formalization Note** The maximum is the real supremum over all finite pure-state ensembles (unit vectors, weights $\ge0$ summing to one) whose average is exactly $\rho$. For a density matrix $\rho$ the set is nonempty (the spectral decomposition) and bounded, and the supremum is attained. If $\rho$ is not a density matrix the set is empty and the value is the junk value $0$; every statement assumes a density matrix.
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Eq. (3), p. 6 (also Eq. (11), p. 11)

import Mathlib
import Definitions.Def_ShorAdditivityEquiv_holevoValue

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P08

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Eq. (3), p.6: the constrained Holevo capacity
`χ_N(ρ) = max_{p_i, |φ_i⟩ : Σ_i p_i |φ_i⟩⟨φ_i| = ρ} H(N(Σ_i p_i |φ_i⟩⟨φ_i|)) − Σ_i p_i H(N(|φ_i⟩⟨φ_i|))`,
"just the Holevo capacity over ensembles whose average input is ρ".

**Formalization Note.** The maximum is the real supremum `sSup` over all finite pure-state
ensembles (unit vectors, weights `≥ 0` summing to 1) whose average `pureAverage e` is exactly
`ρ`. For a channel `N` and a density matrix `ρ` this set is nonempty (the spectral
decomposition of `ρ`), bounded by `log₂ d_out`, and the supremum is attained, so it is the
paper's maximum. For a `ρ` that is not a density matrix the set is empty and the value is the
junk value `0`; every statement of the mission assumes `ρ` is a density matrix. -/
noncomputable def constrainedHolevo {I O : Type} [Fintype I] [Fintype O] [DecidableEq O]
    (N : Superop I O) (ρ : Matrix I I ℂ) : ℝ :=
  sSup {r | ∃ e : PureEnsemble I, pureAverage e = ρ ∧ r = holevoValue N e}

end ShorAdditivityEquiv


