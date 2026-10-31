-- Prove2me | Definitions.Def_ObliviousRSP_bobState
-- name    : ObliviousRSP_bobState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:42.031406+00:00
-- url     : https://prove2.me/theorems/98bbd331-c7cd-402d-b404-9c51feff052c
-- title:
--   Bob's unnormalized conditional state $p_m\rho_{\varphi m}$
-- statement:
--   Alice and Bob share $|\Phi_{d'}\rangle$ on $\mathbb C^\sigma\otimes\mathbb C^\sigma$, Alice holding the first half. If Alice measures her half and obtains the outcome with POVM element $E$, Bob's half is left in the unnormalized state
--   $$
--   \operatorname{Tr}_1\!\big[(E\otimes I)\,|\Phi_{d'}\rangle\langle\Phi_{d'}|\big].
--   $$
--   Its trace is the probability $p_m$ of the outcome, and it equals $p_m\rho_{\varphi m}$, where $\rho_{\varphi m}$ is the (normalized) state of Bob's half given message $m$ in the paper's Fig. 2.
--
--   **Formalization Note** $\operatorname{Tr}_1$ is the published partial trace over the left factor (`WildeQIT.partialTraceLeft`). The state is never divided by $p_m$, so it is defined also when $p_m = 0$; this unnormalized form is the paper's own $\mathbf b$ on p.4.
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, p.3, Fig. 2 and "ρ_φm denotes the state of Bob's half of the shared system given the message m"

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_ObliviousRSP_maxEnt

open scoped Kronecker

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, p.3 (Fig. 2: "ρ_φm denotes the state of Bob's half of the shared system given the
message m"), unnormalized. Alice and Bob share `|Φ_{d′}⟩` (`maxEnt σ`, Alice's half first).
If Alice's measurement on her half gives the outcome with POVM element `E`, Bob's half is left
in the unnormalized state
`bobState E = Tr_1[(E ⊗ I) |Φ_{d′}⟩⟨Φ_{d′}|]`,
whose trace is the probability `p_m` of the outcome and which equals `p_m ρ_φm`.

**Formalization Note.** Tr_1 is `WildeQIT.partialTraceLeft` (traces the left, Alice's, factor).
The state is unnormalized (never divided by `p_m`), so it is defined also when `p_m = 0`; this
is the paper's own quantity **b** of p.4. -/
noncomputable def bobState {σ : Type} [Fintype σ] [DecidableEq σ] (E : Matrix σ σ ℂ) :
    Matrix σ σ ℂ :=
  WildeQIT.partialTraceLeft ((E ⊗ₖ (1 : Matrix σ σ ℂ)) * maxEnt σ)

end ObliviousRSP


