-- Prove2me | Definitions.Def_WildeQIT_QMemory_coherentInfo
-- name    : WildeQIT_QMemory_coherentInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:05.374031+00:00
-- url     : https://prove2.me/theorems/76d5a6d7-8eff-4765-b99d-8a77c16fff86
-- title:
--   Coherent information $I(A\rangle B)_\rho=H(B)_\rho-H(AB)_\rho$
-- statement:
--   For a bipartite state $\rho_{AB}$ with marginal $\rho_B=\mathrm{Tr}_A\{\rho_{AB}\}$, the **coherent information** is
--
--   $$
--   I(A\rangle B)_\rho\equiv H(B)_\rho-H(AB)_\rho ,
--   $$
--
--   the negative of the conditional quantum entropy $H(A|B)_\rho$. It measures quantum correlations and obeys a quantum data-processing inequality.
--
--   **Formalization Note** $\mathcal H_A\otimes\mathcal H_B$ is indexed by `a × b`; $\mathrm{Tr}_A$ is the published `WildeQIT.partialTraceLeft`; entropies in bits.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 11.5.1, eq. (11.55), p. 332

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_QMemory_vonNeumann

namespace WildeQIT.QMemory

/-- **Coherent information** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Definition 11.5.1, p. 332): for `ρ_AB`,
`I(A⟩B)_ρ ≡ H(B)_ρ − H(AB)_ρ` (11.55), where `ρ_B = Tr_A{ρ_AB}`.

**Formalization Note** `H_A ⊗ H_B` is indexed by `a × b`; `Tr_A` is the published
`WildeQIT.partialTraceLeft`. Entropies are in bits. -/
noncomputable def coherentInfo {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ) : ℝ :=
  vonNeumann (WildeQIT.partialTraceLeft ρ) - vonNeumann ρ

end WildeQIT.QMemory


