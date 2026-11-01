-- Prove2me | Definitions.Def_WildeQIT_EntManip_coherentInfoAB
-- name    : WildeQIT_EntManip_coherentInfoAB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:29.673204+00:00
-- url     : https://prove2.me/theorems/133232f4-3b89-431c-a1d8-03eadb7a8ef8
-- title:
--   Coherent information $I(A\rangle B)_\rho = H(B)_\rho - H(AB)_\rho$
-- statement:
--   Let $\rho_{AB}$ be a density operator on $\mathcal H_A\otimes\mathcal H_B$, with reduced state $\rho_B=\operatorname{Tr}_A\{\rho_{AB}\}$. The **coherent information** from $A$ to $B$ is
--
--   $$
--   I(A\rangle B)_\rho \equiv H(B)_\rho - H(AB)_\rho .
--   $$
--
--   It is a lower bound on the relative entropy of entanglement (Proposition 19.2.1) and equals the entanglement entropy on pure states.
--
--   **Formalization Note** $\mathcal H_A\otimes\mathcal H_B$ is indexed by `a × b`; $\operatorname{Tr}_A$ is the published `WildeQIT.partialTraceLeft`; entropies in bits.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 11.5.1, (11.55), p. 332

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_QMemory_vonNeumann

namespace WildeQIT.EntManip

/-- **Coherent information `I(A⟩B)`** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Definition 11.5.1, p. 332): for `ρ_AB`, `I(A⟩B)_ρ ≡ H(B)_ρ − H(AB)_ρ` (11.55),
where `ρ_B = Tr_A{ρ_AB}`.

**Formalization Note** `H_A ⊗ H_B` is indexed by `a × b`; `Tr_A` is the published
`WildeQIT.partialTraceLeft`. Entropies are in bits. -/
noncomputable def coherentInfoAB {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ) : ℝ :=
  WildeQIT.QMemory.vonNeumann (WildeQIT.partialTraceLeft ρ) - WildeQIT.QMemory.vonNeumann ρ

end WildeQIT.EntManip


