-- Prove2me | Definitions.Def_WildeQIT_EntManip_coherentInfoBA
-- name    : WildeQIT_EntManip_coherentInfoBA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:18.881372+00:00
-- url     : https://prove2.me/theorems/96d0f78f-4818-4a40-bc8a-cf34ab60c4d4
-- title:
--   Coherent information $I(B\rangle A)_\rho = H(A)_\rho - H(AB)_\rho$
-- statement:
--   Let $\rho_{AB}$ be a density operator on $\mathcal H_A\otimes\mathcal H_B$, with reduced state $\rho_A=\operatorname{Tr}_B\{\rho_{AB}\}$. The **coherent information** from $B$ to $A$ is
--
--   $$
--   I(B\rangle A)_\rho \equiv H(A)_\rho - H(AB)_\rho ,
--   $$
--
--   the coherent information of Definition 11.5.1 with the roles of $A$ and $B$ exchanged, as used in Proposition 19.2.1.
--
--   **Formalization Note** $\operatorname{Tr}_B$ is the published `WildeQIT.partialTraceRight`; entropies in bits.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 11.5.1, p. 332, with A and B exchanged as in Proposition 19.2.1, p. 539

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_QMemory_vonNeumann

namespace WildeQIT.EntManip

/-- **Coherent information `I(B⟩A)`** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Definition 11.5.1, p. 332, with the roles of `A` and `B` exchanged, as used in
Proposition 19.2.1, p. 539): for `ρ_AB`, `I(B⟩A)_ρ ≡ H(A)_ρ − H(AB)_ρ`, where
`ρ_A = Tr_B{ρ_AB}`.

**Formalization Note** `H_A ⊗ H_B` is indexed by `a × b`; `Tr_B` is the published
`WildeQIT.partialTraceRight`. Entropies are in bits. -/
noncomputable def coherentInfoBA {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ) : ℝ :=
  WildeQIT.QMemory.vonNeumann (WildeQIT.partialTraceRight ρ) - WildeQIT.QMemory.vonNeumann ρ

end WildeQIT.EntManip


