-- Prove2me | Definitions.Def_WildeQIT_Degradable_coherentInfoState
-- name    : WildeQIT_Degradable_coherentInfoState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:45.35889+00:00
-- url     : https://prove2.me/theorems/2b590ebe-9cf0-4422-96fa-786f1b871ba9
-- title:
--   Coherent information $I(A\rangle B)_\rho = H(B)_\rho - H(AB)_\rho$ of a bipartite state
-- statement:
--   For a bipartite state $\rho_{AB}$ with marginal $\rho_B=\mathrm{Tr}_A\rho_{AB}$, the **coherent information** is
--
--   $$
--   I(A\rangle B)_\rho \equiv H(B)_\rho - H(AB)_\rho ,
--   $$
--
--   where $H$ is the von Neumann entropy. It is the quantity whose maximum over channel inputs defines the coherent information of a channel (Definition 13.5.1).
--
--   **Formalization Note** $\rho_B$ is the published `WildeQIT.partialTraceLeft ρ` and $H$ is `QAlgorithms.vnEntropy` (bits). The definition is total on matrices and is applied to density operators.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 11.5.1, eq. (11.55), p. 332, as used in (13.147), p. 411

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_partialTrace

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 11.5.1 (Coherent Information), p. 332, eq. (11.55), as used on p. 411.
-/

namespace WildeQIT.Degradable

/-- **Coherent information of a bipartite state** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 11.5.1, p. 332, eq. (11.55), and p. 411):
`I(A⟩B)_ρ = H(B)_ρ − H(AB)_ρ`.

**Formalization Note.** The bipartite system is `A × B` (Kronecker convention), `ρ_B = Tr_A ρ`
is `WildeQIT.partialTraceLeft ρ`, and `H` is the published von Neumann entropy
`QAlgorithms.vnEntropy` (bits). Total on matrices; used on density operators. -/
noncomputable def coherentInfoState {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  QAlgorithms.vnEntropy (WildeQIT.partialTraceLeft ρ) - QAlgorithms.vnEntropy ρ

end WildeQIT.Degradable


