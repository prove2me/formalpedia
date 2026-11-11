-- Prove2me | Definitions.Def_PermInvCC_Dscore
-- name    : PermInvCC_Dscore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:25:45.402355+00:00
-- url     : https://prove2.me/theorems/8a9d27a3-b841-4ef8-9118-1126d5956f53
-- title:
--   Decoding score $D(U)=\max_{E}H(J^E_U,\hat J^E)$
-- statement:
--   Given estimates $\hat J^E$, one distribution for each event $E\in\mathcal E$, the **score** of a table $U$ is
--   $$D(U):=\max_{E\in\mathcal E}H\bigl(J^E_U,\hat J^E\bigr).$$
--   The decoder of Lemma 3.6 outputs the label of a promised type minimizing this score.
--
--   **Formalization Note** The maximum is a supremum over the finite nonempty family $\mathcal E$.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 3.6, p.12

import Mathlib
import Definitions.Def_PermInvCC_cutEvents
import Definitions.Def_PermInvCC_hell
import Definitions.Def_PermInvCC_J

namespace PermInvCC

/-- The **decoding score** `D(U) = max_{E∈𝓔} H(J^E_U, Ĵ^E)` of a table `U` against estimates
`Ĵ^E`, one for each event (Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256 fe1797dd…,
Lemma 3.6, p.12).

**Formalization Note.** `Jhat E` is a distribution on `{⊥} ∪ ([0, ∞) × E)`; only its values on
`E ∈ 𝓔` are read. The supremum is over the finite set `𝓔`, nonempty for `q ≥ 1`, so it is the
maximum. -/
noncomputable def Dscore {q : ℕ} (Jhat : (E : Finset (Fin q × Fin q)) → DensDist E)
    (U : Fin q → Fin q → ℕ) : ℝ :=
  ⨆ E : cutEvents q, hell (JE E.1 U) (Jhat E.1)

end PermInvCC


