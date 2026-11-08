-- Prove2me | Definitions.Def_SingleInteraction_xyInteraction
-- name    : SingleInteraction_xyInteraction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:18.770878+00:00
-- url     : https://prove2.me/theorems/16fb8b79-16fc-4f88-b4ef-f5332295edac
-- title:
--   The XY interaction $X\otimes X+Y\otimes Y$
-- statement:
--   The two-qubit XY interaction $X\otimes X+Y\otimes Y$; applied to qubits $u,v$ it is $K_{uv}=X_uX_v+Y_uY_v$. It is the interaction of the positive-weight XY problem that Theorem 60 reduces from (Theorem 25 with $\alpha=\beta=1$, $\gamma=0$; Lemma 61).
--
--   **Formalization Note** Symmetric under exchange of the two qubits. Pauli matrices as in the published `MIPRE.LCS.Pauli`.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.3.5, p.26 (Theorem 25 and the consequence below it); §5.1.1, p.55 ($K_{uv}$)

import Mathlib
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_SingleInteraction_twoQubit

namespace SingleInteraction

/-- The two-qubit XY interaction `X ⊗ X + Y ⊗ Y` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.3.5, p.26, Theorem 25 with
`α = β = 1`, `γ = 0`; `K_{uv} = X_uX_v + Y_uY_v`, §5.1.1, p.55).

**Formalization Note** The Pauli matrices are the published `MIPRE.LCS.Pauli.X`, `Y`. -/
def xyInteraction : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  twoQubit MIPRE.LCS.Pauli.X MIPRE.LCS.Pauli.X + twoQubit MIPRE.LCS.Pauli.Y MIPRE.LCS.Pauli.Y

end SingleInteraction


