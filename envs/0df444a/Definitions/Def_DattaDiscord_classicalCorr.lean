-- Prove2me | Definitions.Def_DattaDiscord_classicalCorr
-- name    : DattaDiscord_classicalCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:48.279166+00:00
-- url     : https://prove2.me/theorems/243f87c2-d0ce-4157-bdb0-c467ebc78b57
-- title:
--   Classical correlation $\mathcal J(A:B)=H(A)-\tilde H(A|B)$
-- statement:
--   For a bipartite operator $\rho_{AB}$, the **classical correlation** obtained by measuring $B$ is
--
--   $$
--   \mathcal J(A:B)=\max_{\{\Pi_i\}}\big(H(A)-\tilde H_{\{\Pi_i\}}(A|B)\big)=H(A)-\tilde H(A|B),
--   $$
--
--   the largest reduction of the entropy of $A$ achievable by a rank-one measurement of $B$.
--
--   **Formalization Note** It is written through the second form, $H(\rho_A)$ minus `minCondEntropy`, with $\rho_A$ = `QAlgorithms.traceRight ρ`.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, p.1 (before Eq. (2), "J(A : B) = max{Πi}(H(A) − H̃{Πi}(A|B)) ≡ H(A) − H̃(A|B)")

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_DattaDiscord_minCondEntropy

open scoped ComplexConjugate

namespace DattaDiscord

/-- **Classical correlation** `J(A : B) = max_{Πᵢ} (H(A) − H̃_{Πᵢ}(A|B)) ≡ H(A) − H̃(A|B)`,
Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.1 (before Eq. (2)), the optimum over rank-one POVMs on `B`.

**Formalization Note** It is written through its second form `H(A) − H̃(A|B)`, with
`H̃(A|B) = minCondEntropy ρ` (an infimum, see there) and `H(A) = vnEntropy (traceRight ρ)`. -/
noncomputable def classicalCorr {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  QAlgorithms.vnEntropy (QAlgorithms.traceRight ρ) - minCondEntropy ρ

end DattaDiscord


