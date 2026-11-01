-- Prove2me | Definitions.Def_DattaDiscord_discord
-- name    : DattaDiscord_discord
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:06.425985+00:00
-- url     : https://prove2.me/theorems/056cc73b-7e61-4ed7-9cb5-775cc6654da4
-- title:
--   Quantum discord $\mathcal D(A:B)=I(A:B)-\mathcal J(A:B)$
-- statement:
--   The **quantum discord** of a bipartite state $\rho_{AB}$, with the measurement made on $B$, is
--
--   $$
--   \mathcal D(A:B)=I(A:B)-\mathcal J(A:B)=H(\rho_B)-H(\rho_{AB})+\min_{\{\Pi_i\}}\tilde H_{\{\Pi_i\}}(A|B),
--   $$
--
--   the minimum over rank-one POVMs on $B$. It is the part of the total correlations that no measurement of $B$ can reveal.
--
--   The paper's Eq. (2) prints the second line as $H(A)-H(A:B)+\min\tilde H$; that line is a slip (it would give the Bell state discord $-1$), and the definition follows the unambiguous first line $\mathcal D=I-\mathcal J$.
--
--   **Formalization Note** `discord ρ = mutualInfo ρ - classicalCorr ρ`; the minimum is the infimum `minCondEntropy`.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, Eq. (2), first line, p.1

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_DattaDiscord_classicalCorr

open scoped ComplexConjugate

namespace DattaDiscord

/-- **Quantum discord** `D(A : B) = I(A : B) − J(A : B)`, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, Eq. (2), first line, p.1,
with the measurement made on `B`.

**Formalization Note** Unfolding, `D(A : B) = H(B) − H(A, B) + min_{Πᵢ} H̃_{Πᵢ}(A|B)`. The
printed second line of Eq. (2), `H(A) − H(A : B) + min H̃`, is a slip; the definition follows the
first line, which is unambiguous. The minimum is the infimum `minCondEntropy`. -/
noncomputable def discord {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  mutualInfo ρ - classicalCorr ρ

end DattaDiscord


