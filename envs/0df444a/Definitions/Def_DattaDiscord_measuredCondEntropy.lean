-- Prove2me | Definitions.Def_DattaDiscord_measuredCondEntropy
-- name    : DattaDiscord_measuredCondEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:39.982014+00:00
-- url     : https://prove2.me/theorems/3964cf49-c5ad-4bcb-9bd4-c5b176a2e1cb
-- title:
--   Measured conditional entropy $\tilde H_{\{\Pi_i\}}(A|B)=\sum_i p_iH(\rho_{A|i})$
-- statement:
--   For a bipartite operator $\rho_{AB}$ and a measurement $\{\Pi_i\}_{i=0}^{n-1}$ of $B$, the **measured conditional entropy** is
--
--   $$
--   \tilde H_{\{\Pi_i\}}(A|B)=\sum_{i} p_i\,H(\rho_{A|i}),
--   $$
--
--   where $p_i$ and $\rho_{A|i}$ are the outcome probabilities and post-measurement states of Eq. (1), and $H(\sigma)=-\mathrm{Tr}(\sigma\log_2\sigma)$ is the von Neumann entropy in bits. It is the quantum analogue of the classical conditional entropy: the average uncertainty left in $A$ once the outcome on $B$ is known.
--
--   **Formalization Note** $H$ is the published `QAlgorithms.vnEntropy` (base 2, "all logarithms are taken to base 2"). An outcome with $p_i=0$ contributes $0$.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, p.1 (after Eq. (1), "H̃{Πi}(A|B) ≡ Σi piH(ρA|i)")

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_DattaDiscord_condState

open scoped ComplexConjugate

namespace DattaDiscord

/-- **Measured conditional entropy** `H̃_{Πᵢ}(A|B) = ∑ᵢ pᵢ H(ρ_{A|i})`, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.1 (after
Eq. (1)): the average von Neumann entropy of the post-measurement states of `A` when `B` is
measured with the POVM `{Πᵢ}`, weighted by the outcome probabilities.

**Formalization Note** `H` is the published `QAlgorithms.vnEntropy`, in bits ("all logarithms are
taken to base 2", p.1). A term with `pᵢ = 0` is `0 · H(0) = 0`, the convention `pᵢ H(ρ_{A|i}) = 0`
for outcomes of probability zero. -/
noncomputable def measuredCondEntropy {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    {n : ℕ} (ρ : Matrix (A × B) (A × B) ℂ) (M : Fin n → Matrix B B ℂ) : ℝ :=
  ∑ i, outcomeProb ρ (M i) * QAlgorithms.vnEntropy (condState ρ (M i))

end DattaDiscord


