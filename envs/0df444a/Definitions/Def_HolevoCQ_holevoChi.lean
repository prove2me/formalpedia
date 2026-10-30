-- Prove2me | Definitions.Def_HolevoCQ_holevoChi
-- name    : HolevoCQ_holevoChi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:47.18899+00:00
-- url     : https://prove2.me/theorems/3e2c26dc-1c60-46e8-8df1-e0ac011e960c
-- title:
--   Entropy bound $\Delta H(\pi)=H(\bar S)-\sum_i\pi_iH(S_i)$
-- statement:
--   Let $H(S)=-\mathrm{Tr}\,S\log_2 S$ be the von Neumann entropy (binary logarithm) of a density operator $S$. For signal states $S_i$, $i\in A$, and a distribution $\pi$ on $A$, put $\bar S=\sum_i\pi_iS_i$ and $\bar H(S_{(\cdot)})=\sum_i\pi_iH(S_i)$. The entropy bound (Holevo quantity) is
--
--   $$
--   \Delta H(\pi)=H(\bar S)-\bar H(S_{(\cdot)})=H\Big(\sum_{i\in A}\pi_iS_i\Big)-\sum_{i\in A}\pi_iH(S_i).
--   $$
--
--   Holevo's Theorem identifies the capacity of the channel $i\mapsto S_i$ with $\max_\pi\Delta H(\pi)$. Applied to the word states $S_u$ and a law on $A^n$, the same definition gives the block quantity $\Delta H_n$.
--
--   **Formalization Note** $H$ is `QAlgorithms.vnEntropy` (bits). The body coincides with the platform's `Information100.P27.labelInformation` and `Dependency50.P07.ensembleInformation`; it is restated over an arbitrary finite alphabet because those modules are not available in this workspace.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, §2, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_HolevoCQ_avgState

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, §2, p.2: the entropy bound
`ΔH(π) = H(S̄) − H̄(S(·)) = H(Σ_i π_i S_i) − Σ_i π_i H(S_i)`, with `H(S) = −Tr S log S`.

**Formalization Note.** `H` is `QAlgorithms.vnEntropy`, the von Neumann entropy with the binary
logarithm (the paper uses binary logarithms throughout, p.1). The body is the same as the
platform's `Information100.P27.labelInformation` and `Dependency50.P07.ensembleInformation`
(the latter is the quantity bounded in the Proved reference
`Renew46.P35.cq_identity_and_holevo`); it is restated here over an arbitrary finite alphabet `A`
because those modules are not available in this workspace. Applied to the word states
`wordState S n` and a law on `Fin n → A`, it is the block quantity `ΔH_n`. -/
noncomputable def holevoChi {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) (π : A → ℝ) : ℝ :=
  vnEntropy (avgState S π) - ∑ i, π i * vnEntropy (S i)

end HolevoCQ


