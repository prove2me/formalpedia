-- Prove2me | Definitions.Def_LockingAccInfo_outcomeEntropy
-- name    : LockingAccInfo_outcomeEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:15.669621+00:00
-- url     : https://prove2.me/theorems/1cbb4e78-e56c-473c-ac9e-07fe5ed2a093
-- title:
--   Outcome entropy $H(\mathcal N[\sigma])$ of a measurement applied to a state
-- statement:
--   For a finite family of operators $\mathcal N=\{N_v\}_{v\in V}$ on a finite-dimensional system and an operator $\sigma$, the **outcome entropy** is the Shannon entropy (in bits) of the distribution $v\mapsto\operatorname{tr}(N_v\sigma)$:
--
--   $$
--   H(\mathcal N[\sigma]) := -\sum_{v\in V}\operatorname{tr}(N_v\sigma)\log_2\operatorname{tr}(N_v\sigma),
--   $$
--
--   with $0\log0=0$. When $\mathcal N$ is a POVM and $\sigma$ a state this is the entropy of the outcome of measuring $\sigma$ with $\mathcal N$.
--
--   **Formalization Note** The probability of outcome $v$ is the published `effectProb (N v) σ` $=\operatorname{Re}\operatorname{tr}(N_v\sigma)$ and the entropy is the published `shannon`.
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §III, p.3 (H(𝒩[σ])) and Lemma 5, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

open QAlgorithms (effectProb)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, §III, p.3 and Lemma 5, p.4:
"H(N[σ]) is the entropy of the outcome when the measurement N is applied to σ": the Shannon
entropy (in bits) of the outcome distribution `v ↦ tr(N_v σ)`.

**Formalization Note.** `N` is any finite family of operators; the outcome probability of `v` is
the published `effectProb (N v) σ = Re tr(N_v σ)`, and `shannon` is the published Shannon entropy
in bits with `0 log 0 = 0`. Base 2 is forced by the paper's `1 + H(Y) = H(XY)` (p.3). -/
noncomputable def outcomeEntropy {V Q : Type} [Fintype V] [Fintype Q] (N : V → Matrix Q Q ℂ)
    (σ : Matrix Q Q ℂ) : ℝ :=
  shannon (fun v => effectProb (N v) σ)

end LockingAccInfo


