-- Prove2me | Definitions.Def_FeedbackSwitching_minimaxRegret
-- name    : FeedbackSwitching_minimaxRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:03.487303+00:00
-- url     : https://prove2.me/theorems/e8fce870-dd3e-4b49-8236-38ebfabfb196
-- title:
--   Minimax regret with switching costs $\mathrm{Reg}^\star_T(G)$
-- statement:
--   For a known feedback graph $G$ and a known horizon $T$, the **minimax regret** is
--   $$
--   \mathrm{Reg}^\star_T(G)=\inf_{\text{learners}}\ \sup_{\ell_1,\dots,\ell_T\in[0,1]^K}\ \mathrm{Reg}_T ,
--   $$
--   the infimum over learners of the supremum over oblivious loss sequences of the regret with switching costs of Eq. (12).
--
--   **Formalization Note** The infimum is over `Learner K` (randomized, seeing only revealed losses, jointly measurable in history and coins); the supremum over all of $[0,1]^{T\times K}$. Both index types are nonempty and every regret lies in $[-T,2T]$, so the real infimum and supremum are genuine (proved in the mission's sanity file).
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), §3.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_FeedbackSwitching_regret

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

**Minimax regret** `Reg⋆_T(G)` (p.13 = PDF p.15): "the infimum over learners of the supremum
over loss sequences of `Reg_T`", for the known horizon `T` and the known graph `G`.

**Formalization Note.** The infimum ranges over `Learner K` (randomized learners that see only the
revealed losses and are jointly measurable in history and coins), the supremum over all loss
sequences in `[0,1]^{T×K}`. Both index types are nonempty (a constant learner; the zero
sequence), and every regret lies in `[−T, 2T]`, so the real `⨅`/`⨆` are a genuine infimum and
supremum (proved in `Solutions/verification/FeedbackSwitching_sanity.lean`). -/
noncomputable def minimaxRegret {K : ℕ} (G : FeedbackGraph K) (T : ℕ) : ℝ :=
  ⨅ L : Learner K, ⨆ ℓ : LossSeq K T, regret G L.toPolicy ℓ.1

end FeedbackSwitching


