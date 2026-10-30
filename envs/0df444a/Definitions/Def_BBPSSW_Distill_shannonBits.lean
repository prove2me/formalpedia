-- Prove2me | Definitions.Def_BBPSSW_Distill_shannonBits
-- name    : BBPSSW_Distill_shannonBits
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:57.02756+00:00
-- url     : https://prove2.me/theorems/13105f59-7507-4497-b920-283334d0a07c
-- title:
--   Shannon entropy in bits
-- statement:
--   For a finite probability vector $q$ on an alphabet $\alpha$,
--
--   $$H(q)=-\sum_{a\in\alpha}q_a\log_2q_a .$$
--
--   **Formalization Note** Zero-probability letters contribute $0$ ($\log_2 0=0$ in Lean).
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 1 ("−Σ_i p_i log2 p_i") and p. 3 ("H(X) is the Shannon entropy of PX")

import Mathlib

namespace BBPSSW.Distill

/-- **Shannon entropy in bits of a finite distribution.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 1 ("the source's Shannon entropy, −Σ_i p_i log2 p_i") and p. 3 ("H(X) is the Shannon
entropy of P_X").

`shannonBits q = −∑ a, q a · log₂ (q a)`.

**Formalization Note.** `Real.logb 2 0 = 0`, so zero-probability letters contribute `0`. -/
noncomputable def shannonBits {α : Type*} [Fintype α] (q : α → ℝ) : ℝ :=
  -∑ a, q a * Real.logb 2 (q a)

end BBPSSW.Distill


