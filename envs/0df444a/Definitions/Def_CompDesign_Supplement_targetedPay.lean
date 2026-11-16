-- Prove2me | Definitions.Def_CompDesign_Supplement_targetedPay
-- name    : CompDesign_Supplement_targetedPay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:52:37.29896+00:00
-- url     : https://prove2.me/theorems/90e1d5b9-4576-43eb-80cc-16b2a15c9be1
-- title:
--   Targeted-implementation payment rule (58)
-- statement:
--   For a target set $T\subseteq N$ and bonuses $b_i$, the **targeted-implementation rule** pays
--   $$p_i(S)=\begin{cases}c_i+b_i&\text{if }i\in S\cap T,\\0&\text{otherwise.}\end{cases}$$
--   It reads the costs, so it is not cost oblivious; it is the rule of Theorem C.1.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), App. C, (58), p.71 (PDF 74)

import Mathlib

namespace CompDesign.Supplement

/-- The targeted-implementation payment rule (58) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…), App. C, p.71 (PDF 74): for a target
`T ⊆ N` and bonuses `b_i`, `p_i(S) = c_i + b_i` if `i ∈ S ∩ T`, and `0` otherwise. The rule reads
the costs (it is not cost oblivious). -/
def targetedPay {n : ℕ} (T : Finset (Fin n)) (c b : Fin n → ℝ) (S : Finset (Fin n))
    (i : Fin n) : ℝ :=
  if i ∈ S ∧ i ∈ T then c i + b i else 0

end CompDesign.Supplement


