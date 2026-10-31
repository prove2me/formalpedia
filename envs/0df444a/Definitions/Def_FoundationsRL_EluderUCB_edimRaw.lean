-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_edimRaw
-- name    : FoundationsRL_EluderUCB_edimRaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:28.459222+00:00
-- url     : https://prove2.me/theorems/d4cb678e-1aef-472f-ba98-554288601005
-- title:
--   Definition 6: the underlined $\underline{\mathrm{Edim}}_{f^\star}(\mathcal F,\varepsilon)$
-- statement:
--   For a class $\mathcal F\subset(\Pi\to\mathbb R)$, a function $f^\star:\Pi\to\mathbb R$ and a scale $\varepsilon$, the quantity $\underline{\mathrm{Edim}}_{f^\star}(\mathcal F,\varepsilon)$ is the length of the longest sequence of decisions $\pi^1,\dots,\pi^d$ satisfying (4.9).
--
--   It counts how many times, in the worst case, a new decision can surprise a learner. Its monotone version is the eluder dimension.
--
--   **Formalization Note** The value is a supremum in $\mathbb N\cup\{\infty\}$, and it is $\infty$ when arbitrarily long sequences exist. The empty sequence always qualifies.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Definition 6, p. 59

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_IsElusiveSeq

namespace FoundationsRL.EluderUCB

/-- **The underlined quantity of Definition 6.** Foster & Rakhlin, arXiv:2312.16730v1, Definition 6,
p. 59: the length of the longest sequence of decisions satisfying (4.9), written with an underline
in the source (the underline is lost in text extraction).

**Formalization Note.** The value lies in `ℕ∞`: it is the supremum of the lengths `d` of sequences
satisfying (4.9), and it is `⊤` when arbitrarily long ones exist. The empty sequence always
qualifies, so the supremum is taken over a nonempty set and is `0` exactly when no sequence of
length one satisfies (4.9). -/
noncomputable def edimRaw {Act : Type*} (F : Set (Act → ℝ)) (fstar : Act → ℝ) (ε : ℝ) : ℕ∞ :=
  ⨆ (d : ℕ) (π : Fin d → Act) (_ : IsElusiveSeq F fstar ε π), (d : ℕ∞)

end FoundationsRL.EluderUCB


