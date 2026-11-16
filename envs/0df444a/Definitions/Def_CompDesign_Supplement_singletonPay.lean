-- Prove2me | Definitions.Def_CompDesign_Supplement_singletonPay
-- name    : CompDesign_Supplement_singletonPay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:50:00.799192+00:00
-- url     : https://prove2.me/theorems/4db97f52-83d9-4d83-b3a6-1649a0fb48c4
-- title:
--   Singleton-prize rule $p^{sing}$ (binary actions, §5.3)
-- statement:
--   Fix a strict public priority order on $N$. For nonempty $S$, let $w(S)$ be the highest-priority element of $\arg\max_{i\in S}v(\{i\})$. The **singleton-prize rule** pays
--   $$p^{sing}_i(S)=\begin{cases}B&\text{if }S\ne\emptyset\text{ and }i=w(S),\\0&\text{otherwise.}\end{cases}$$
--   It is one branch of the randomized rule of Theorem 5.4.
--
--   **Formalization Note** The priority order is a rank `prio : Fin n → ℕ` (smaller first); Theorem 5.4 assumes it injective, and then exactly one agent of a nonempty $S$ is paid.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §5.3, p.32 (PDF 35)

import Mathlib

namespace CompDesign.Supplement

/-- The singleton-prize rule of §5.3, p.32 (PDF 35), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…): for nonempty `S`, `w(S)` is the
element of `argmax_{i∈S} v({i})` of highest priority, and `p^sing_i(S) = B` if `S ≠ ∅` and
`i = w(S)`, else `0`.

**Formalization Note.** The fixed public priority order is a rank `prio : Fin n → ℕ`, smaller first;
the theorems assume it injective, so the condition below holds for exactly one `i ∈ S` when `S` is
nonempty. -/
noncomputable def singletonPay {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (prio : Fin n → ℕ)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ S ∧ ∀ j ∈ S, v {j} < v {i} ∨ (v {j} = v {i} ∧ prio i ≤ prio j) then B else 0

end CompDesign.Supplement


