-- Prove2me | Definitions.Def_MultiSelectPandora_Supplement_tau
-- name    : MultiSelectPandora_Supplement_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:33:29.20094+00:00
-- url     : https://prove2.me/theorems/9aea655d-9109-4ecf-aadb-95912746ed9a
-- title:
--   The phase threshold $\tau_1(U,\alpha[1:k-1])$
-- statement:
--   Let $\hat k=1$, let $U$ be a set of boxes and $\alpha[1:k-1]$ a prefix, and let $\alpha_0:=+\infty$. The **phase threshold** is
--   $$\tau_1(U,\alpha[1:k-1])=\sup\Big\{x\in[0,\alpha_{k-1}]\;:\;\text{some optimal policy of }P\big(U,(\alpha[1:k-1],x)\big)\text{ claims a box closed with positive probability}\Big\},$$
--   with $\tau_1=-\infty$ when the set is empty. For $k=1$ the range of $x$ is $[0,\infty)$.
--
--   It is the largest value of the competing entry $\alpha_k$ at which some optimal policy still uses its closed claim; Theorem 4.10 switches between its two phases at this threshold.
--
--   **Formalization Note** The value is a supremum in the extended reals $\overline{\mathbb R}$, with the empty supremum $-\infty$, as on the page. Appendix B.2 shows the defining set is closed and bounded, so the supremum is the page's "largest value". Only the prefix $\alpha_1,\dots,\alpha_{k-1}$ of the argument $\alpha$ is used.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; preprint basis, sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 4.2, p.18 (PDF p.19); existence of the threshold, App. B.2, p.37 (PDF p.38)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Supplement_IsOptimal
import Definitions.Def_MultiSelectPandora_Supplement_ClaimsClosed
import Definitions.Def_MultiSelectPandora_Supplement_setLast

namespace MultiSelectPandora.Supplement

/-- **The phase threshold `τ_1(U, α[1 : k−1])`.** Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection*, manuscript (STOC 2027 submission), Definition 4.2, p.18 (PDF p.19), with `k̂ = 1`:
"Fix a prefix α[1 : k − k̂], and let x range over [0, α_{k−k̂}], where α_{k−k̂} := +∞ if k̂ = k. The phase threshold
τ_k̂(U, α[1 : k − k̂]) is the largest value x for which some optimal policy of P(U, (α[1 : k − k̂], x, 0, …, 0), k̂) claims
k̂ boxes closed with positive probability, and −∞ if there is no such x."

**Formalization Note.** With `k̂ = 1` the state is `(α[1 : k−1], x)` (`setLast α x`) and `x` ranges over `[0, α_{k−1}]`,
or over `[0, ∞)` when `k = 1` (the condition `j + 2 = k → x ≤ α j` is empty then). The value is the supremum in
`EReal` of the set of such `x`: `⊥ = −∞` when the set is empty, as on the page. App. B.2 (p.37, PDF p.38) shows the
set is closed and bounded, so the supremum is the page's "largest value". Only the prefix `α[1 : k−1]` of the argument
`α` is used. -/
noncomputable def tau (I : Inst) {k : ℕ} (U : Finset (Fin I.n)) (α : Fin k → ℝ) : EReal :=
  sSup {e : EReal | ∃ x : ℝ, e = (x : EReal) ∧ 0 ≤ x ∧ (∀ j : Fin k, j.val + 2 = k → x ≤ α j) ∧
    ∃ π : StPolicy I k, IsOptimal I π U (setLast α x) ∧ ClaimsClosed I π U (setLast α x)}

end MultiSelectPandora.Supplement


