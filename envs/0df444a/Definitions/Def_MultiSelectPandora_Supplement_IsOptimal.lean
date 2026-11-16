-- Prove2me | Definitions.Def_MultiSelectPandora_Supplement_IsOptimal
-- name    : MultiSelectPandora_Supplement_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:31:22.781926+00:00
-- url     : https://prove2.me/theorems/b9c8ad23-a0dc-4fa3-8ba5-35eca2504122
-- title:
--   Optimal policies of $P(U,\alpha)$ with one closed claim
-- statement:
--   A state policy $\pi$ is **optimal for $P(U,\alpha)$** (with $\hat k=1$) if it is admissible from $(U,\alpha)$ and
--   $$u_{\pi'}(U,\alpha)\le u_\pi(U,\alpha)\qquad\text{for every state policy }\pi'\text{ admissible from }(U,\alpha).$$
--
--   This is the notion of optimal policy in Definition 4.2 and Theorem 4.10; "an optimal policy for $P(M,0)$" is the case $U=M$, $\alpha=0$.
--
--   **Formalization Note** Exact optimality, not $\varepsilon$-optimality. The comparison class is all admissible state policies, which attain the optimum over history-dependent policies because $(U,\alpha)$ is a sufficient statistic (§2.2).
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; preprint basis, sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.2, p.6 (PDF p.7); Definition 4.2, p.18 (PDF p.19); Theorem 4.10, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Supplement_Admissible
import Definitions.Def_MultiSelectPandora_Supplement_stValue

namespace MultiSelectPandora.Supplement

/-- **An optimal policy of `P(U, α)` with one closed claim.** Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection*, manuscript (STOC 2027 submission), §2.1–§2.2, pp.5–6 (PDF pp.6–7), with
`k̂ = 1` (§4.2, p.22, PDF p.23): an admissible policy whose expected utility from `(U, α)` is at least that of every
admissible policy.

**Formalization Note.** Exact optimality, not `ε`-optimality; the comparison class is all admissible state policies,
which attain the optimum over history-dependent policies (§2.2). -/
def IsOptimal (I : Inst) {k : ℕ} (π : StPolicy I k) (U : Finset (Fin I.n)) (α : Fin k → ℝ) : Prop :=
  Admissible I π U α ∧ ∀ π' : StPolicy I k, Admissible I π' U α → stValue I π' U α ≤ stValue I π U α

end MultiSelectPandora.Supplement


