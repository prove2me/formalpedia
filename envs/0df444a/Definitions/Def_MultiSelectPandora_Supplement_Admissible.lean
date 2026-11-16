-- Prove2me | Definitions.Def_MultiSelectPandora_Supplement_Admissible
-- name    : MultiSelectPandora_Supplement_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:30:33.471649+00:00
-- url     : https://prove2.me/theorems/1160f192-196b-468f-bab2-3b9f575104b1
-- title:
--   Admissible state policies
-- statement:
--   A state policy $\pi$ is **admissible from $(U,\alpha)$** if, at every state $(V,\beta)$ reached with positive probability from $(U,\alpha)$, the box that $\pi$ opens or claims closed there belongs to $V$, the set of boxes neither opened nor claimed closed.
--
--   Admissibility is the feasibility condition of the problem $P(U,\alpha)$: only available boxes can be opened or selected unopened. The budget of one closed claim needs no separate condition, since a claim ends the process.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; preprint basis, sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6); §2.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Supplement_Reach

namespace MultiSelectPandora.Supplement

/-- **Admissible from `(U, α)`.** Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection*, manuscript (STOC 2027 submission), §2.1–§2.2, pp.5–6 (PDF pp.6–7): only boxes that are neither opened
nor claimed closed can be opened or claimed closed. At every state reached with positive probability, the box the
policy opens or claims closed lies in the current set of boxes.

**Formalization Note.** The budget of one closed claim is respected automatically, since a claim ends the process. -/
def Admissible (I : Inst) {k : ℕ} (π : StPolicy I k) (U : Finset (Fin I.n)) (α : Fin k → ℝ) : Prop :=
  ∀ V β, Reach I π U α V β → ∀ i : Fin I.n, (π V β = .openBox i ∨ π V β = .claimStop i) → i ∈ V

end MultiSelectPandora.Supplement


