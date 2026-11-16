-- Prove2me | Definitions.Def_MultiSelectPandora_Supplement_Reach
-- name    : MultiSelectPandora_Supplement_Reach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:29:38.546728+00:00
-- url     : https://prove2.me/theorems/f1759778-5b5f-4611-8442-73c4c69e3c7c
-- title:
--   States reached with positive probability
-- statement:
--   Fix a state policy $\pi$ and a start state $(U,\alpha)$. The states **reached with positive probability** are the smallest set that
--
--   1. contains $(U,\alpha)$, and
--   2. whenever it contains $(V,\beta)$ and $\pi$ opens a box $i\in V$ there, contains $(V\setminus\{i\},\mathrm{top}_k(\beta\cup\{v\}))$ for every value $v$ with $\Pr[v_i=v]>0$.
--
--   Stopping, with or without a closed claim, ends the process. This is the meaning of "a state that the policy reaches with positive probability" in Definition 4.2, Observation 4.1 and Theorem 4.10.
--
--   **Formalization Note** Values of positive probability are the support positions with positive probability in the explicit finite law of each box.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; preprint basis, sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.2, p.6 (PDF p.7); Definition 4.2, p.18 (PDF p.19); Theorem 4.10, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_insertTop
import Definitions.Def_MultiSelectPandora_Supplement_StPolicy

namespace MultiSelectPandora.Supplement

/-- **States reached with positive probability from `(U, α)` under a state policy.** Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection*, manuscript (STOC 2027 submission), §2.2, p.6
(PDF p.7), and Definition 4.2, p.18 (PDF p.19) ("with positive probability"): the start state, and from a reached
state `(V, β)` at which the policy opens a box `i ∈ V`, every `(V \ {i}, top_k(β ∪ {v}))` for a value `v` of positive
probability.

**Formalization Note.** Support positions `j` with `prob i j > 0` stand for values of positive probability. A stop or a
closed claim ends the process, so it leads to no further state. -/
inductive Reach (I : Inst) {k : ℕ} (π : StPolicy I k) (U : Finset (Fin I.n)) (α : Fin k → ℝ) :
    Finset (Fin I.n) → (Fin k → ℝ) → Prop
  /-- the start state -/
  | start : Reach I π U α U α
  /-- opening a box of the current set and observing a value of positive probability -/
  | step {V : Finset (Fin I.n)} {β : Fin k → ℝ} {i : Fin I.n} (j : Fin (I.s i)) :
      Reach I π U α V β → π V β = .openBox i → i ∈ V → 0 < I.prob i j →
      Reach I π U α (V.erase i) (insertTop β (I.val i j))

end MultiSelectPandora.Supplement


