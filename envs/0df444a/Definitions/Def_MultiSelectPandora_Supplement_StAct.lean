-- Prove2me | Definitions.Def_MultiSelectPandora_Supplement_StAct
-- name    : MultiSelectPandora_Supplement_StAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:28:12.750931+00:00
-- url     : https://prove2.me/theorems/57789f48-7064-4c9d-81bb-a49be341c114
-- title:
--   Actions with one closed claim: open a box, stop, or stop with a box claimed closed
-- statement:
--   With at most one closed claim ($\hat k=1$), an **action** of the searcher at a state is one of:
--
--   1. **open** box $i$: pay $c_i$ and observe $v_i$;
--   2. **stop** and select the $k$ secured values $\alpha_1,\dots,\alpha_k$;
--   3. **stop with box $i$ claimed closed**: select box $i$ unopened, which contributes $\mathbb E[v_i]$, together with $\alpha_1,\dots,\alpha_{k-1}$.
--
--   The helper $\mathrm{ofRule}$ turns the output of a box-selection rule into an action: open the box it names, or stop when it names none.
--
--   These are the actions of the selection model of §2.1, where the searcher claims boxes closed when it stops; they are the moves of the policies in Theorem 4.10.
--
--   **Formalization Note** The closed claim is part of the stopping action. In the representation of §2.2 a claim is a separate action leading to $(U\setminus\{i\},\mathrm{top}_k(\alpha\cup\{\mathbb E[v_i]\}),\hat k-1)$, under which a claim of a box with $\mathbb E[v_i]<\alpha_k$ is a free no-op; here a claimed box is always selected, as in Appendix B.2 ("a box claimed closed is one of the selected boxes"). Both give the same optimal value.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; preprint basis, sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6); §2.2, p.6 (PDF p.7); §4.2, p.22 (PDF p.23); App. B.2, p.37 (PDF p.38)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst

namespace MultiSelectPandora.Supplement

/-- **An action at a state of the problem with one closed claim.** Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection*, manuscript (STOC 2027 submission), §2.1, p.5 (PDF p.6):
"A policy π specifies the next action, which is to open a box or to stop and select". With at most one closed claim
(`k̂ = 1`, §4.2, p.22, PDF p.23) the action is: open box `i`, stop and select the `k` best observed values, or stop
and select box `i` claimed closed (unopened) together with the `k − 1` best observed values.

**Formalization Note.** The closed claim is part of the stopping action, as in the selection model of §2.1, where
the searcher claims boxes closed "when it stops". §2.2 (p.6, PDF p.7) treats a closed claim as a separate action before
stopping that leads to `(U \ {i}, top_k(α ∪ {E[v_i]}), k̂ − 1)`; with that representation a claim of a box whose mean is
below `α_k` is a free no-op, so "some optimal policy claims a box closed with positive probability" (Definition 4.2)
would hold at every large outside option, against App. B.2 (p.37, PDF p.38: "a box claimed closed is one of the selected
boxes"). Here a claimed box is always selected. -/
inductive StAct (I : Inst) where
  /-- open box `i` (pay `c_i`, observe `v_i`) -/
  | openBox : Fin I.n → StAct I
  /-- stop and select the `k` observed values `α` -/
  | stop : StAct I
  /-- stop and select box `i` claimed closed together with `α_1, …, α_{k−1}` -/
  | claimStop : Fin I.n → StAct I

/-- The action the generalized Weitzman rule names: open the box it returns, or stop on `none`. -/
def StAct.ofRule {I : Inst} : Option (Fin I.n) → StAct I
  | some i => .openBox i
  | none => .stop

end MultiSelectPandora.Supplement


