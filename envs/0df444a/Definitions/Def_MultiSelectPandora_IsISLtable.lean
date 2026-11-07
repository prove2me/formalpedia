-- Prove2me | Definitions.Def_MultiSelectPandora_IsISLtable
-- name    : MultiSelectPandora_IsISLtable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:19.528072+00:00
-- url     : https://prove2.me/theorems/cc74f470-86be-4af0-8dd4-5b5b17a34e0c
-- title:
--   $I^{SL}$ written as a table
-- statement:
--   A table $S$ is $I^{SL}$ written as a table when there is a list of all states of $I^{SL}$, each once, numbered so that the numbering extends the componentwise order ("any total order that extends the componentwise order"), such that: $T=n$; the initial state is $0$; $h\equiv0$; the actions are $2i$ (open box $i$), $2i+1$ (claim box $i$) and $2n$ (*end*); the two actions of a box form a group; the entries of the table are the rewards and transitions of $I^{SL}$ at each state; and outcomes of an opening are listed by support position.
--
--   **Formalization Note** This is a relation, so it covers every admissible numbering, and it does not build the table. Claim A.3 says that a machine computes such a table.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.23, p.15 (PDF p.16); p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawInst
import Definitions.Def_MultiSelectPandora_RawInst_toInst
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_outcomes
import Definitions.Def_MultiSelectPandora_IsSortedState
import Definitions.Def_MultiSelectPandora_Levels
import Definitions.Def_MultiSelectPandora_ISL
import Definitions.Def_MultiSelectPandora_DPData_openGain
import Definitions.Def_MultiSelectPandora_DPData_claimGain
import Definitions.Def_MultiSelectPandora_insertTop

namespace MultiSelectPandora

/-- **`S` is `I^SL` written as a table.** Beyhaghi–Han–Luqman manuscript, Definition 3.23, p.15 (PDF p.16), with p.8 (PDF p.9): "numbering them according
to any total order that extends the componentwise order puts them in this form".

**Formalization Note.** A relation, not a function: `st` lists the states of `I^SL`, each once, in a numbering that extends the componentwise order, and any
such numbering is allowed. The actions are numbered `2 i` (open box `i`), `2 i + 1` (claim box `i`), `2 n` (`end`), the two actions of a box form a group, `T = n`,
`h ≡ 0`. The entries are rational casts of the real objects of `I^SL`, and open outcomes are listed by support position. -/
def IsISLtable (ε : ℚ) (k : ℕ) (I : RawInst) (S : RawSSDP) : Prop :=
  ∃ st : List (Fin k → ℝ), st.Nodup ∧
    (∀ α, α ∈ st ↔ IsSortedState α ∧ ∀ j, α j ∈ Levels I.toInst k ε) ∧
    (∀ (a b : ℕ) (ha : a < st.length) (hb : b < st.length), (∀ j, st[a] j ≤ st[b] j) → a ≤ b) ∧
    S.L = st.length ∧ S.T = I.toInst.n ∧ st[S.init]? = some 0 ∧
    S.h = List.replicate S.L 0 ∧ S.actions.length = 2 * I.toInst.n + 1 ∧
    (∀ act ∈ S.actions, act.2.length = S.L) ∧
    (S.actions.getD (2 * I.toInst.n) (none, [])).1 = none ∧
    (∀ i : Fin I.toInst.n,
      (S.actions.getD (2 * i.val) (none, [])).1 = some i.val ∧
      (S.actions.getD (2 * i.val + 1) (none, [])).1 = some i.val) ∧
    ∀ (a : ℕ) (ha : a < st.length),
      S.outcomes (2 * I.toInst.n) a = [(1, 0, a)] ∧
      ∀ i : Fin I.toInst.n,
        (S.outcomes (2 * i.val) a).length = I.toInst.s i ∧
        (∀ j : Fin (I.toInst.s i), ∃ (p r : ℚ) (nx : ℕ) (hnx : nx < st.length),
          (S.outcomes (2 * i.val) a)[j.val]? = some (p, r, nx) ∧
          (p : ℝ) = I.toInst.prob i j ∧
          (r : ℝ) = (ISL I.toInst k ε).openGain st[a] i j ∧
          st[nx] = insertTop st[a] ((ISL I.toInst k ε).x i j)) ∧
        ∃ (r : ℚ) (nx : ℕ) (hnx : nx < st.length),
          S.outcomes (2 * i.val + 1) a = [(1, r, nx)] ∧
          (r : ℝ) = (ISL I.toInst k ε).claimGain st[a] i ∧
          st[nx] = insertTop st[a] ((ISL I.toInst k ε).b i)

end MultiSelectPandora


