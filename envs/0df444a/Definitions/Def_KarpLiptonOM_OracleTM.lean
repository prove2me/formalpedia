-- Prove2me | Definitions.Def_KarpLiptonOM_OracleTM
-- name    : KarpLiptonOM_OracleTM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:28.576799+00:00
-- url     : https://prove2.me/theorems/9bea48ee-b0f2-4094-bf44-a5b62cfdc7eb
-- title:
--   Deterministic oracle Turing machine (work tape and query tape)
-- statement:
--   A deterministic **oracle Turing machine** has a work tape (holding the input at the start) and a query tape, a finite tape alphabet containing $0$, $1$ and a separator $\#$, finitely many states with an initial state, distinct accepting and rejecting states, a query state $q_?$ and two answer states $q_{\mathrm{yes}}, q_{\mathrm{no}}$, and a transition function that, from the state and the two scanned symbols, determines the next state, the symbols written and the head moves on both tapes.
--
--   When the machine enters $q_?$, the next step consults the oracle: the machine moves to $q_{\mathrm{yes}}$ if the string on the query tape belongs to the oracle language and to $q_{\mathrm{no}}$ otherwise. Every oracle question costs one step.
--
--   The same machine is used as a decider (it accepts or rejects), as a transducer (its output is the string on the work tape when it halts), and as a randomized machine (it receives its random string as a second argument).
--
--   **Formalization Note** The model extends the published one-tape machine of `CookPvsNP` by a second tape and the query mechanism. The oracle answer leaves both tapes unchanged; erasing the query tape is the machine's business. This is a standard variant of the oracle machine model, polynomially equivalent to the others.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 and §A.2.2, p.21 (oracle machines; Definition A.2.1)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_Tape

namespace KarpLiptonOM

/-- A deterministic **oracle Turing machine** (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20 and §A.2.2, p.21; Definition
A.2.1): a two-tape machine (work tape, query tape) in the style of the published Cook model
`CookPvsNP.TM`, with tape symbols `Γ ⊇ {0, 1, #}` (via `ι`), finite states with the halting states
`qaccept ≠ qreject`, a query state `qquery` and answer states `qyes`, `qno`.

**Formalization Note** In state `qquery` the machine makes one step: it enters `qyes` if the string
on its query tape (`Tape.bits`) is in the oracle language and `qno` otherwise, leaving both tapes
unchanged (`OracleTM.step`). In any other non-halting state, `δ q a b = (q', (a', d₁), (b', d₂))`
writes `a'` on the work tape and `b'` on the query tape, moves the heads in directions `d₁`, `d₂`,
and enters `q'`. The same machine serves as a decider (accept/reject), as a transducer (output =
string on the work tape) and as a randomized machine (random string as a second input). -/
structure OracleTM where
  /-- the non-blank tape symbols -/
  Γ : Type
  [finΓ : Fintype Γ]
  [decΓ : DecidableEq Γ]
  /-- the input symbols `0, 1, #` (`some false`, `some true`, `none`) inside `Γ` -/
  ι : Option Bool ↪ Γ
  /-- the states -/
  Q : Type
  [finQ : Fintype Q]
  [decQ : DecidableEq Q]
  /-- the initial state -/
  q₀ : Q
  /-- the accepting state -/
  qaccept : Q
  /-- the rejecting state -/
  qreject : Q
  /-- the query state -/
  qquery : Q
  /-- the state entered after a positive answer -/
  qyes : Q
  /-- the state entered after a negative answer -/
  qno : Q
  accept_ne_reject : qaccept ≠ qreject
  /-- the transition function on (state, scanned work symbol, scanned query symbol) -/
  δ : Q → Option Γ → Option Γ → Q × (Option Γ × CookPvsNP.Move) × (Option Γ × CookPvsNP.Move)

attribute [instance] OracleTM.finΓ OracleTM.decΓ OracleTM.finQ OracleTM.decQ

end KarpLiptonOM


