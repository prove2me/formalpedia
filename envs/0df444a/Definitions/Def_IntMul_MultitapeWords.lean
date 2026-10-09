-- Prove2me | Definitions.Def_IntMul_MultitapeWords
-- name    : IntMul_MultitapeWords
-- status  : Definition
-- author  : @avi
-- created : 2026-10-09T02:06:02.667331+00:00
-- url     : https://prove2.me/theorems/a56a9e12-1f3b-46c4-b234-cf14bcb66bb8
-- title:
--   Multitape Turing machines on arbitrary inputs over $\{0,1,\#\}$
-- statement:
--   This file extends the shared machine model `IntMul_MultitapeModel` from inputs of the form $x\#y$ to arbitrary words over the input alphabet $\{0,1,\#\}$, so that subroutines such as sorting and matrix transposition can be stated.
--
--   A letter is `some b` (the bit $b$) or `none` (the separator $\#$), written on the tape as the machine's symbols $0$, $1$ or $\#$.
--
--   - **Initial configuration on $w$:** state $\mathrm{START}$; the input tape holds $\triangleright\,w\,\square\square\cdots$; every other tape holds $\triangleright\,\square\square\cdots$; all heads are on cell $0$.
--   - **$M$ halts with output $v$ at step $t$:** after exactly $t$ steps from that configuration the state is $\mathrm{HALT}$ and the whole output tape is $\triangleright\,v\,\square\square\cdots$.
--   - **Encodings:** $\mathrm{bits}(x)$ is a bit string viewed as a word, and $\mathrm{joinSep}(u_1,\dots,u_m)=u_1\#u_2\#\cdots\#u_m$ (empty for $m=0$).
-- source:
--   A. Montanaro, Computational Complexity, lecture notes (Cambridge Part III, 2012), §3, §3.4, §4; extends the published definition IntMul_MultitapeModel to inputs other than x#y.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

/-!
# Multitape machines on general inputs over `{0, 1, #}`

Extends the shared model `IntMul_MultitapeModel` (Montanaro, *Computational Complexity*, §3,
§3.4) from inputs `x#y` to arbitrary words over the input alphabet `{0, 1, #}`, so that
subroutines such as sorting and matrix transposition can be stated. A letter is an
`Option Bool`: `some b` is the bit `b` and `none` is the separator `#`.
-/

namespace IntMul

namespace MultitapeTM

variable (M : MultitapeTM)

/-- The tape symbol of a letter of `{0, 1, #}`. -/
def letterSym : Option Bool → M.Sym
  | none => M.sep
  | some b => M.bitSym b

/-- The initial configuration on input `w`: state `START`; the input tape holds `▷ w □ □ …`;
every other tape holds `▷ □ □ …`; every head is on cell `0`. -/
def initCfgW (w : List (Option Bool)) : M.Cfg where
  state := M.qStart
  cells := fun i => if i = M.inTape then M.tapeOf (w.map M.letterSym) else M.tapeOf []
  head := fun _ => 0

/-- On input `w`, after `t` steps the machine is in state `HALT` and the output tape holds
exactly `▷ v □ □ …`. -/
def HaltsWithOutputW (w : List (Option Bool)) (t : ℕ) (v : List (Option Bool)) : Prop :=
  (M.step^[t] (M.initCfgW w)).state = M.qHalt ∧
    (M.step^[t] (M.initCfgW w)).cells M.outTape = M.tapeOf (v.map M.letterSym)

end MultitapeTM

/-- A bit string as a word over `{0, 1, #}`. -/
def bits (x : List Bool) : List (Option Bool) := x.map some

/-- The words `u₁ # u₂ # ⋯ # u_m` (the empty list gives the empty word). -/
def joinSep (us : List (List (Option Bool))) : List (Option Bool) :=
  List.intercalate [none] us

end IntMul


