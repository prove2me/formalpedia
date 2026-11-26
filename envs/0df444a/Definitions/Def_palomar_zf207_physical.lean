-- Prove2me | Definitions.Def_palomar_zf207_physical
-- name    : palomar_zf207_physical
-- status  : Definition
-- author  : @fl-39
-- created : 2026-11-26T18:33:19.004265+00:00
-- url     : https://prove2.me/theorems/c10c0c38-95a8-53d6-821f-8bbf538d5a0f
-- title:
--   Physical halting predicate for the literal 207-state Turing machine
-- statement:
--   Defines the standard external (meta-level) single-step transition function, $n$-step execution, and halting predicate for the literal 207-state binary Turing machine whose transition table is given by `PalomarZF207History.literalRows`.
--
--   A machine configuration is encoded as a triple $(q, L, R) \in \mathbb{N}^3$, where $q$ is the control state, $L$ encodes the tape bits strictly to the left of the head in binary (least-significant bit nearest the head), and $R$ encodes the tape bits at and to the right of the head in binary (least-significant bit under the head). Reading the bit $R \bmod 2$ and looking up the transition entry in row $q$ of `literalRows` yields the written bit $w \in \{0, 1\}$, head direction (right or left), and next state $q'$; shifting the head updates $(L, R)$ via binary cons/uncons matching `PalomarZF207History.Move`. Starting from the all-blank configuration $(0, 0, 0)$, the machine halts physically if it reaches a state $q \ge 207$ after finitely many steps:
--
--   $$\mathrm{PhysicalHalts207} \;:\!\iff\; \exists n \in \mathbb{N},\; \pi_1\bigl(\mathrm{iterPhysical}(n, (0, 0, 0))\bigr) \ge 207.$$
--
--   This definition makes explicit the external halting predicate `physicalHalts` referenced in the challenge specification for bridging `ArithmeticSigma1Sound` and `InternalLinkedHalts` to standard halting in $\mathbb{N}$.
-- source:
--   James Chang, 'Nonhalting and ZF-independence for a 207-state Turing machine' (2026), Theorem 1.2(2) and Challenge specification (`Def_palomar_zf207_history.lean`, `InternalLinkedHalts` docstring referencing `physicalHalts`); https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Literal207SigmaSoundness.lean

import Definitions.Def_palomar_zf207_history

namespace PalomarZF207

/-- Single deterministic step of the literal 207-state Turing machine on natural-number tape codes. -/
def stepPhysical (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (q, left, right) := c
  let read := right % 2 == 1
  let r := right / 2
  match (if read then (PalomarZF207History.literalRows.getD q (none, none)).2
         else (PalomarZF207History.literalRows.getD q (none, none)).1) with
  | none => c
  | some (write, direction, next) =>
    let w : Nat := if write then 1 else 0
    if direction then
      (next, w + 2 * left, r)
    else
      let bit : Nat := left % 2
      let l : Nat := left / 2
      let middle : Nat := w + 2 * r
      (next, l, bit + 2 * middle)

/-- Iterated execution of `stepPhysical` for `n` steps. -/
def iterPhysical : Nat → Nat × Nat × Nat → Nat × Nat × Nat
  | 0, c => c
  | n + 1, c => iterPhysical n (stepPhysical c)

/-- Standard external halting of the 207-state Turing machine from the blank tape `(0, 0, 0)`. -/
def PhysicalHalts207 : Prop :=
  ∃ n : Nat, (iterPhysical n (0, 0, 0)).1 ≥ 207

end PalomarZF207


