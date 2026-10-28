-- Prove2me | Definitions.Def_BIP68_Core
-- name    : BIP68_Core
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T01:35:09.657713+00:00
-- url     : https://prove2.me/theorems/45d4f637-6ec0-43fb-96d4-5503b4cb02da
-- title:
--   Lean transcription of the pinned Core sequence-lock helpers
-- statement:
--   The implementation reads unsigned 32-bit words using the masks $2^{31}$, $2^{22}$, and $65535$, and converts the masked delay to seconds with a nine-bit left shift. Enforcement checks unsigned version at least two and flags bit zero.
--
--   An accumulator consists of integer thresholds $a,b$ and a reversed height list. It starts at $(-1,-1,[])$. Processing a disabled input prepends zero and leaves both thresholds unchanged. For an enabled time input it updates $b$ to $\max(b,M(\max(c-1,0))+512d-1)$; for an enabled height input it updates $a$ to $\max(a,c+d-1)$. Both enabled branches prepend the original coin height. The masked delay and seconds are computed with bit-vector operations. The final subtraction takes place in the integers, preserving the $-1$ sentinel.
--
--   If transaction-level enforcement is off, calculation preserves all original heights and returns thresholds $(-1,-1)$. The output height list is obtained by reversing the accumulator's list. Evaluation accepts precisely when
--
--   $$a<H\quad\land\quad b<M(\max(H-1,0)).$$
--
--   The sequence-lock function composes calculation with evaluation. These are total functions over the model's records; their definitions do not assume valid histories or bounded arithmetic. The main theorem states the domain appropriate for comparison with Core. This is a manual transcription of the named routines, not a formal C++ semantics or a proof about compiled machine code.
-- source:
--   BIP68, Specification and Implementation sections: https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0068.mediawiki; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, CalculateSequenceLocks/EvaluateSequenceLocks/SequenceLocks, lines 45–116: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L45-L116; constants: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/primitives/transaction.h#L86-L115.

import Definitions.Def_BIP68_Model

namespace BitcoinBIP68

def coreEnabled (version flags : BitVec 32) : Bool :=
  decide (2 ≤ version.toNat) && ((flags &&& 1) != 0)

def coreDisabled (sequence : BitVec 32) : Bool :=
  (sequence &&& 0x80000000) != 0

def coreTimeBased (sequence : BitVec 32) : Bool :=
  (sequence &&& 0x00400000) != 0

def coreDelay (sequence : BitVec 32) : Nat :=
  (sequence &&& 0x0000ffff).toNat

def coreSeconds (sequence : BitVec 32) : Nat :=
  ((sequence &&& 0x0000ffff) <<< 9).toNat

structure Accumulator where
  minHeight : Int
  minTime : Int
  heightsRev : List Nat
  deriving Repr, DecidableEq

def initial : Accumulator := ⟨-1, -1, []⟩

def coreStep (ctx : Context) (acc : Accumulator) (input : Input) : Accumulator :=
  if coreDisabled input.sequence then
    { acc with heightsRev := 0 :: acc.heightsRev }
  else if coreTimeBased input.sequence then
    { acc with
      minTime := max acc.minTime
        ((ctx.mtp (input.coinHeight - 1) : Int) + (coreSeconds input.sequence : Int) - 1)
      heightsRev := input.coinHeight :: acc.heightsRev }
  else
    { acc with
      minHeight := max acc.minHeight
        ((input.coinHeight : Int) + (coreDelay input.sequence : Int) - 1)
      heightsRev := input.coinHeight :: acc.heightsRev }

def calculate (version flags : BitVec 32) (ctx : Context)
    (inputs : List Input) : Accumulator :=
  if coreEnabled version flags then inputs.foldl (coreStep ctx) initial
  else { initial with heightsRev := (inputs.map Input.coinHeight).reverse }

def returnedHeights (acc : Accumulator) : List Nat := acc.heightsRev.reverse

def evaluate (ctx : Context) (acc : Accumulator) : Bool :=
  decide (acc.minHeight < (ctx.height : Int) ∧
    acc.minTime < (ctx.mtp (ctx.height - 1) : Int))

def sequenceLocks (version flags : BitVec 32) (ctx : Context)
    (inputs : List Input) : Bool :=
  evaluate ctx (calculate version flags ctx inputs)

end BitcoinBIP68


