-- Prove2me | Definitions.Def_BIP68_Model
-- name    : BIP68_Model
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T01:34:59.674036+00:00
-- url     : https://prove2.me/theorems/db64902c-d929-480d-b490-26081bcd8181
-- title:
--   BIP68 input data, declarative eligibility, and arithmetic domain
-- statement:
--   An input consists of an unsigned 32-bit sequence word $s$ and a natural-number coin height $c$. A context consists of a natural-number candidate height $H$ and a total function $M:\mathbb N\to\mathbb N$ supplying median times. Put $h^-=\max(h-1,0)$, $d=s\bmod 65536$, and let $D$ and $T$ be the tests for bits 31 and 22, expressed by quotient and remainder. Enforcement $E$ means that the unsigned version is at least two and the flags value is odd. A single input satisfies its delay when
--
--   $$D\ \lor\ \begin{cases}M(c^-)+512d\le M(H^-),&T,\\ c+d\le H,&\neg T.\end{cases}$$
--
--   The transaction-level predicate holds when $E$ is false or every input satisfies that condition. The expected output height list replaces an input height by zero exactly when $E$ and $D$ both hold, preserving order and repetitions.
--
--   The admissible-context predicate requires $0<H\le2^{31}-1$, every input height at most $H$, and $M(h)\le2^{63}-1$ for all $h\le H$. A separate no-overflow predicate requires the selected pre-subtraction sum to be at most $2^{31}-1$ for an enforced height input, or $2^{63}-1$ for an enforced time input. It imposes no sum condition on disabled inputs or when enforcement is off. Heights and clocks are nonnegative by type; no clock monotonicity is assumed. Empty input lists are included. The records alone impose no validity conditions: the predicates supply them when a theorem needs them.
--
--   These definitions separate per-input eligibility from the implementation's threshold-accumulation algorithm. Decidable instances are supplied for the three flag predicates.
-- source:
--   BIP68, Specification and Implementation sections: https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0068.mediawiki; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, CalculateSequenceLocks/EvaluateSequenceLocks/SequenceLocks, lines 45–116: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L45-L116; constants: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/primitives/transaction.h#L86-L115.

import Std

namespace BitcoinBIP68

structure Input where
  sequence : BitVec 32
  coinHeight : Nat
  deriving Repr, DecidableEq

structure Context where
  height : Nat
  mtp : Nat → Nat

def int32Max : Nat := 2147483647
def int64Max : Nat := 9223372036854775807

def specEnabled (version flags : BitVec 32) : Prop :=
  2 ≤ version.toNat ∧ flags.toNat % 2 = 1

def specDisabled (sequence : BitVec 32) : Prop :=
  sequence.toNat / 2147483648 = 1

def specTimeBased (sequence : BitVec 32) : Prop :=
  (sequence.toNat / 4194304) % 2 = 1

def specDelay (sequence : BitVec 32) : Nat :=
  sequence.toNat % 65536

instance (version flags : BitVec 32) : Decidable (specEnabled version flags) :=
  inferInstanceAs (Decidable (2 ≤ version.toNat ∧ flags.toNat % 2 = 1))

instance (sequence : BitVec 32) : Decidable (specDisabled sequence) :=
  inferInstanceAs (Decidable (sequence.toNat / 2147483648 = 1))

instance (sequence : BitVec 32) : Decidable (specTimeBased sequence) :=
  inferInstanceAs (Decidable ((sequence.toNat / 4194304) % 2 = 1))

def inputSatisfied (ctx : Context) (input : Input) : Prop :=
  specDisabled input.sequence ∨
    if specTimeBased input.sequence then
      ctx.mtp (input.coinHeight - 1) + 512 * specDelay input.sequence ≤
        ctx.mtp (ctx.height - 1)
    else
      input.coinHeight + specDelay input.sequence ≤ ctx.height

def satisfiesBIP68 (version flags : BitVec 32) (ctx : Context)
    (inputs : List Input) : Prop :=
  ¬ specEnabled version flags ∨ ∀ input ∈ inputs, inputSatisfied ctx input

def expectedHeights (version flags : BitVec 32) (inputs : List Input) : List Nat :=
  inputs.map fun input =>
    if specEnabled version flags ∧ specDisabled input.sequence then 0
    else input.coinHeight

def admissible (ctx : Context) (inputs : List Input) : Prop :=
  0 < ctx.height ∧ ctx.height ≤ int32Max ∧
  (∀ h, h ≤ ctx.height → ctx.mtp h ≤ int64Max) ∧
  ∀ input ∈ inputs, input.coinHeight ≤ ctx.height

def noOverflow (version flags : BitVec 32) (ctx : Context)
    (inputs : List Input) : Prop :=
  ∀ input ∈ inputs, specEnabled version flags → ¬ specDisabled input.sequence →
    if specTimeBased input.sequence then
      ctx.mtp (input.coinHeight - 1) + 512 * specDelay input.sequence ≤ int64Max
    else
      input.coinHeight + specDelay input.sequence ≤ int32Max

end BitcoinBIP68


