-- Prove2me | Definitions.Def_SubsetConvFPRAS_Supplement_CommonBasesInput
-- name    : SubsetConvFPRAS_Supplement_CommonBasesInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:47:34.097094+00:00
-- url     : https://prove2.me/theorems/45066330-a2c7-4cd6-9568-f315e4030e74
-- title:
--   Input and resource bound of Theorem 1.2 on the common-bases bit machine
-- statement:
--   This file fixes the input of Theorem 1.2 on the published bit machine of `OAI.CommonBasesFPRAS` (registers of bits, fair coins, two independence oracles, counters for bit operations and oracle calls).
--
--   The instance of Theorem 1.2 consists of two matroids on a common ground set $U$ with $|U|=n$, accessed only through their independence oracles, and an accuracy parameter $0<\varepsilon\le1$. The machine therefore starts with $n$ in binary in register $0$ and the numerator and denominator of the rational $\varepsilon$ in registers $2$ and $3$; all other registers are empty and the control state is $0$. No rank is written: register $1$, which holds the common rank in the published layout, stays empty.
--
--   The input length is
--   $$L(n,\varepsilon)=4+\operatorname{bits}(n)+\operatorname{bits}(\mathrm{num}\,\varepsilon)+\operatorname{bits}(\mathrm{den}\,\varepsilon),$$
--   and the resource bound is $B=C\,(1+n+L+\lceil\varepsilon^{-1}\rceil)^d$, polynomial in the size of the instance and $1/\varepsilon$ as Definition 1.1 requires.
--
--   **Formalization Note** Binary representations are Lean's `Nat.bits`, least significant bit first, as in the published machine.
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Definition 1.1 and Theorem 1.2, p.3

import Mathlib
import Definitions.Def_CommonBasesFPRAS

open scoped Classical

namespace SubsetConvFPRAS.Supplement

/-!
# Input and resource bound of Theorem 1.2 on the published common-bases bit machine

X. Chen, K. Liu, *An FPRAS for Counting Common Bases of Two Matroids*, arXiv:2610.06724 (version held,
sha256 6c1d68c2…), Definition 1.1 and Theorem 1.2, p.3.

The machine is the published `OAI.CommonBasesFPRAS` bit machine (registers of bits, fair coins, two
independence oracles, bit-operation and oracle-call counters), used unchanged. Its own initial
configuration also carries a common rank `r` and a failure parameter `δ`, which Theorem 1.2's input does
not have, so this file gives the input of Theorem 1.2: the ground-set size `n` and the accuracy `ε`.

**Formalization Note.**
* Register `0` holds `n` in binary (`Nat.bits`, least significant bit first); registers `2, 3` hold the
  numerator and denominator of `ε`; every other register is empty (register `1`, which holds the rank in
  the published layout, stays empty). The control state is `0`.
* The input length counts the four input registers' bits plus `4`.
* The resource bound is `C · (1 + n + L + ⌈ε⁻¹⌉)^d`: polynomial in the size of the instance and `1/ε`
  (Definition 1.1).
-/

open OAI.CommonBasesFPRAS

/-- The bit length of Theorem 1.2's input `(n, ε)`. -/
def inputLength12 (n : ℕ) (ε : ℚ) : ℕ :=
  4 + n.bits.length + ε.num.natAbs.bits.length + ε.den.bits.length

/-- The initial configuration of Theorem 1.2: register `0` is `n`, registers `2, 3` are the numerator and
denominator of `ε`, all other registers are empty, control state `0`, no output, both counters `0`. -/
def initialConfig12 (k s n : ℕ) (ε : ℚ) : MachineConfig k s where
  registers := fun i => match i.val with
    | 0 => n.bits
    | 2 => ε.num.natAbs.bits
    | 3 => ε.den.bits
    | _ => []
  control := 0

/-- The resource bound `C · (1 + n + L + ⌈ε⁻¹⌉)^d` of Theorem 1.2, with `L = inputLength12 n ε`. -/
def resourceBound12 (C d n : ℕ) (ε : ℚ) : ℕ :=
  C * (1 + n + inputLength12 n ε + ⌈ε⁻¹⌉₊) ^ d

end SubsetConvFPRAS.Supplement


